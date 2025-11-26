# ADR-0003: Embedding System設計（形式検証 + 実用的決定）

## ステータス

採択済み（2024-11-25）

## コンテキスト

PCE-Memoryにセマンティック検索機能を追加するため、Embedding（埋め込みベクトル）システムの設計が必要。形式手法（Alloy/TLA+）で検証可能な性質と、実用的に決定すべき性質を明確に分離して設計する。

### 設計要件

1. **機能要件**
   - テキストを埋め込みベクトルに変換
   - バッチ処理のサポート
   - キャッシュによるパフォーマンス最適化
   - モデルバージョン管理

2. **非機能要件**
   - プライバシー（機密データの保護）
   - 可用性（プロバイダー障害への耐性）
   - 整合性（キャッシュの一貫性）

### 検証アプローチ

| 性質の種類 | 検証方法 |
|-----------|---------|
| 構造的不変条件 | Alloy（状態空間探索） |
| 時相的性質 | TLA+（モデル検査） |
| 実装依存パラメータ | 実用的決定（ベンチマーク/経験則） |

## 設計比較（形式検証）

ADR-0002と同様に、複数の設計選択肢をAlloyで比較検証した。

### 比較した設計軸

| 設計軸 | 選択肢A | 選択肢B | 選択肢C |
|-------|---------|---------|---------|
| キャッシュキー戦略 | バージョン込み（textHash+version） | テキストのみ（textHash） | キャッシュなし |
| フェイルオーバー戦略 | 即時切替 | リトライ後切替 | エラーのみ（fallbackなし） |
| Redact順序 | Redact→Embed | Embed→Redact | 選択可能 |

### Alloy検証結果（構造的性質）

```
-- キャッシュキー戦略
CacheA_NoStale              UNSAT ← 反例なし（安全）
CacheB_NoStale              SAT   ← 反例発見（安全でない）

-- フェイルオーバー戦略
FailoverA_RequestCompletion UNSAT ← 反例なし（安全）
FailoverB_RequestCompletion SAT   ← 反例発見（リトライ中は保証なし）
FailoverC_RequestCompletion SAT   ← 反例発見（フォールバックなし）

-- Redact順序
RedactA_Safe                UNSAT ← 反例なし（安全）
RedactB_Safe                SAT   ← 反例発見（機密情報漏洩）
RedactC_Safe                SAT   ← 反例発見（EmbedFirst選択時に漏洩）
```

### TLA+検証結果（時相的性質）

#### pce_embedding.tla（採用設計の検証）

```
TLC2 Version 2.19
Model checking completed. No error has been found.
171641 states generated, 35108 distinct states found, 0 states left on queue.
```

| 不変条件 | 結果 | 意味 |
|---------|------|------|
| Inv_CacheVersionConsistency | ✅ 成立 | キャッシュ内エントリは現在のモデルバージョンのみ |
| Inv_UniqueRequestId | ✅ 成立 | リクエストIDは一意 |
| Inv_NoProcessingWithoutProvider | ✅ 成立 | プロバイダーなしで処理開始しない |

#### TLA+で発見されたバグと修正（v2）

**問題1**: `RequestIdUsed`が`batchQueue`と`currentBatch`をチェックしていなかった
**問題2**: `ProcessingRec`にmodelVersionがなく、バージョン更新中の不整合を検出できなかった
**問題3**: `Inv_UniqueRequestId`がコンテナ間の重複をチェックしていなかった

```tla
-- v2修正1: ProcessingRecにmodelVersionを追加
ProcessingRec == [text: Text, requestId: RequestId,
                 provider: {"primary", "fallback"}, modelVersion: ModelVersion]

-- v2修正2: CompleteProcessingでバージョンチェック
CompleteProcessing(proc, vec) ==
  /\ proc \in processingRequests
  /\ proc.modelVersion = currentModelVersion  -- バージョン一致必須
  /\ ...

-- v2修正3: バージョン不一致時の専用アクション
CompleteProcessingStale(proc) ==
  /\ proc.modelVersion # currentModelVersion
  /\ failedRequests' = failedRequests \cup {
       [text |-> proc.text, requestId |-> proc.requestId,
        error |-> "STALE_MODEL_VERSION"]
     }

-- v2修正4: Inv_UniqueRequestIdを全コンテナ間で相互排他
Inv_UniqueRequestId ==
  /\ \A r1, r2 \in pendingRequests: r1 # r2 => r1.requestId # r2.requestId
  /\ \A r1 \in pendingRequests, r2 \in processingRequests: r1.requestId # r2.requestId
  /\ \A r1 \in pendingRequests, r2 \in completedRequests: r1.requestId # r2.requestId
  /\ ... (全コンテナ間の組み合わせ)
```

#### embedding_failover_comparison.tla（設計比較）

```
TLC2 Version 2.19
Error: Invariant Inv_C_CanComplete is violated.
120 states generated, 66 distinct states found
```

**発見された反例（設計C: フェイルオーバーなし）**:

```
State 1: 初期状態（両プロバイダー利用可能）
State 2: リクエストr1を送信
State 3: プライマリで処理開始
State 4: プライマリ障害発生
→ フォールバックは利用可能だが、設計Cでは切り替えできず処理不可
```

| 設計 | Inv_A_CanComplete | Inv_C_CanComplete | 採用 |
|-----|-------------------|-------------------|------|
| A: 即時フェイルオーバー | ✅ 成立 | - | ✅ 採用 |
| C: フェイルオーバーなし | - | ❌ 反例発見 | ❌ 不採用 |

### 発見された問題

**設計B（テキストのみキー）の反例**:
```
cache.entries に {text=t1, version=v_old, vector=vec1} があり
cache.currentVersion = v_new のとき
→ CacheB_Lookup で古いバージョンのエントリが返される
```

**設計B（Embed-then-Redact）の反例**:
```
req.sensitivity = Confidential のとき
→ 埋め込み時点で機密情報がベクトル空間にエンコードされる
→ 後からredactしても情報は漏洩済み
```

### 設計比較サマリー

```
┌────────────────────────────────────────────────────────────────┐
│                     安全性の比較                               │
├──────────────┬──────────────┬──────────────┬──────────────────┤
│   検証項目   │ 設計A        │ 設計B        │ 設計C           │
├──────────────┼──────────────┼──────────────┼──────────────────┤
│ キャッシュ   │ ✅ 安全     │ ❌ 古いver   │ ✅ なし         │
│ フェイルオーバー │ ✅ 保証   │ △ リトライ中 │ ❌ 単一障害点  │
│ Redact順序  │ ✅ 安全     │ ❌ 漏洩      │ ❌ 誤選択リスク │
└──────────────┴──────────────┴──────────────┴──────────────────┘
```

## 決定

形式検証（Alloy + TLA+）の結果に基づき、以下の設計を採用する。

### 採用する設計

| 設計軸 | 採用設計 | 検証方法 | 根拠 |
|--------|---------|---------|------|
| キャッシュキー戦略 | **A: バージョン込みキー** | Alloy | 古いバージョンのエントリが返されないことを形式的に保証 |
| フェイルオーバー戦略 | **A: 即時フェイルオーバー** | Alloy + TLA+ | 可用性を形式的に保証（どちらかが利用可能なら成功） |
| Redact順序 | **A: Redact-before-Embed** | Alloy | 機密情報が漏洩しないことを形式的に保証 |

### 採用しない設計

| 設計 | 不採用理由 | 反例 |
|------|-----------|------|
| キャッシュB（テキストのみ） | 古いバージョンのエントリが返される | Alloy SAT |
| フェイルオーバーB（リトライ後） | リトライ中は可用性保証なし | Alloy SAT |
| フェイルオーバーC（なし） | 単一障害点、処理不可 | Alloy SAT + TLA+反例 |
| RedactB（Embed-first） | 機密情報がベクトル空間に漏洩 | Alloy SAT |
| RedactC（選択可能） | 誤選択時に漏洩 | Alloy SAT |

### 1. 形式検証で保証する性質（Alloy）

以下の構造的不変条件をAlloyで検証済み:

```alloy
-- embedding.als より抜粋

fact EmbeddingDeterminism {
  all disj e1, e2: Embedding |
    (e1.sourceText = e2.sourceText and e1.modelVersion = e2.modelVersion)
      implies e1.vector = e2.vector
}

fact CacheConsistency {
  all e: EmbeddingCache.entries |
    e.modelVersion = EmbeddingCache.currentModelVersion
}

fact RedactBeforeEmbed {
  all req: EmbeddingRequest |
    req.sensitivity = Confidential implies req.redacted = True
}
```

**検証結果**:
```
check NoStaleEmbeddings         UNSAT ← 成立（安全）
check DeterministicCacheLookup  UNSAT ← 成立（安全）
check ConfidentialDataProtection UNSAT ← 成立（安全）
```

### 2. 形式検証で保証する性質（TLA+）

以下の時相的性質をTLA+で検証:

```tla
-- pce_embedding.tla より抜粋

Inv_CacheVersionConsistency ==
  \A t \in Text: cache[t] # <<>> => cache[t].modelVersion = currentModelVersion

Liveness_EventualResponse ==
  \A req \in pendingRequests:
    <>((\E c \in completedRequests: c.requestId = req.requestId) \/
       (\E f \in failedRequests: f.requestId = req.requestId))

Liveness_BatchCompletion ==
  <>[] (currentBatch = {})
```

**検証対象の性質**:

| 不変条件 | 意味 | 種類 |
|---------|------|------|
| Inv_CacheVersionConsistency | キャッシュ内エントリは現在のモデルバージョンのみ | 安全性 |
| Inv_UniqueRequestId | リクエストIDは一意 | 安全性 |
| Liveness_EventualResponse | 全リクエストは最終的に完了/失敗 | 活性 |
| Liveness_BatchCompletion | バッチ処理は最終的に完了 | 活性 |

### 3. 実用的決定（形式検証対象外）

以下の設計決定は形式検証では証明できないが、実用的な観点から決定:

#### 3.1 プロバイダー戦略: ハイブリッド（ローカル優先 + リモートフォールバック）

| 選択肢 | メリット | デメリット |
|-------|---------|-----------|
| **ローカルのみ** | 低レイテンシ、プライバシー保護 | モデル品質が限定的 |
| リモートのみ | 高品質モデル利用可能 | レイテンシ、外部依存 |
| **ハイブリッド（採用）** | バランス、フォールバック | 実装複雑性 |

**決定理由**:
- プライバシー: 機密データはローカルで処理
- 可用性: リモートプロバイダー障害時のフォールバック
- パフォーマンス: 通常はローカルで低レイテンシ

#### 3.2 ローカルモデル選択: all-MiniLM-L6-v2 (ONNX)

| モデル | 次元数 | サイズ | 品質 |
|-------|--------|-------|------|
| **all-MiniLM-L6-v2（採用）** | 384 | 22MB | 良好 |
| all-mpnet-base-v2 | 768 | 438MB | 高品質 |
| e5-small-v2 | 384 | 130MB | 高品質 |

**決定理由**:
- サイズと品質のバランスが最良
- ONNXランタイムで高速推論可能
- 日本語対応（多言語モデル）

#### 3.3 キャッシュTTL: 24時間（設定可能）

**決定理由**:
- 埋め込みは決定的（同一入力→同一出力）
- モデルバージョン変更時は強制無効化（形式検証済み）
- 24時間は freshness とパフォーマンスのバランス

#### 3.4 バッチサイズ上限: 32アイテム

**決定理由**:
- ONNXランタイムのメモリ使用量
- レイテンシとスループットのトレードオフ
- 部分失敗時のリトライコスト

#### 3.5 Redact-before-Embed: BoundaryPolicy準拠

**決定理由**:
- 形式検証（Alloy）で `RedactBeforeEmbed` を証明
- `BoundaryClass.redact` のタグを持つフィールドは埋め込み前に除去
- ベクトル空間への機密情報漏洩を防止

## 仕様 → 実装対応表

### TLA+ 変数/アクション → TypeScript対応

| TLA+ 要素 | 種類 | TypeScript 対応 | ファイル |
|-----------|------|-----------------|----------|
| `primaryProvider` | 変数 | `LocalEmbeddingProvider` インスタンス | `src/embedding/providers/local.ts` |
| `fallbackProvider` | 変数 | `RemoteEmbeddingProvider` インスタンス | `src/embedding/providers/remote.ts` |
| `cache` | 変数 | `EmbeddingCache.entries` | `src/embedding/cache.ts` |
| `currentModelVersion` | 変数 | `EmbeddingCache.currentModelVersion` | `src/embedding/cache.ts` |
| `pendingRequests` | 変数 | 関数呼び出しキュー（暗黙的） | N/A |
| `processingRequests` | 変数 | Promise実行中（暗黙的） | N/A |
| `completedRequests` | 変数 | TaskEither成功結果 | N/A |
| `failedRequests` | 変数 | TaskEither失敗結果 | N/A |
| `SubmitRequest` | アクション | `embeddingService.embed(text)` | `src/embedding/service.ts` |
| `ProcessCacheHit` | アクション | `cache.get(hash)` 成功時 | `src/embedding/service.ts` |
| `StartProcessing` | アクション | `provider.embed(text)` 呼び出し | `src/embedding/service.ts` |
| `CompleteProcessing` | アクション | Promise解決 + `cache.set()` | `src/embedding/service.ts` |
| `CompleteProcessingStale` | アクション | バージョン不一致時のエラー返却 | `src/embedding/service.ts` |
| `FailoverRetry` | アクション | primary失敗時の`fallbackProvider.embed()` | `src/embedding/service.ts` |
| `UpdateModelVersion` | アクション | `cache.invalidateAll()` | `src/embedding/cache.ts` |

### Alloy シグネチャ → TypeScript型対応

| Alloy 要素 | TypeScript 対応 | 備考 |
|-----------|-----------------|------|
| `sig Text` | `string` | 埋め込み対象テキスト |
| `sig ModelVersion` | `string` | セマンティックバージョン |
| `sig Vector` | `number[]` | 埋め込みベクトル（384次元） |
| `sig ContentHash` | `string` | SHA-256ハッシュ |
| `sig SensitivityLevel` | `'public' \| 'internal' \| 'confidential'` | BoundaryPolicy参照 |
| `sig EmbeddingProvider` | `interface EmbeddingProvider` | 下記参照 |
| `sig CacheState` | `interface EmbeddingCache` | 二状態モデル対応 |
| `sig EmbeddingRequest` | `EmbedParams` | 関数パラメータ |
| `sig Embedding` | `CacheEntry` | キャッシュエントリ |

### 不変条件 → 実装での保証方法

| 形式仕様の不変条件 | 実装での保証方法 |
|------------------|-----------------|
| `Inv_CacheVersionConsistency` | `cache.set()`でmodelVersionを必須パラメータ化 |
| `Inv_UniqueRequestId` | UUIDv4生成で衝突回避 |
| `Inv_NoProcessingWithoutProvider` | `AvailableProvider`チェックを先行ガード |
| `WellFormedCacheState` | TypeScript型システムで構造強制 |
| `RedactBeforeEmbed` | `embeddingService.embed()`の前処理で強制redact |

## 設計詳細

### EmbeddingProvider インターフェース

```typescript
interface EmbeddingProvider {
  readonly modelVersion: string;
  readonly status: 'available' | 'unavailable' | 'degraded';

  embed(text: string): TaskEither<EmbeddingError, number[]>;
  embedBatch(texts: string[]): TaskEither<EmbeddingError, number[][]>;
}

interface LocalEmbeddingProvider extends EmbeddingProvider {
  readonly runtimeType: 'onnx';
  readonly modelPath: string;
}

interface RemoteEmbeddingProvider extends EmbeddingProvider {
  readonly endpoint: string;
  readonly apiKey: string;
}
```

### EmbeddingCache インターフェース

```typescript
interface EmbeddingCache {
  readonly currentModelVersion: string;

  get(textHash: string): TaskEither<CacheError, CacheEntry | undefined>;
  set(textHash: string, embedding: number[]): TaskEither<CacheError, void>;
  invalidateAll(): TaskEither<CacheError, void>;
  invalidateByModelVersion(version: string): TaskEither<CacheError, void>;
}

interface CacheEntry {
  readonly embedding: number[];
  readonly modelVersion: string;
  readonly createdAt: number;
}
```

### 処理フロー

```
┌─────────────────────────────────────────────────────────────┐
│                    EmbeddingService                          │
├─────────────────────────────────────────────────────────────┤
│  1. Redact                                                  │
│     └─ BoundaryPolicy.redact タグのフィールドを除去         │
│                                                             │
│  2. Hash                                                    │
│     └─ テキストのSHA-256ハッシュを計算                      │
│                                                             │
│  3. Cache Lookup                                            │
│     ├─ HIT: キャッシュから返却                              │
│     └─ MISS: プロバイダー呼び出しへ                         │
│                                                             │
│  4. Provider Call                                           │
│     ├─ Primary (Local ONNX)                                 │
│     │   └─ 失敗時: Fallback へ                              │
│     └─ Fallback (Remote API)                                │
│         └─ 失敗時: エラー返却                               │
│                                                             │
│  5. Cache Store                                             │
│     └─ 成功時: キャッシュに保存                             │
└─────────────────────────────────────────────────────────────┘
```

### Layer/Scope統合

```typescript
// index.ts での統合
registerSystemLayer("embedding", new Set(["embed_text"] as const), new Set(["db"]));

// handleUpsert でのスコープ管理
async function handleUpsert(params: UpsertParams): Promise<UpsertResult> {
  const scopeResult = enterRequestScope(requestId);
  // ...
  // 埋め込み生成（スコープ内で実行）
  const embedding = await embeddingService.embed(redactedText)();
  // ...
  exitRequestScope(scopeId);
}
```

## 結果

### 保証される性質

| 性質 | 保証方法 | 仕様ファイル |
|------|---------|-------------|
| 埋め込み決定性 | Alloy（形式検証） | embedding.als |
| キャッシュ整合性 | Alloy + TLA+（形式検証） | embedding.als, pce_embedding.tla |
| Redact-before-Embed | Alloy（形式検証） | embedding.als |
| プロバイダーフェイルオーバー | TLA+（形式検証） | pce_embedding.tla |
| バッチ処理完了 | TLA+（形式検証） | pce_embedding.tla |

### トレードオフ

| メリット | デメリット |
|---------|-----------|
| 形式検証による安全性保証 | ONNXランタイム依存 |
| ローカル処理によるプライバシー | モデル更新時の再デプロイ必要 |
| フォールバックによる可用性 | 実装複雑性の増加 |

### 既知の制限事項：並行リクエストとキャッシュ整合性

#### 制限の概要

現在の実装では、**単一プロセス内の並行リクエスト**において、キャッシュ書き込み時の完全なアトミック性は保証されない。これはNode.jsの非同期インターリービングに起因する。

#### 発生条件

```
時刻T1: リクエストA がembedding生成開始（modelVersion = v1）
時刻T2: updateModelVersion(v2) が呼ばれ、キャッシュクリア
時刻T3: リクエストA が完了、キャッシュ書き込み試行
```

この場合、`cacheSetIfVersionMatches`でバージョンチェックを行うが、チェックと書き込みの間に再度バージョン変更が入る可能性がある（極めて稀）。

#### 影響度分析

| 観点 | 評価 | 理由 |
|------|------|------|
| 発生頻度 | 極低 | モデル更新は稀（数ヶ月に1回程度） |
| データ整合性 | 影響なし | 古いバージョンのキャッシュは次回getで無視される |
| パフォーマンス | 軽微 | 余分なキャッシュエントリが一時的に存在するのみ |
| セキュリティ | 影響なし | データ破損やリーク経路なし |

#### 現在の緩和策

1. **バージョン込みキー戦略**: キャッシュキーに`textHash:modelVersion`を使用し、古いエントリは自然にマッチしない
2. **書き込み前バージョンチェック**: `cacheSetIfVersionMatches`で書き込み直前にバージョン確認
3. **バッチ処理の逐次実行**: `A.traverse(TE.ApplicativeSeq)`で単一バッチ内のレース条件を回避

#### 将来の改善オプション（現時点では不要）

本格的な並行性制御が必要になった場合の選択肢:

| 選択肢 | 実装コスト | 効果 |
|--------|----------|------|
| AsyncMutex導入 | 中 | 完全な排他制御 |
| CAS (Compare-And-Set) | 中 | 楽観的ロック |
| シングルリクエスト化 | 低 | 並行実行を禁止 |

現時点では、発生頻度と影響度を考慮し、追加実装は行わない。

### 未検証の性質（将来の検証候補）

| 性質 | 理由 |
|------|------|
| 埋め込み品質（recall/precision） | ベンチマーク依存 |
| レイテンシ保証 | 実行環境依存 |
| 並行処理のアトミック性 | 上記「既知の制限事項」参照 |

## 参考資料

- [embedding.als](../spec/alloy/embedding.als) - Alloy仕様（単一設計）
- [embedding_design_comparison.als](../spec/alloy/embedding_design_comparison.als) - Alloy仕様（設計比較）
- [embedding_design_verification_results.md](../spec/embedding_design_verification_results.md) - 形式検証結果
- [pce_embedding.tla](../spec/tlaplus/pce_embedding.tla) - TLA+仕様
- [search_extensions_duckdb.md](../search_extensions_duckdb.md) - ハイブリッド検索ガイド
- [core-types.md](../core-types.md) - EmbeddingProvider型定義
- [ADR-0001](./0001-formal-design-v1-v2-hybrid.md) - V1/V2 Hybrid設計
- [ADR-0002](./0002-api-interface-statemachine-design.md) - 状態機械API設計
