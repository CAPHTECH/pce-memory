# Embedding設計の形式検証結果

## 検証対象

3つの設計軸について複数の選択肢を比較検証:

### 設計軸1: キャッシュキー戦略

| 設計 | 概要 | 特徴 |
|------|------|------|
| A: バージョン込みキー | textHash + modelVersion | 古いバージョンは自動除外 |
| B: テキストのみキー | textHash only | シンプルだが古いエントリ返却リスク |
| C: キャッシュなし | - | 安全だがパフォーマンス低下 |

### 設計軸2: フェイルオーバー戦略

| 設計 | 概要 | 特徴 |
|------|------|------|
| A: 即時フェイルオーバー | primary失敗→即fallback | 高可用性 |
| B: リトライ後フェイルオーバー | N回リトライ→fallback | レイテンシ増加 |
| C: エラーのみ | fallbackなし | 単一障害点 |

### 設計軸3: Redact順序

| 設計 | 概要 | 特徴 |
|------|------|------|
| A: Redact-before-Embed | 先にredact、後でembed | 機密情報漏洩防止 |
| B: Embed-then-Redact | 先にembed、後でredact | ベクトル空間に情報残存 |
| C: 選択可能 | リクエストごとに指定 | 誤選択リスク |

## Alloy検証結果（期待値）

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

### 結果の論理的根拠

#### キャッシュキー戦略

| アサーション | 結果 | 論理的根拠 |
|------------|------|-----------|
| CacheA_NoStale | **UNSAT（成立）** | ルックアップ条件に`result.version = cache.currentVersion`を含むため、古いバージョンは返されない |
| CacheB_NoStale | **SAT（違反）** | ルックアップがtextHashのみで検索するため、キャッシュに古いversionのエントリがあれば返される反例が存在 |

```alloy
-- 設計Bの反例シナリオ:
-- cache.entries に {text=t1, version=v_old, vector=vec1} があり
-- cache.currentVersion = v_new のとき
-- CacheB_Lookup で result.version != cache.currentVersion となる
```

#### フェイルオーバー戦略

| アサーション | 結果 | 論理的根拠 |
|------------|------|-----------|
| FailoverA_RequestCompletion | **UNSAT（成立）** | primary/fallbackのどちらかがavailableなら必ずsuccess=True |
| FailoverB_RequestCompletion | **SAT（違反）** | retryCount < maxRetriesの状態でprimary unavailableだと、fallback availableでもsuccess=False |
| FailoverC_RequestCompletion | **SAT（違反）** | primary unavailableだとfallbackがないためsuccess=False（even if fallback would be available in other designs） |

```alloy
-- 設計Bの反例シナリオ:
-- primary.status = Unavailable
-- fallback.status = Available
-- state.retryCount = 0, state.maxRetries = 3
-- → リトライ中なのでsuccess = False（fallbackに切り替わらない）
```

#### Redact順序

| アサーション | 結果 | 論理的根拠 |
|------------|------|-----------|
| RedactA_Safe | **UNSAT（成立）** | Confidential → redacted=True が強制され、redacted=True → hasSensitiveInfo=False |
| RedactB_Safe | **SAT（違反）** | Confidential → hasSensitiveInfo=True が常に成立（埋め込み時点で情報がエンコードされる） |
| RedactC_Safe | **SAT（違反）** | EmbedFirst選択時はRedactBと同じ動作で漏洩 |

```alloy
-- 設計Bの反例シナリオ:
-- req.sensitivity = Confidential
-- → RedactB_Process により result.hasSensitiveInfo = True
-- → アサーション hasSensitiveInfo = False に違反
```

## 設計比較サマリー

```
┌────────────────────────────────────────────────────────────────────────────┐
│                     キャッシュキー戦略の比較                                │
├──────────────┬──────────────────┬──────────────────┬──────────────────────┤
│   検証項目   │ A(バージョン込み) │ B(テキストのみ)  │ C(キャッシュなし)   │
├──────────────┼──────────────────┼──────────────────┼──────────────────────┤
│ 古いバージョン │ ✅ 返されない    │ ❌ 返される可能性 │ ✅ キャッシュなし   │
│ パフォーマンス │ ✅ 高速         │ ✅ 高速          │ ❌ 毎回計算         │
│ 採用判定     │ ✅ 採用         │ ❌ 不採用        │ △ 条件付き         │
└──────────────┴──────────────────┴──────────────────┴──────────────────────┘

┌────────────────────────────────────────────────────────────────────────────┐
│                     フェイルオーバー戦略の比較                              │
├──────────────┬──────────────────┬──────────────────┬──────────────────────┤
│   検証項目   │ A(即時)          │ B(リトライ後)    │ C(エラーのみ)       │
├──────────────┼──────────────────┼──────────────────┼──────────────────────┤
│ 可用性保証   │ ✅ 高い         │ △ リトライ中遅延 │ ❌ 単一障害点       │
│ レイテンシ   │ ✅ 低い         │ ❌ リトライ分増加 │ ✅ 低い            │
│ 採用判定     │ ✅ 採用         │ △ 条件付き       │ ❌ 不採用          │
└──────────────┴──────────────────┴──────────────────┴──────────────────────┘

┌────────────────────────────────────────────────────────────────────────────┐
│                     Redact順序の比較                                        │
├──────────────┬──────────────────┬──────────────────┬──────────────────────┤
│   検証項目   │ A(Redact-first)  │ B(Embed-first)   │ C(選択可能)         │
├──────────────┼──────────────────┼──────────────────┼──────────────────────┤
│ 機密情報保護 │ ✅ 安全         │ ❌ 漏洩リスク    │ ❌ 誤選択リスク     │
│ 柔軟性       │ △ 固定         │ △ 固定          │ ✅ 柔軟            │
│ 採用判定     │ ✅ 採用         │ ❌ 不採用        │ ❌ 不採用          │
└──────────────┴──────────────────┴──────────────────┴──────────────────────┘
```

## 採用する設計

形式検証の結果に基づき、以下の設計を採用:

| 設計軸 | 採用設計 | 根拠 |
|--------|---------|------|
| キャッシュキー戦略 | **A: バージョン込みキー** | 古いバージョンのエントリが返されないことを形式的に保証 |
| フェイルオーバー戦略 | **A: 即時フェイルオーバー** | 可用性を形式的に保証（どちらかが利用可能なら成功） |
| Redact順序 | **A: Redact-before-Embed** | 機密情報が漏洩しないことを形式的に保証 |

## TLA+検証結果

### pce_embedding.tla（採用設計の検証）

```
TLC2 Version 2.19
Model checking completed. No error has been found.
171641 states generated, 35108 distinct states found, 0 states left on queue.
```

**検証した不変条件**:

| 不変条件 | 結果 | 意味 |
|---------|------|------|
| Inv_CacheVersionConsistency | ✅ 成立 | キャッシュ内エントリは現在のモデルバージョンのみ |
| Inv_UniqueRequestId | ✅ 成立 | リクエストIDは一意 |
| Inv_NoProcessingWithoutProvider | ✅ 成立 | プロバイダーなしで処理開始しない |

**TLA+で発見・修正したバグ**:
- `RequestIdUsed`がバッチキューと処理中バッチをチェックしていなかった
- 修正: `batchQueue`と`currentBatch`のチェックを追加

### embedding_failover_comparison.tla（設計比較）

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

**TLA+設計比較結果**:

| 設計 | Inv_A_CanComplete | Inv_C_CanComplete | 採用 |
|-----|-------------------|-------------------|------|
| A: 即時フェイルオーバー | ✅ 成立 | - | ✅ 採用 |
| C: フェイルオーバーなし | - | ❌ 反例発見 | ❌ 不採用 |

## 参考資料

- [embedding_design_comparison.als](alloy/embedding_design_comparison.als) - Alloy設計比較仕様
- [embedding_design_comparison_small.als](alloy/embedding_design_comparison_small.als) - Alloy縮小版
- [pce_embedding.tla](tlaplus/pce_embedding.tla) - TLA+採用設計仕様
- [embedding_failover_comparison.tla](tlaplus/embedding_failover_comparison.tla) - TLA+設計比較仕様
- [ADR-0003](../adr/0003-embedding-system-design.md) - 設計決定記録
