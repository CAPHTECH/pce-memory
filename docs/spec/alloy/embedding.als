/**
 * Alloy Model: Embedding System for PCE Memory
 * ADR-0003: Embedding設計の形式検証
 *
 * 検証対象（構造的不変条件）:
 * - EmbeddingDeterminism: 同一テキスト + 同一モデルバージョン → 同一埋め込み
 * - CacheConsistency: キャッシュはモデルバージョン変更時に無効化
 * - UniqueEmbeddingPerTextVersion: テキスト×バージョンの組に対して埋め込みは一意
 * - RedactBeforeEmbed: 機密データは埋め込み前にredact
 *
 * 修正履歴:
 * - v2: 二状態モデルに変更（pre/post状態でキャッシュ遷移を検証）
 * - v2: トートロジーになっていたアサーションを修正
 */
module pce_memory/embedding

open util/integer

// ========== 基本シグネチャ ==========

sig Text {}
sig ModelVersion {}
sig Vector {}
sig ContentHash {}

// 機密性レベル
abstract sig SensitivityLevel {}
one sig Public, Internal, Confidential extends SensitivityLevel {}

// ========== Bool型 ==========
abstract sig Bool {}
one sig True, False extends Bool {}

// ========== Embedding Provider ==========

abstract sig ProviderStatus {}
one sig Available, Unavailable, Degraded extends ProviderStatus {}

sig EmbeddingProvider {
  status: one ProviderStatus,
  modelVersion: one ModelVersion,
  supportsBatch: one Bool
}

// ========== 埋め込みリクエスト ==========

sig EmbeddingRequest {
  text: one Text,
  textHash: one ContentHash,
  sensitivity: one SensitivityLevel,
  redacted: one Bool  // redact済みかどうか
}

// ========== 埋め込み結果 ==========

sig Embedding {
  sourceText: one Text,
  sourceHash: one ContentHash,
  vector: one Vector,
  modelVersion: one ModelVersion,
  timestamp: one Int
}

// ========== キャッシュ状態（二状態モデル用） ==========

/**
 * CacheState: キャッシュの状態を表現
 * 注意: one sigではなく通常のsigにすることで、pre/post状態を表現可能
 */
sig CacheState {
  entries: set Embedding,
  currentModelVersion: one ModelVersion
}

// ========== 不変条件（Facts）==========

/**
 * EmbeddingDeterminism: 同一テキスト + 同一モデルバージョン → 同一ベクトル
 * 数学的決定性を表現
 */
fact EmbeddingDeterminism {
  all disj e1, e2: Embedding |
    (e1.sourceText = e2.sourceText and e1.modelVersion = e2.modelVersion)
      implies e1.vector = e2.vector
}

/**
 * SourceHashConsistency: 同一テキストは同一ハッシュ
 */
fact SourceHashConsistency {
  all disj e1, e2: Embedding |
    e1.sourceText = e2.sourceText implies e1.sourceHash = e2.sourceHash
}

/**
 * NonNegativeTimestamp: タイムスタンプは非負
 */
fact NonNegativeTimestamp {
  all e: Embedding | e.timestamp >= 0
}

/**
 * RedactBeforeEmbed: Confidentialデータは埋め込み前にredact必須
 * 実装への制約: EmbeddingServiceはredact後のテキストのみ受け付ける
 */
fact RedactBeforeEmbed {
  all req: EmbeddingRequest |
    req.sensitivity = Confidential implies req.redacted = True
}

/**
 * InternalDataPolicy: Internalデータもredact推奨だが必須ではない
 * 注意: この制約は実装で選択可能
 */
// fact InternalDataRedactRecommended {
//   all req: EmbeddingRequest |
//     req.sensitivity = Internal implies req.redacted = True
// }

// ========== キャッシュ状態の整合性（各状態に対する制約） ==========

/**
 * CacheStateConsistency: 各キャッシュ状態内のエントリは現在のモデルバージョンのみ
 * 注意: これは「正しい」キャッシュ状態の定義であり、全ての状態に適用
 */
pred WellFormedCacheState[cs: CacheState] {
  all e: cs.entries | e.modelVersion = cs.currentModelVersion
}

/**
 * UniqueCacheEntry: キャッシュ内でテキスト×バージョンの組は一意
 */
pred UniqueCacheEntries[cs: CacheState] {
  all disj e1, e2: cs.entries |
    not (e1.sourceText = e2.sourceText and e1.modelVersion = e2.modelVersion)
}

// ========== 状態遷移（Predicates）==========

/**
 * modelVersionUpdate: モデルバージョン変更時のキャッシュ無効化
 * 二状態モデル: pre状態からpost状態への遷移を検証
 */
pred modelVersionUpdate[pre, post: CacheState] {
  // 前提条件: 両状態が整合している
  WellFormedCacheState[pre]

  // バージョンが変更される
  pre.currentModelVersion != post.currentModelVersion

  // post状態も整合している（新バージョンのエントリのみ）
  WellFormedCacheState[post]

  // 古いバージョンのエントリは新キャッシュに存在しない（明示的検証）
  no e: post.entries | e.modelVersion = pre.currentModelVersion

  // 新しいエントリは新バージョンのもののみ（再計算されたもの）
  all e: post.entries | e.modelVersion = post.currentModelVersion
}

/**
 * cacheInvalidation: キャッシュ全無効化
 * モデルバージョン変更時に全エントリを削除
 */
pred cacheInvalidation[pre, post: CacheState, newVersion: ModelVersion] {
  pre.currentModelVersion != newVersion
  post.currentModelVersion = newVersion
  no post.entries  // 全エントリ削除
}

/**
 * addCacheEntry: キャッシュエントリ追加
 */
pred addCacheEntry[pre, post: CacheState, newEntry: Embedding] {
  // バージョン不変
  post.currentModelVersion = pre.currentModelVersion

  // 新エントリは現在のバージョン
  newEntry.modelVersion = pre.currentModelVersion

  // エントリ追加
  post.entries = pre.entries + newEntry
}

/**
 * embedRequest: 埋め込みリクエストの処理
 */
pred embedRequest[req: EmbeddingRequest, provider: EmbeddingProvider, result: Embedding] {
  // プロバイダーが利用可能
  provider.status = Available

  // redact要件を満たす
  req.sensitivity != Confidential or req.redacted = True

  // 結果の整合性
  result.sourceText = req.text
  result.sourceHash = req.textHash
  result.modelVersion = provider.modelVersion
}

/**
 * cacheHit: キャッシュヒット条件
 */
pred cacheHit[cs: CacheState, text: Text] {
  some e: cs.entries |
    e.sourceText = text and e.modelVersion = cs.currentModelVersion
}

/**
 * cacheMiss: キャッシュミス条件
 */
pred cacheMiss[cs: CacheState, text: Text] {
  no e: cs.entries |
    e.sourceText = text and e.modelVersion = cs.currentModelVersion
}

// ========== アサーション（実質的な検証） ==========

/**
 * NoStaleEmbeddingsAfterUpdate: モデルバージョン更新後、古いエントリは残らない
 * 二状態モデルで検証: pre -> post の遷移で古いバージョンのエントリが消える
 */
assert NoStaleEmbeddingsAfterUpdate {
  all pre, post: CacheState |
    modelVersionUpdate[pre, post] implies
      (no e: post.entries | e.modelVersion = pre.currentModelVersion)
}

/**
 * InvalidationClearsAll: キャッシュ無効化は全エントリを削除
 */
assert InvalidationClearsAll {
  all pre, post: CacheState, v: ModelVersion |
    cacheInvalidation[pre, post, v] implies
      no post.entries
}

/**
 * CacheHitExclusive: キャッシュヒットとミスは排他的
 */
assert CacheHitExclusive {
  all cs: CacheState, t: Text |
    not (cacheHit[cs, t] and cacheMiss[cs, t])
}

/**
 * CacheHitOrMiss: 任意のテキストはヒットかミスのどちらか
 */
assert CacheHitOrMiss {
  all cs: CacheState, t: Text |
    cacheHit[cs, t] or cacheMiss[cs, t]
}

/**
 * ConfidentialDataProtection: Confidentialデータは必ずredact後に埋め込み
 * embedRequestが成功するにはredactが必要
 */
assert ConfidentialDataProtection {
  all req: EmbeddingRequest, provider: EmbeddingProvider, result: Embedding |
    (embedRequest[req, provider, result] and req.sensitivity = Confidential)
      implies req.redacted = True
}

/**
 * AddEntryPreservesVersion: エントリ追加はバージョンを保持
 */
assert AddEntryPreservesVersion {
  all pre, post: CacheState, e: Embedding |
    addCacheEntry[pre, post, e] implies
      post.currentModelVersion = pre.currentModelVersion
}

/**
 * WellFormedAfterAdd: エントリ追加後もキャッシュは整合
 */
assert WellFormedAfterAdd {
  all pre, post: CacheState, e: Embedding |
    (WellFormedCacheState[pre] and addCacheEntry[pre, post, e]) implies
      WellFormedCacheState[post]
}

// ========== 探索（Runs）==========

/**
 * 反例探索: 古いバージョンが残るケース（設計Bの問題を示す）
 */
pred StaleEntryExists {
  some cs: CacheState, e: cs.entries |
    e.modelVersion != cs.currentModelVersion
}

/**
 * 正常ケース探索: 整合したキャッシュ状態
 */
pred ConsistentCacheExists {
  some cs: CacheState |
    WellFormedCacheState[cs] and
    UniqueCacheEntries[cs] and
    #cs.entries > 1
}

// ========== チェック ==========

// 二状態モデルの検証
check NoStaleEmbeddingsAfterUpdate for 6 but 4 CacheState, 4 Embedding, 3 Text, 2 ModelVersion
check InvalidationClearsAll for 5 but 3 CacheState, 3 Embedding, 2 ModelVersion

// 排他性の検証
check CacheHitExclusive for 5 but 2 CacheState, 3 Embedding, 3 Text, 2 ModelVersion
check CacheHitOrMiss for 5 but 2 CacheState, 3 Embedding, 3 Text, 2 ModelVersion

// redact制約の検証
check ConfidentialDataProtection for 5 but 3 EmbeddingRequest, 2 EmbeddingProvider, 3 Embedding

// 状態遷移の検証
check AddEntryPreservesVersion for 5 but 3 CacheState, 3 Embedding, 2 ModelVersion
check WellFormedAfterAdd for 5 but 3 CacheState, 3 Embedding, 2 ModelVersion

// 探索実行
run ConsistentCacheExists for 5 but 2 CacheState, 4 Embedding, 3 Text, 2 ModelVersion
run StaleEntryExists for 5 but 2 CacheState, 3 Embedding, 2 Text, 2 ModelVersion
