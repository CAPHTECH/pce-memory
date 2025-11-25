/**
 * Alloy Model: Embedding System for PCE Memory
 * ADR-0003: Embedding設計の形式検証
 *
 * 検証対象（構造的不変条件）:
 * - EmbeddingDeterminism: 同一テキスト + 同一モデルバージョン → 同一埋め込み
 * - CacheConsistency: キャッシュはモデルバージョン変更時に無効化
 * - UniqueEmbeddingPerTextVersion: テキスト×バージョンの組に対して埋め込みは一意
 * - RedactBeforeEmbed: 機密データは埋め込み前にredact
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

// ========== キャッシュ ==========

one sig EmbeddingCache {
  entries: set Embedding,
  currentModelVersion: one ModelVersion
}

// ========== Bool型 ==========
abstract sig Bool {}
one sig True, False extends Bool {}

// ========== 不変条件（Facts）==========

/**
 * EmbeddingDeterminism: 同一テキスト + 同一モデルバージョン → 同一ベクトル
 * TLA+ correspondence: 数学的決定性
 */
fact EmbeddingDeterminism {
  all disj e1, e2: Embedding |
    (e1.sourceText = e2.sourceText and e1.modelVersion = e2.modelVersion)
      implies e1.vector = e2.vector
}

/**
 * UniqueEmbeddingPerTextVersion: テキスト×バージョンの組に対してキャッシュエントリは一意
 */
fact UniqueEmbeddingPerTextVersion {
  all disj e1, e2: EmbeddingCache.entries |
    not (e1.sourceText = e2.sourceText and e1.modelVersion = e2.modelVersion)
}

/**
 * CacheConsistency: キャッシュ内のエントリは現在のモデルバージョンのみ
 */
fact CacheConsistency {
  all e: EmbeddingCache.entries |
    e.modelVersion = EmbeddingCache.currentModelVersion
}

/**
 * RedactBeforeEmbed: Confidentialデータは埋め込み前にredact必須
 */
fact RedactBeforeEmbed {
  all req: EmbeddingRequest |
    req.sensitivity = Confidential implies req.redacted = True
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

// ========== Predicates ==========

/**
 * modelVersionUpdate: モデルバージョン変更時のキャッシュ無効化
 */
pred modelVersionUpdate[cache, cache': EmbeddingCache, oldVersion, newVersion: ModelVersion] {
  // 新旧バージョンは異なる
  oldVersion != newVersion

  // 古いバージョンのエントリは新キャッシュに存在しない
  cache'.currentModelVersion = newVersion
  no e: cache'.entries | e.modelVersion = oldVersion
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
pred cacheHit[cache: EmbeddingCache, text: Text, version: ModelVersion] {
  some e: cache.entries |
    e.sourceText = text and e.modelVersion = version
}

/**
 * cacheMiss: キャッシュミス条件
 */
pred cacheMiss[cache: EmbeddingCache, text: Text, version: ModelVersion] {
  no e: cache.entries |
    e.sourceText = text and e.modelVersion = version
}

// ========== アサーション ==========

/**
 * NoStaleEmbeddings: 古いバージョンの埋め込みはキャッシュに残らない
 */
assert NoStaleEmbeddings {
  all cache, cache': EmbeddingCache, v1, v2: ModelVersion |
    modelVersionUpdate[cache, cache', v1, v2] implies
      no e: cache'.entries | e.modelVersion = v1
}

/**
 * DeterministicCacheLookup: キャッシュルックアップは決定的
 */
assert DeterministicCacheLookup {
  all cache: EmbeddingCache, t: Text, v: ModelVersion |
    (cacheHit[cache, t, v] or cacheMiss[cache, t, v]) and
    not (cacheHit[cache, t, v] and cacheMiss[cache, t, v])
}

/**
 * ConfidentialDataProtection: Confidentialデータは必ずredact後に埋め込み
 */
assert ConfidentialDataProtection {
  all req: EmbeddingRequest, provider: EmbeddingProvider, result: Embedding |
    embedRequest[req, provider, result] and req.sensitivity = Confidential
      implies req.redacted = True
}

// ========== チェック ==========

check NoStaleEmbeddings for 5 but 3 Embedding, 3 Text, 2 ModelVersion
check DeterministicCacheLookup for 5 but 3 Embedding, 3 Text, 2 ModelVersion
check ConfidentialDataProtection for 5 but 3 EmbeddingRequest, 2 EmbeddingProvider
run {} for 5 but 4 Embedding, 3 Text, 2 ModelVersion, 2 EmbeddingProvider
