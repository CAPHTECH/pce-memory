module embedding_design_comparison

/**
 * Embedding System Design Comparison
 * 複数の設計軸について、安全性を形式検証で比較
 *
 * 設計軸:
 * 1. キャッシュキー戦略 (Cache Key Strategy)
 * 2. フェイルオーバー戦略 (Failover Strategy)
 * 3. Redact順序 (Redact Order)
 *
 * 検証する安全性:
 * - NoStaleEmbedding: 古いモデルバージョンの埋め込みが返されない
 * - NoSensitiveDataLeakage: 機密データが埋め込みを通じて漏洩しない
 * - RequestCompletion: リクエストは最終的に完了または失敗する
 */

open util/integer

-- ============================================================
-- 共通シグネチャ
-- ============================================================

sig Text {}
sig ModelVersion {}
sig Vector {}
sig TextHash {}

abstract sig Bool {}
one sig True, False extends Bool {}

abstract sig SensitivityLevel {}
one sig Public, Internal, Confidential extends SensitivityLevel {}

-- ============================================================
-- 設計軸1: キャッシュキー戦略
-- ============================================================

/**
 * 設計A: バージョン込みキー (textHash + modelVersion)
 */
sig CacheA_Entry {
  textHash: one TextHash,
  modelVersion: one ModelVersion,
  vector: one Vector
}

one sig CacheA {
  entries: set CacheA_Entry,
  currentVersion: one ModelVersion
}

-- キャッシュAのルックアップ: textHashとmodelVersionの両方で検索
pred CacheA_Lookup[cache: CacheA, hash: TextHash, version: ModelVersion, result: CacheA_Entry] {
  result in cache.entries
  result.textHash = hash
  result.modelVersion = version
}

-- 設計Aの安全性: 返されるエントリは常に現在のバージョン
assert CacheA_NoStaleEmbedding {
  all cache: CacheA, hash: TextHash, result: CacheA_Entry |
    CacheA_Lookup[cache, hash, cache.currentVersion, result] implies
      result.modelVersion = cache.currentVersion
}

/**
 * 設計B: テキストのみキー (textHash only)
 */
sig CacheB_Entry {
  textHash: one TextHash,
  modelVersion: one ModelVersion,  -- メタデータとして保持
  vector: one Vector
}

one sig CacheB {
  entries: set CacheB_Entry,
  currentVersion: one ModelVersion
}

-- キャッシュBのルックアップ: textHashのみで検索（バージョン無視）
pred CacheB_Lookup[cache: CacheB, hash: TextHash, result: CacheB_Entry] {
  result in cache.entries
  result.textHash = hash
  -- バージョンチェックなし！
}

-- 設計Bの問題: 古いバージョンのエントリが返される可能性
assert CacheB_NoStaleEmbedding {
  all cache: CacheB, hash: TextHash, result: CacheB_Entry |
    CacheB_Lookup[cache, hash, result] implies
      result.modelVersion = cache.currentVersion
}

/**
 * 設計C: キャッシュなし
 */
sig CacheC {
  -- エントリなし
}

-- 設計Cは常に安全（キャッシュがないため）
assert CacheC_NoStaleEmbedding {
  -- 常に成立（キャッシュがないため古いエントリが返されることはない）
  True = True
}

-- ============================================================
-- 設計軸2: フェイルオーバー戦略
-- ============================================================

abstract sig ProviderStatus {}
one sig Available, Unavailable extends ProviderStatus {}

sig Provider {
  status: one ProviderStatus
}

/**
 * 設計A: 即時フェイルオーバー
 */
pred FailoverA_GetResult[primary, fallback: Provider, success: Bool] {
  -- プライマリが利用可能なら成功
  primary.status = Available implies success = True
  -- プライマリが利用不可でフォールバックが利用可能なら成功
  (primary.status = Unavailable and fallback.status = Available) implies success = True
  -- 両方利用不可なら失敗
  (primary.status = Unavailable and fallback.status = Unavailable) implies success = False
}

-- 設計Aの安全性: 少なくとも1つが利用可能なら成功
assert FailoverA_RequestCompletion {
  all primary, fallback: Provider, success: Bool |
    FailoverA_GetResult[primary, fallback, success] implies
      ((primary.status = Available or fallback.status = Available) implies success = True)
}

/**
 * 設計B: リトライ後フェイルオーバー（簡略化）
 */
sig RetryState {
  retryCount: one Int,
  maxRetries: one Int
}

pred FailoverB_GetResult[primary, fallback: Provider, state: RetryState, success: Bool] {
  -- プライマリが利用可能なら成功
  primary.status = Available implies success = True
  -- プライマリ不可でリトライ上限到達でフォールバック利用可能なら成功
  (primary.status = Unavailable and state.retryCount >= state.maxRetries and fallback.status = Available) implies success = True
  -- リトライ中は結果未定（簡略化のため失敗とする）
  (primary.status = Unavailable and state.retryCount < state.maxRetries) implies success = False
}

-- 設計Bの問題: リトライ中は成功が保証されない
assert FailoverB_RequestCompletion {
  all primary, fallback: Provider, state: RetryState, success: Bool |
    FailoverB_GetResult[primary, fallback, state, success] implies
      ((primary.status = Available or fallback.status = Available) implies success = True)
}

/**
 * 設計C: エラーのみ（フォールバックなし）
 */
pred FailoverC_GetResult[primary: Provider, success: Bool] {
  primary.status = Available implies success = True
  primary.status = Unavailable implies success = False
}

-- 設計Cの問題: プライマリ不可で必ず失敗
assert FailoverC_RequestCompletion {
  all primary: Provider, success: Bool |
    FailoverC_GetResult[primary, success] implies
      (primary.status = Available implies success = True)
  -- フォールバックがないため、利用可能でも保証できない
}

-- ============================================================
-- 設計軸3: Redact順序
-- ============================================================

sig EmbeddingRequest {
  text: one Text,
  sensitivity: one SensitivityLevel,
  redacted: one Bool
}

sig EmbeddingResult {
  sourceText: one Text,
  vector: one Vector,
  containsSensitiveInfo: one Bool  -- 機密情報を含むか
}

/**
 * 設計A: Redact-before-Embed（先にredact、後で埋め込み）
 */
pred RedactOrderA_Process[req: EmbeddingRequest, result: EmbeddingResult] {
  -- Confidentialデータはredact後のみ埋め込み
  req.sensitivity = Confidential implies req.redacted = True
  -- redact済みなら結果に機密情報は含まれない
  req.redacted = True implies result.containsSensitiveInfo = False
  -- redact未済でPublicなら機密情報は含まれない
  (req.redacted = False and req.sensitivity = Public) implies result.containsSensitiveInfo = False
}

-- 設計Aの安全性: Confidentialデータは常に保護される
assert RedactOrderA_NoSensitiveDataLeakage {
  all req: EmbeddingRequest, result: EmbeddingResult |
    RedactOrderA_Process[req, result] and req.sensitivity = Confidential implies
      result.containsSensitiveInfo = False
}

/**
 * 設計B: Embed-then-Redact（先に埋め込み、後でredact）
 * 問題: ベクトル空間に機密情報がエンコードされた後では遅い
 */
pred RedactOrderB_Process[req: EmbeddingRequest, result: EmbeddingResult] {
  -- 埋め込みは無条件で実行
  result.sourceText = req.text
  -- 埋め込み後のredactは効果がない（ベクトルには情報が含まれる）
  req.sensitivity = Confidential implies result.containsSensitiveInfo = True
}

-- 設計Bの問題: Confidentialデータが漏洩する
assert RedactOrderB_NoSensitiveDataLeakage {
  all req: EmbeddingRequest, result: EmbeddingResult |
    RedactOrderB_Process[req, result] and req.sensitivity = Confidential implies
      result.containsSensitiveInfo = False
}

/**
 * 設計C: 選択可能（リクエストごとに順序を指定）
 */
abstract sig RedactOrder {}
one sig RedactFirst, EmbedFirst extends RedactOrder {}

sig ConfigurableRequest {
  text: one Text,
  sensitivity: one SensitivityLevel,
  redactOrder: one RedactOrder,
  redacted: one Bool
}

pred RedactOrderC_Process[req: ConfigurableRequest, result: EmbeddingResult] {
  -- RedactFirst選択時: 設計Aと同じ
  (req.redactOrder = RedactFirst and req.sensitivity = Confidential) implies req.redacted = True
  (req.redactOrder = RedactFirst and req.redacted = True) implies result.containsSensitiveInfo = False

  -- EmbedFirst選択時: 設計Bと同じ（危険）
  (req.redactOrder = EmbedFirst and req.sensitivity = Confidential) implies result.containsSensitiveInfo = True
}

-- 設計Cの問題: EmbedFirst選択時に漏洩の可能性
assert RedactOrderC_NoSensitiveDataLeakage {
  all req: ConfigurableRequest, result: EmbeddingResult |
    RedactOrderC_Process[req, result] and req.sensitivity = Confidential implies
      result.containsSensitiveInfo = False
}

-- ============================================================
-- 設計比較サマリ
-- ============================================================

/**
 * 比較1: キャッシュキー戦略
 * - 設計A (バージョン込み): 安全 ✓
 * - 設計B (テキストのみ): 古いバージョンが返される可能性 ✗
 * - 設計C (キャッシュなし): 安全だがパフォーマンス低下 △
 */
pred CompareCacheStrategies {
  -- 設計Bでは古いエントリが返される状況が存在
  some cache: CacheB, hash: TextHash, result: CacheB_Entry |
    CacheB_Lookup[cache, hash, result] and result.modelVersion != cache.currentVersion
}

/**
 * 比較2: フェイルオーバー戦略
 * - 設計A (即時): 最も高い可用性 ✓
 * - 設計B (リトライ後): リトライ中の遅延 △
 * - 設計C (エラーのみ): 単一障害点 ✗
 */
pred CompareFailoverStrategies {
  -- 設計Cではプライマリ障害時に必ず失敗
  some primary: Provider |
    primary.status = Unavailable
}

/**
 * 比較3: Redact順序
 * - 設計A (Redact-first): 安全 ✓
 * - 設計B (Embed-first): 機密情報漏洩 ✗
 * - 設計C (選択可能): 誤選択時に漏洩リスク ✗
 */
pred CompareRedactOrder {
  -- 設計B/Cでは機密情報が漏洩する状況が存在
  some req: EmbeddingRequest, result: EmbeddingResult |
    RedactOrderB_Process[req, result] and
    req.sensitivity = Confidential and
    result.containsSensitiveInfo = True
}

-- ============================================================
-- 検証コマンド
-- ============================================================

-- キャッシュ戦略
check CacheA_NoStaleEmbedding for 5    -- 期待: UNSAT（安全）
check CacheB_NoStaleEmbedding for 5    -- 期待: SAT（反例あり）

-- フェイルオーバー戦略
check FailoverA_RequestCompletion for 4  -- 期待: UNSAT（安全）
check FailoverB_RequestCompletion for 4  -- 期待: SAT（反例あり）
check FailoverC_RequestCompletion for 4  -- 期待: SAT（反例あり）

-- Redact順序
check RedactOrderA_NoSensitiveDataLeakage for 4  -- 期待: UNSAT（安全）
check RedactOrderB_NoSensitiveDataLeakage for 4  -- 期待: SAT（反例あり）
check RedactOrderC_NoSensitiveDataLeakage for 4  -- 期待: SAT（反例あり）

-- 比較実行
run CompareCacheStrategies for 5
run CompareFailoverStrategies for 4
run CompareRedactOrder for 4
