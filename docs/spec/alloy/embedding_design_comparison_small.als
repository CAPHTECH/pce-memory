module embedding_design_comparison_small

/**
 * Embedding設計比較（縮小版）
 * Alloy検証用の最小モデル
 */

-- ============================================================
-- 共通シグネチャ
-- ============================================================

sig Text {}
sig ModelVersion {}
sig Vector {}

abstract sig Bool {}
one sig True, False extends Bool {}

-- ============================================================
-- 設計軸1: キャッシュキー戦略
-- ============================================================

/**
 * 設計A: バージョン込みキー
 */
sig CacheA_Entry {
  text: one Text,
  version: one ModelVersion,
  vector: one Vector
}

one sig CacheA {
  entries: set CacheA_Entry,
  currentVersion: one ModelVersion
}

pred CacheA_Lookup[cache: CacheA, t: Text, v: ModelVersion, result: CacheA_Entry] {
  result in cache.entries
  result.text = t
  result.version = v
}

-- 設計Aの安全性: 返されるエントリは常に現在のバージョン
assert CacheA_NoStale {
  all cache: CacheA, t: Text, result: CacheA_Entry |
    CacheA_Lookup[cache, t, cache.currentVersion, result] implies
      result.version = cache.currentVersion
}

/**
 * 設計B: テキストのみキー（バージョン無視）
 */
sig CacheB_Entry {
  text: one Text,
  version: one ModelVersion,
  vector: one Vector
}

one sig CacheB {
  entries: set CacheB_Entry,
  currentVersion: one ModelVersion
}

pred CacheB_Lookup[cache: CacheB, t: Text, result: CacheB_Entry] {
  result in cache.entries
  result.text = t
  -- バージョンチェックなし！
}

-- 設計Bの問題: 古いバージョンが返される
assert CacheB_NoStale {
  all cache: CacheB, t: Text, result: CacheB_Entry |
    CacheB_Lookup[cache, t, result] implies
      result.version = cache.currentVersion
}

-- ============================================================
-- 設計軸3: Redact順序
-- ============================================================

abstract sig Sensitivity {}
one sig Public, Confidential extends Sensitivity {}

sig Request {
  text: one Text,
  sensitivity: one Sensitivity,
  redacted: one Bool
}

sig Result {
  hasSensitiveInfo: one Bool
}

/**
 * 設計A: Redact-before-Embed
 */
pred RedactA[req: Request, result: Result] {
  req.sensitivity = Confidential implies req.redacted = True
  req.redacted = True implies result.hasSensitiveInfo = False
  (req.redacted = False and req.sensitivity = Public) implies result.hasSensitiveInfo = False
}

assert RedactA_Safe {
  all req: Request, result: Result |
    RedactA[req, result] and req.sensitivity = Confidential implies
      result.hasSensitiveInfo = False
}

/**
 * 設計B: Embed-then-Redact（危険）
 */
pred RedactB[req: Request, result: Result] {
  req.sensitivity = Confidential implies result.hasSensitiveInfo = True
}

assert RedactB_Safe {
  all req: Request, result: Result |
    RedactB[req, result] and req.sensitivity = Confidential implies
      result.hasSensitiveInfo = False
}

-- ============================================================
-- 検証（スコープ3）
-- ============================================================

check CacheA_NoStale for 3
check CacheB_NoStale for 3
check RedactA_Safe for 3
check RedactB_Safe for 3
