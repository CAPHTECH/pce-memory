module boundary

open util/seq
open util/integer

-- 基本集合
sig Scope {}
sig AllowTag {}
sig ContentHash {}
sig Field {}

-- 境界クラスとポリシー
sig BoundaryClass {
  allow: set AllowTag,
  redact: set AllowTag,
  escalation: lone Escalation
}
sig Escalation {}

sig PolicyVersion {}

sig Policy {
  scopes: set Scope,
  classes: set BoundaryClass,
  version: one PolicyVersion
}

-- Claim と Active Context
sig GitCommit {}
sig Url {}
sig Signature {}

sig Provenance {
  git: lone GitCommit,
  url: lone Url,
  signed: lone Signature
}

sig Claim {
  scope: one Scope,
  klass: one BoundaryClass,
  hash: one ContentHash,
  version: one PolicyVersion,
  fields: set Field,
  provenance: one Provenance
}

sig ActiveContext {
  claims: some Claim,
  allow: set AllowTag,
  scopeFilter: set Scope,
  policy: one Policy,
  expires: Int
}

abstract sig FeedbackSignal {}
one sig Helpful, Harmful, Outdated extends FeedbackSignal {}

sig Feedback {
  claim: one Claim,
  signal: one FeedbackSignal,
  at: lone seq Int
}

-- 安全性: 重複禁止（content_hash は一意）
fact uniqueHash {
  all disj c1, c2: Claim | c1.hash != c2.hash
}

-- Provenance は最低1種の情報を持つ（git/url/signed のいずれか）
fact provenanceRequired {
  all c: Claim | some (c.provenance.git + c.provenance.url + c.provenance.signed)
}

-- 安全性: AC に含まれる Claim は scope と allow を満たす
fact acAllowed {
  all ac: ActiveContext, c: ac.claims |
    c.scope in ac.scopeFilter and c.klass.allow & ac.allow != none
}

-- AC はポリシーに含まれるクラスのみを採用
fact acPolicyBinding {
  all ac: ActiveContext, c: ac.claims |
    c.klass in ac.policy.classes and c.version = ac.policy.version
}

-- 完全に redaction 対象の Claim は AC に含まれない
fact noFullyRedactedInAC {
  all ac: ActiveContext, c: ac.claims |
    not (c.fields in c.klass.redact)
}

-- 境界クラス定義の整合性: redact ⊆ allow
fact boundaryConsistency {
  all bc: BoundaryClass | bc.redact in bc.allow
}

-- フィードバック対象は既存 Claim のみ
fact feedbackTargetsExistingClaim {
  all f: Feedback | f.claim in Claim
}

-- expires は非負
fact acExpiresPositive {
  all ac: ActiveContext | ac.expires >= 0
}

-- アサーション: deny ケースは存在しない（allow が空なら AC に載らない）
assert noDenyLeak {
  all ac: ActiveContext | all c: Claim |
    c in ac.claims implies some (c.klass.allow & ac.allow)
}

-- アサーション: AC にポリシーバージョン不一致の Claim は入らない
assert noVersionMismatch {
  all ac: ActiveContext, c: Claim |
    c in ac.claims implies c.version = ac.policy.version
}

-- テスト用インスタンス生成
run {} for 6 but 4 Claim, 3 BoundaryClass, 3 Scope, 4 AllowTag, 4 Field
check noDenyLeak for 6 but 4 Claim, 3 BoundaryClass, 3 Scope, 4 AllowTag, 4 Field
check noVersionMismatch for 6 but 4 Claim, 3 BoundaryClass, 3 Scope, 4 AllowTag, 4 Field
