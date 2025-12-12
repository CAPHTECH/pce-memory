module sync_conflict

-- CRDT同期の衝突検出に関する形式検証 (Issue #18 Phase 3)
--
-- 検証対象:
--   1. 境界クラスの格上げ単調性
--   2. Entity/Relationの重複検出
--   3. 参照整合性の検証
--   4. 衝突解決の一貫性

open util/ordering[Time]

-- 時間
sig Time {}

-- 境界クラス（厳格度順）
abstract sig BoundaryClass {}
one sig Public, Internal, Pii, Secret extends BoundaryClass {}

-- 厳格度関数: public=0, internal=1, pii=2, secret=3
fun strictness[bc: BoundaryClass]: Int {
    bc = Public => 0
    else bc = Internal => 1
    else bc = Pii => 2
    else 3  -- Secret
}

-- 境界クラスのマージ: より厳格な方を選択
fun mergeBoundary[a, b: BoundaryClass]: BoundaryClass {
    strictness[a] >= strictness[b] => a else b
}

-- ContentHash（Claimの識別子）
sig ContentHash {}

-- Entity
sig Entity {
    entityId: one ContentHash
}

-- Relation（Entity間の関係）
sig Relation {
    relationId: one ContentHash,
    src: one Entity,
    dst: one Entity
}

-- Claim
sig Claim {
    contentHash: one ContentHash,
    boundary: one BoundaryClass
}

-- 同期ストア（ローカルとリモート）
sig Store {
    claims: set Claim,
    entities: set Entity,
    relations: set Relation
}

-- 衝突種別
abstract sig ConflictType {}
one sig BoundaryUpgrade, EntityDuplicate, RelationDuplicate, MissingReference extends ConflictType {}

-- 衝突
sig Conflict {
    conflictType: one ConflictType,
    targetId: one ContentHash,
    localValue: lone BoundaryClass,
    remoteValue: lone BoundaryClass,
    resolution: one Resolution
}

-- 解決方法
abstract sig Resolution {}
one sig AutoResolved, Skipped extends Resolution {}

-- 同期操作
sig SyncOperation {
    time: one Time,
    localStore: one Store,
    remoteStore: one Store,
    resultStore: one Store,
    detectedConflicts: set Conflict
}

-- ===== 事実（制約） =====

-- 境界クラス格上げの単調性: マージ結果は両方より厳格
fact BoundaryMergeMonotonic {
    all a, b: BoundaryClass |
        let merged = mergeBoundary[a, b] |
            strictness[merged] >= strictness[a] and
            strictness[merged] >= strictness[b]
}

-- 同一ContentHashのClaimは一意
fact UniqueClaimHash {
    all s: Store | all disj c1, c2: s.claims |
        c1.contentHash != c2.contentHash
}

-- 同一IDのEntityは一意
fact UniqueEntityId {
    all s: Store | all disj e1, e2: s.entities |
        e1.entityId != e2.entityId
}

-- Relationの参照整合性: src/dstはストア内のEntityを参照
fact RelationReferenceIntegrity {
    all s: Store, r: s.relations |
        r.src in s.entities and r.dst in s.entities
}

-- ===== 同期操作の制約 =====

-- Claimのマージ: 同一ContentHashで境界格上げのみ許可
fact ClaimMergeRule {
    all op: SyncOperation |
        all c: op.resultStore.claims |
            -- 結果のClaimはローカルまたはリモートに存在
            c.contentHash in (op.localStore.claims.contentHash + op.remoteStore.claims.contentHash)
}

-- 境界格上げ時は衝突として記録
fact BoundaryUpgradeConflictDetection {
    all op: SyncOperation |
        all lc: op.localStore.claims, rc: op.remoteStore.claims |
            (lc.contentHash = rc.contentHash and strictness[rc.boundary] > strictness[lc.boundary]) implies
                some conf: op.detectedConflicts |
                    conf.conflictType = BoundaryUpgrade and
                    conf.targetId = lc.contentHash and
                    conf.localValue = lc.boundary and
                    conf.remoteValue = rc.boundary and
                    conf.resolution = AutoResolved
}

-- Entity重複時は既存優先で衝突記録
fact EntityDuplicateDetection {
    all op: SyncOperation |
        all le: op.localStore.entities, re: op.remoteStore.entities |
            le.entityId = re.entityId implies
                some conf: op.detectedConflicts |
                    conf.conflictType = EntityDuplicate and
                    conf.targetId = le.entityId and
                    conf.resolution = Skipped
}

-- 参照整合性エラーは衝突として記録
fact MissingReferenceDetection {
    all op: SyncOperation |
        all rr: op.remoteStore.relations |
            (rr.src not in op.resultStore.entities or rr.dst not in op.resultStore.entities) implies
                some conf: op.detectedConflicts |
                    conf.conflictType = MissingReference and
                    conf.targetId = rr.relationId and
                    conf.resolution = Skipped
}

-- ===== CRDT特性 =====

-- 冪等性: mergeBoundary(x, x) = x
assert Idempotent {
    all bc: BoundaryClass | mergeBoundary[bc, bc] = bc
}

-- 可換性: mergeBoundary(a, b) = mergeBoundary(b, a)
assert Commutative {
    all a, b: BoundaryClass | mergeBoundary[a, b] = mergeBoundary[b, a]
}

-- 結合律: (a merge b) merge c = a merge (b merge c)
assert Associative {
    all a, b, c: BoundaryClass |
        mergeBoundary[mergeBoundary[a, b], c] = mergeBoundary[a, mergeBoundary[b, c]]
}

-- 境界格下げ禁止: 結果の境界はローカルより厳格
assert NoBoundaryDowngrade {
    all op: SyncOperation |
        all rc: op.resultStore.claims |
            some lc: op.localStore.claims |
                lc.contentHash = rc.contentHash implies
                    strictness[rc.boundary] >= strictness[lc.boundary]
}

-- 衝突検出の完全性: 境界格上げは必ず検出
assert ConflictDetectionComplete {
    all op: SyncOperation |
        all lc: op.localStore.claims, rc: op.remoteStore.claims |
            (lc.contentHash = rc.contentHash and strictness[rc.boundary] > strictness[lc.boundary]) implies
                some conf: op.detectedConflicts |
                    conf.conflictType = BoundaryUpgrade and conf.targetId = lc.contentHash
}

-- 参照整合性の保持: 結果のRelationは有効なEntity参照
assert ResultReferenceIntegrity {
    all op: SyncOperation, r: op.resultStore.relations |
        r.src in op.resultStore.entities and r.dst in op.resultStore.entities
}

-- ===== 検証コマンド =====

-- インスタンス生成
run {} for 5 but 3 Claim, 3 Entity, 2 Relation, 2 Store, 1 SyncOperation, 4 Conflict

-- CRDT特性の検証
check Idempotent for 4
check Commutative for 4
check Associative for 4

-- 安全性の検証
check NoBoundaryDowngrade for 6 but 4 Claim, 3 Entity, 2 Relation, 2 Store, 1 SyncOperation
check ConflictDetectionComplete for 6 but 4 Claim, 3 Entity, 2 Relation, 2 Store, 1 SyncOperation
check ResultReferenceIntegrity for 6 but 4 Claim, 3 Entity, 2 Relation, 2 Store, 1 SyncOperation
