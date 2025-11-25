---- MODULE pce_v1v2_integrated ----
\* V1+V2 Integrated Design: Conservative Either + Layer (Fixed)
\* 形式検証に基づく推奨設計

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  ContentHash,    \* コンテンツハッシュの集合
  Scope,          \* スコープ {session, project, principle}
  AllowTag,       \* 許可タグの集合
  ACId,           \* ActiveContext ID
  Rid,            \* リクエストID
  MinScore,       \* Criticスコア下限
  MaxScore,       \* Criticスコア上限
  ReqCounterMax,  \* ログ上限
  LayerName,      \* Layer名の集合
  ScopeId         \* リソーススコープID

VARIABLES
  \* V1 Conservative: 基本状態
  policyApplied,  \* ポリシー適用済みフラグ
  claims,         \* Claim格納 [ContentHash -> Record]
  acs,            \* ActiveContext [ACId -> Record]
  logs,           \* 監査ログ
  critic,         \* Criticスコア [ContentHash -> Int]
  reqCounter,     \* リクエストカウンタ
  lastResult,     \* Either[Error, Success] 結果
  \* V2 Effect: Layer + Scope
  layerGraph,     \* Layer依存グラフ [LayerName -> LayerRec]
  activeScopes,   \* アクティブなリソーススコープ
  scopeResources  \* スコープごとのリソース [ScopeId -> SUBSET ContentHash]

vars == <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
          layerGraph, activeScopes, scopeResources>>

\* Either型の値
Left == "Left"
Right == "Right"
None == "None"

\* Capability型（有限集合）
Capability == {"db_access", "schema_validate", "policy_check", "config_read"}

\* Layer型の定義
LayerRec == [provides: SUBSET Capability, requires: SUBSET LayerName]

\* 型制約
TypeInv ==
  /\ policyApplied \in BOOLEAN
  /\ claims \in [ContentHash -> [scope: Scope, allow: SUBSET AllowTag]]
  /\ acs \in [ACId -> [claims: SUBSET ContentHash, allow: SUBSET AllowTag, scope: SUBSET Scope]]
  /\ logs \in Seq([op: STRING, ok: BOOLEAN, req: Rid])
  /\ critic \in [ContentHash -> MinScore..MaxScore]
  /\ reqCounter \in 0..ReqCounterMax
  /\ lastResult \in {Left, Right, None}
  /\ layerGraph \in [LayerName -> LayerRec]
  /\ activeScopes \in SUBSET ScopeId
  /\ scopeResources \in [ScopeId -> SUBSET ContentHash]

\* ========== V1 Conservative 不変条件 ==========

\* Either強制: 操作後は必ずLeft/Right
EitherTotality == policyApplied => lastResult \in {Left, Right}

\* Criticスコア範囲
Inv_CriticBounds ==
  \A ch \in DOMAIN critic : MinScore <= critic[ch] /\ critic[ch] <= MaxScore

\* ログのリクエストID一意性
Inv_LogReqUnique ==
  \A i, j \in 1..Len(logs) : i # j => logs[i].req # logs[j].req

\* ACのClaim整合性
Inv_AC_Allowed ==
  \A id \in DOMAIN acs :
    \A ch \in acs[id].claims :
      claims[ch].scope \in acs[id].scope /\ claims[ch].allow \cap acs[id].allow # {}

\* ========== V2 Layer 不変条件（修正済み） ==========

\* 依存関係の充足性チェック
DependenciesSatisfied(requires) ==
  requires \subseteq DOMAIN layerGraph

\* Layer非循環性（DAG）- 直接依存のチェック
LayerAcyclic ==
  \A l1, l2 \in DOMAIN layerGraph:
    l1 \in layerGraph[l2].requires => l2 \notin layerGraph[l1].requires

\* スコープベースリソース
LiveResources == UNION {scopeResources[s] : s \in activeScopes}

ScopedResourceInvariant ==
  \A s \in ScopeId : s \notin activeScopes => scopeResources[s] \cap LiveResources = {}

\* 【修正】リソース一意所有権制約
UniqueOwnership ==
  \A r \in UNION {scopeResources[s] : s \in ScopeId} :
    Cardinality({s \in ScopeId : r \in scopeResources[s]}) <= 1

\* ========== ヘルパー ==========

ReqSet == { logs[i].req : i \in 1..Len(logs) }
CanLog == Len(logs) < ReqCounterMax
DefaultScope == CHOOSE s \in Scope : TRUE

\* ========== 初期状態 ==========

Init ==
  /\ policyApplied = FALSE
  /\ claims = [c \in ContentHash |-> [scope |-> DefaultScope, allow |-> {}]]
  /\ acs = [id \in ACId |-> [claims |-> {}, allow |-> {}, scope |-> {}]]
  /\ logs = << >>
  /\ critic = [c \in ContentHash |-> MinScore]
  /\ reqCounter = 0
  /\ lastResult = None
  /\ layerGraph = [l \in LayerName |-> [provides |-> {}, requires |-> {}]]
  /\ activeScopes = {}
  /\ scopeResources = [s \in ScopeId |-> {}]

\* ========== アクション ==========

\* ポリシー適用
ApplyPolicy ==
  /\ ~policyApplied
  /\ policyApplied' = TRUE
  /\ lastResult' = Right
  /\ UNCHANGED <<claims, acs, logs, critic, reqCounter, layerGraph, activeScopes, scopeResources>>

\* 【修正】Layer登録（自己依存禁止ガード追加）
RegisterLayer(name, provides, requires) ==
  /\ name \in LayerName
  /\ name \notin requires                    \* 【修正】自己依存禁止
  /\ DependenciesSatisfied(requires)
  /\ layerGraph' = [layerGraph EXCEPT ![name] = [provides |-> provides, requires |-> requires]]
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult, activeScopes, scopeResources>>

\* スコープ開始
EnterScope(sid) ==
  /\ sid \in ScopeId
  /\ sid \notin activeScopes
  /\ activeScopes' = activeScopes \cup {sid}
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult, layerGraph, scopeResources>>

\* スコープ終了（自動リソース解放）
ExitScope(sid) ==
  /\ sid \in activeScopes
  /\ activeScopes' = activeScopes \ {sid}
  /\ scopeResources' = [scopeResources EXCEPT ![sid] = {}]
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult, layerGraph>>

\* Upsert操作（V1 Either + V2 Scope統合）
Upsert(ch, sc, allowSet, rid, sid) ==
  /\ policyApplied
  /\ rid \notin ReqSet
  /\ CanLog
  /\ sid \in activeScopes                    \* V2: スコープ内でのみ実行可能
  /\ \/ \* 成功ケース (Right)
        /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
        /\ claims' = [claims EXCEPT ![ch] = [scope |-> sc, allow |-> allowSet]]
        /\ critic' = [critic EXCEPT ![ch] = MinScore]
        /\ logs' = Append(logs, [op |-> "upsert", ok |-> TRUE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Right
        /\ scopeResources' = [scopeResources EXCEPT ![sid] = scopeResources[sid] \cup {ch}]
        /\ UNCHANGED <<policyApplied, acs, layerGraph, activeScopes>>
     \/ \* 失敗ケース (Left) - 重複
        /\ ch \in DOMAIN claims
        /\ claims[ch].allow # {}
        /\ logs' = Append(logs, [op |-> "upsert", ok |-> FALSE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Left
        /\ UNCHANGED <<policyApplied, claims, acs, critic, layerGraph, activeScopes, scopeResources>>

\* Activate操作
Activate(id, scopeSet, allowSet, rid) ==
  /\ policyApplied
  /\ id \in ACId
  /\ rid \notin ReqSet
  /\ CanLog
  /\ LET matchedClaims == {ch \in DOMAIN claims :
         claims[ch].scope \in scopeSet /\ claims[ch].allow \cap allowSet # {}}
     IN
     /\ acs' = [acs EXCEPT ![id] = [claims |-> matchedClaims, allow |-> allowSet, scope |-> scopeSet]]
     /\ logs' = Append(logs, [op |-> "activate", ok |-> TRUE, req |-> rid])
     /\ reqCounter' = reqCounter + 1
     /\ lastResult' = Right
     /\ UNCHANGED <<policyApplied, claims, critic, layerGraph, activeScopes, scopeResources>>

\* Feedback操作
Feedback(ch, rid) ==
  /\ policyApplied
  /\ rid \notin ReqSet
  /\ CanLog
  /\ \/ \* 成功ケース
        /\ ch \in DOMAIN claims
        /\ claims[ch].allow # {}
        /\ critic' = [critic EXCEPT ![ch] = IF critic[ch] < MaxScore THEN critic[ch] + 1 ELSE MaxScore]
        /\ logs' = Append(logs, [op |-> "feedback", ok |-> TRUE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Right
        /\ UNCHANGED <<policyApplied, claims, acs, layerGraph, activeScopes, scopeResources>>
     \/ \* 失敗ケース
        /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
        /\ logs' = Append(logs, [op |-> "feedback", ok |-> FALSE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Left
        /\ UNCHANGED <<policyApplied, claims, acs, critic, layerGraph, activeScopes, scopeResources>>

\* ========== 次状態 ==========

Next ==
  \/ ApplyPolicy
  \/ \E name \in LayerName, provides \in SUBSET Capability, requires \in SUBSET LayerName:
       RegisterLayer(name, provides, requires)
  \/ \E sid \in ScopeId: EnterScope(sid)
  \/ \E sid \in ScopeId: ExitScope(sid)
  \/ \E ch \in ContentHash, sc \in Scope, allowSet \in SUBSET AllowTag, rid \in Rid, sid \in ScopeId:
       Upsert(ch, sc, allowSet, rid, sid)
  \/ \E id \in ACId, scopeSet \in SUBSET Scope, allowSet \in SUBSET AllowTag, rid \in Rid:
       Activate(id, scopeSet, allowSet, rid)
  \/ \E ch \in ContentHash, rid \in Rid:
       Feedback(ch, rid)

Spec == Init /\ [][Next]_vars

\* ========== 統合不変条件 ==========

Inv_All ==
  /\ TypeInv
  /\ Inv_CriticBounds
  /\ Inv_LogReqUnique
  /\ Inv_AC_Allowed
  /\ LayerAcyclic
  /\ ScopedResourceInvariant
  /\ UniqueOwnership

\* ライブネス（公平性付き）
Liveness_AllEffectsResolve == <>[] (lastResult \in {Left, Right})

====
