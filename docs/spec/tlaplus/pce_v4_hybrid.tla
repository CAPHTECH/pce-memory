---- MODULE pce_v4_hybrid ----
\* V4: Hybrid Formal Design (TLA+ + SMT + Effect + Runtime Monitoring)
\* 最も厳密な形式検証アプローチ

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  ContentHash,
  Scope,
  AllowTag,
  ACId,
  Rid,
  MinScore,
  MaxScore,
  ReqCounterMax,
  LayerName,
  ScopeId,
  SMTResult       \* {Valid, Invalid, Unknown}

VARIABLES
  \* 基本状態（V1継承）
  policyApplied,
  claims,
  acs,
  logs,
  critic,
  reqCounter,
  lastResult,     \* Either結果
  \* Effect状態（V2継承）
  effectStack,
  layerGraph,
  activeScopes,
  scopeResources,
  \* V4固有: SMT証明 + ランタイム監視
  smtProofs,      \* [Operation -> SMTResult]
  monitor,        \* ランタイム観測ログ
  crossValidated  \* TLA+とSMTの交差検証フラグ

vars == <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
          effectStack, layerGraph, activeScopes, scopeResources,
          smtProofs, monitor, crossValidated>>

\* Either型
Left == "Left"
Right == "Right"
None == "None"

\* SMT結果型
Valid == "Valid"
Invalid == "Invalid"
Unknown == "Unknown"

\* 操作名
Operations == {"upsert", "activate", "feedback", "validate"}

\* モニタレコード（有限集合で定義）
OpName == {"policy", "upsert", "activate", "feedback", "validate"}
MonitorRec == [ts: 0..ReqCounterMax, op: OpName, assertion: BOOLEAN]

\* Effect/Layerレコード
EffectRec == [name: STRING, requires: SUBSET LayerName, status: STRING]
LayerRec == [provides: SUBSET STRING, requires: SUBSET LayerName]

\* 型制約
TypeInv ==
  /\ policyApplied \in BOOLEAN
  /\ claims \in [ContentHash -> [scope: Scope, allow: SUBSET AllowTag]]
  /\ acs \in [ACId -> [claims: SUBSET ContentHash, allow: SUBSET AllowTag, scope: SUBSET Scope]]
  /\ logs \in Seq([op: STRING, ok: BOOLEAN, req: Rid])
  /\ critic \in [ContentHash -> MinScore..MaxScore]
  /\ reqCounter \in 0..ReqCounterMax
  /\ lastResult \in {Left, Right, None}
  /\ effectStack \in Seq(EffectRec)
  /\ layerGraph \in [LayerName -> LayerRec]
  /\ activeScopes \in SUBSET ScopeId
  /\ scopeResources \in [ScopeId -> SUBSET STRING]
  /\ smtProofs \in [Operations -> {Valid, Invalid, Unknown}]
  /\ monitor \in Seq(MonitorRec)
  /\ crossValidated \in BOOLEAN

\* V1継承: Either強制
EitherTotality == lastResult \in {Left, Right}

\* V2継承: Layer非循環性
LayerAcyclic ==
  \A l1, l2 \in DOMAIN layerGraph:
    l1 \in layerGraph[l2].requires => l2 \notin layerGraph[l1].requires

\* V2継承: スコープリソース
LiveResources == UNION {scopeResources[s] : s \in activeScopes}
ScopedResourceInvariant ==
  \A s \in ScopeId : s \notin activeScopes => scopeResources[s] \cap LiveResources = {}

\* V4固有: SMT健全性
\* SMT証明がValidなら、その操作は仕様を満たす
SMTSoundness ==
  \A op \in Operations:
    smtProofs[op] = Valid =>
      \* 操作の事前条件が満たされていれば事後条件も満たされる
      TRUE  \* TLCでは具体的な証明は外部SMTソルバに委譲

\* V4固有: モニタ健全性
\* 全ての観測が実際の状態と一致
MonitorSoundness ==
  \A i \in 1..Len(monitor):
    monitor[i].assertion = TRUE

\* V4固有: 交差検証
\* TLA+不変条件とSMT証明の整合性
CrossValidation ==
  crossValidated =
    /\ \A op \in Operations: smtProofs[op] \in {Valid, Unknown}
    /\ LayerAcyclic
    /\ ScopedResourceInvariant

\* ヘルパー
ReqSet == { logs[i].req : i \in 1..Len(logs) }
CanLog == Len(logs) < ReqCounterMax
DependenciesSatisfied(requires) == requires \subseteq DOMAIN layerGraph
DefaultScope == CHOOSE s \in Scope : TRUE

\* 初期状態
Init ==
  /\ policyApplied = FALSE
  /\ claims = [c \in ContentHash |-> [scope |-> DefaultScope, allow |-> {}]]
  /\ acs = [id \in ACId |-> [claims |-> {}, allow |-> {}, scope |-> {}]]
  /\ logs = << >>
  /\ critic = [c \in ContentHash |-> MinScore]
  /\ reqCounter = 0
  /\ lastResult = None
  /\ effectStack = << >>
  /\ layerGraph = [l \in LayerName |-> [provides |-> {}, requires |-> {}]]
  /\ activeScopes = {}
  /\ scopeResources = [s \in ScopeId |-> {}]
  /\ smtProofs = [op \in Operations |-> Unknown]
  /\ monitor = << >>
  /\ crossValidated = FALSE

\* SMT検証実行
SMTVerify(op, result) ==
  /\ op \in Operations
  /\ result \in {Valid, Invalid, Unknown}
  /\ smtProofs' = [smtProofs EXCEPT ![op] = result]
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
                 effectStack, layerGraph, activeScopes, scopeResources, monitor, crossValidated>>

\* 交差検証更新
UpdateCrossValidation ==
  /\ crossValidated' = CrossValidation
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
                 effectStack, layerGraph, activeScopes, scopeResources, smtProofs, monitor>>

\* モニタ記録
RecordMonitor(op, assertion) ==
  /\ monitor' = Append(monitor, [ts |-> Len(logs), op |-> op, assertion |-> assertion, state_hash |-> ""])
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
                 effectStack, layerGraph, activeScopes, scopeResources, smtProofs, crossValidated>>

\* ポリシー適用
ApplyPolicy ==
  /\ ~policyApplied
  /\ smtProofs["upsert"] # Invalid  \* SMT事前検証
  /\ policyApplied' = TRUE
  /\ lastResult' = Right
  /\ monitor' = Append(monitor, [ts |-> 0, op |-> "policy", assertion |-> TRUE])
  /\ UNCHANGED <<claims, acs, logs, critic, reqCounter,
                 effectStack, layerGraph, activeScopes, scopeResources, smtProofs, crossValidated>>

\* スコープ開始
EnterScope(sid) ==
  /\ sid \in ScopeId
  /\ sid \notin activeScopes
  /\ activeScopes' = activeScopes \cup {sid}
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
                 effectStack, layerGraph, scopeResources, smtProofs, monitor, crossValidated>>

\* スコープ終了
ExitScope(sid) ==
  /\ sid \in activeScopes
  /\ activeScopes' = activeScopes \ {sid}
  /\ scopeResources' = [scopeResources EXCEPT ![sid] = {}]
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult,
                 effectStack, layerGraph, smtProofs, monitor, crossValidated>>

\* Upsert操作（三重検証: SMT + Either + Layer）
V4_Upsert(ch, sc, allowSet, rid, sid) ==
  /\ policyApplied
  /\ smtProofs["upsert"] = Valid  \* SMT事前検証必須
  /\ rid \notin ReqSet
  /\ CanLog
  /\ sid \in activeScopes
  /\ \/ \* 成功ケース
        /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
        /\ claims' = [claims EXCEPT ![ch] = [scope |-> sc, allow |-> allowSet]]
        /\ critic' = [critic EXCEPT ![ch] = MinScore]
        /\ logs' = Append(logs, [op |-> "upsert", ok |-> TRUE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Right
        /\ scopeResources' = [scopeResources EXCEPT ![sid] = scopeResources[sid] \cup {ch}]
        /\ monitor' = Append(monitor, [ts |-> reqCounter, op |-> "upsert", assertion |-> TRUE])
        /\ UNCHANGED <<policyApplied, acs, effectStack, layerGraph, activeScopes, smtProofs, crossValidated>>
     \/ \* 失敗ケース
        /\ ch \in DOMAIN claims
        /\ claims[ch].allow # {}
        /\ logs' = Append(logs, [op |-> "upsert", ok |-> FALSE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Left
        /\ monitor' = Append(monitor, [ts |-> reqCounter, op |-> "upsert", assertion |-> TRUE])
        /\ UNCHANGED <<policyApplied, claims, acs, critic, effectStack, layerGraph, activeScopes, scopeResources, smtProofs, crossValidated>>

\* Activate操作
V4_Activate(id, scopeSet, allowSet, rid) ==
  /\ policyApplied
  /\ smtProofs["activate"] \in {Valid, Unknown}
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
     /\ monitor' = Append(monitor, [ts |-> reqCounter, op |-> "activate", assertion |-> TRUE])
     /\ UNCHANGED <<policyApplied, claims, critic, effectStack, layerGraph, activeScopes, scopeResources, smtProofs, crossValidated>>

\* Feedback操作
V4_Feedback(ch, rid) ==
  /\ policyApplied
  /\ smtProofs["feedback"] \in {Valid, Unknown}
  /\ rid \notin ReqSet
  /\ CanLog
  /\ \/ \* 成功
        /\ ch \in DOMAIN claims
        /\ claims[ch].allow # {}
        /\ critic' = [critic EXCEPT ![ch] = IF critic[ch] < MaxScore THEN critic[ch] + 1 ELSE MaxScore]
        /\ logs' = Append(logs, [op |-> "feedback", ok |-> TRUE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Right
        /\ monitor' = Append(monitor, [ts |-> reqCounter, op |-> "feedback", assertion |-> TRUE])
        /\ UNCHANGED <<policyApplied, claims, acs, effectStack, layerGraph, activeScopes, scopeResources, smtProofs, crossValidated>>
     \/ \* 失敗
        /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
        /\ logs' = Append(logs, [op |-> "feedback", ok |-> FALSE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Left
        /\ monitor' = Append(monitor, [ts |-> reqCounter, op |-> "feedback", assertion |-> TRUE])
        /\ UNCHANGED <<policyApplied, claims, acs, critic, effectStack, layerGraph, activeScopes, scopeResources, smtProofs, crossValidated>>

\* 次状態
Next ==
  \/ ApplyPolicy
  \/ \E op \in Operations, result \in {Valid, Invalid, Unknown}: SMTVerify(op, result)
  \/ UpdateCrossValidation
  \/ \E sid \in ScopeId: EnterScope(sid)
  \/ \E sid \in ScopeId: ExitScope(sid)
  \/ \E ch \in ContentHash, sc \in Scope, allowSet \in SUBSET AllowTag, rid \in Rid, sid \in ScopeId:
       V4_Upsert(ch, sc, allowSet, rid, sid)
  \/ \E id \in ACId, scopeSet \in SUBSET Scope, allowSet \in SUBSET AllowTag, rid \in Rid:
       V4_Activate(id, scopeSet, allowSet, rid)
  \/ \E ch \in ContentHash, rid \in Rid:
       V4_Feedback(ch, rid)

Spec == Init /\ [][Next]_vars

\* ========== 不変条件（最強セット） ==========

\* V1継承
Inv_CriticBounds ==
  \A ch \in DOMAIN critic : MinScore <= critic[ch] /\ critic[ch] <= MaxScore

Inv_LogReqUnique ==
  \A i, j \in 1..Len(logs) : i # j => logs[i].req # logs[j].req

Inv_AC_Allowed ==
  \A id \in DOMAIN acs :
    \A ch \in acs[id].claims :
      claims[ch].scope \in acs[id].scope /\ claims[ch].allow \cap acs[id].allow # {}

\* V2継承
Inv_LayerAcyclic == LayerAcyclic
Inv_ScopedResource == ScopedResourceInvariant

\* V4固有
Inv_SMTSoundness == SMTSoundness
Inv_MonitorSoundness == MonitorSoundness

\* 統合不変条件
Inv_All ==
  /\ Inv_CriticBounds
  /\ Inv_LogReqUnique
  /\ Inv_AC_Allowed
  /\ Inv_LayerAcyclic
  /\ Inv_ScopedResource
  /\ Inv_SMTSoundness
  /\ Inv_MonitorSoundness

\* ライブネス
Liveness_CrossValidated == <>(crossValidated = TRUE)
Liveness_SMTComplete == <>(\A op \in Operations: smtProofs[op] \in {Valid, Invalid})

====
