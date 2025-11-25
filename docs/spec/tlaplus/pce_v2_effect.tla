---- MODULE pce_v2_effect ----
\* V2: Effect-TS Design (Effect + Layer + Scope)
\* 依存関係とリソース管理を型レベルで表現

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
  LayerName,      \* Layer名の集合 {DB, Schema, Policy, Config}
  ScopeId         \* リソーススコープID

VARIABLES
  policyApplied,
  claims,
  acs,
  logs,
  critic,
  reqCounter,
  \* V2固有: Effect System状態
  effectStack,    \* Effect実行スタック
  layerGraph,     \* Layer依存グラフ [LayerName -> [provides, requires]]
  activeScopes,   \* アクティブなリソーススコープ
  scopeResources  \* スコープごとのリソース [ScopeId -> SUBSET Resource]

vars == <<policyApplied, claims, acs, logs, critic, reqCounter,
          effectStack, layerGraph, activeScopes, scopeResources>>

\* Effect型の定義
EffectRec == [name: STRING, requires: SUBSET LayerName, status: {"pending", "running", "completed", "failed"}]

\* Layer型の定義（有限集合で定義）
Capability == {"db_access", "schema_validate", "policy_check", "config_read"}
LayerRec == [provides: SUBSET Capability, requires: SUBSET LayerName]

\* 型制約
TypeInv ==
  /\ policyApplied \in BOOLEAN
  /\ claims \in [ContentHash -> [scope: Scope, allow: SUBSET AllowTag]]
  /\ acs \in [ACId -> [claims: SUBSET ContentHash, allow: SUBSET AllowTag, scope: SUBSET Scope]]
  /\ logs \in Seq([op: STRING, ok: BOOLEAN, req: Rid])
  /\ critic \in [ContentHash -> MinScore..MaxScore]
  /\ reqCounter \in 0..ReqCounterMax
  /\ effectStack \in Seq(EffectRec)
  /\ layerGraph \in [LayerName -> LayerRec]
  /\ activeScopes \in SUBSET ScopeId
  /\ scopeResources \in [ScopeId -> SUBSET ContentHash]

\* Layer依存関係の充足性チェック
DependenciesSatisfied(requires) ==
  requires \subseteq DOMAIN layerGraph

\* Layer非循環性（DAG）
\* 簡略化: 直接依存のみチェック
LayerAcyclic ==
  \A l1, l2 \in DOMAIN layerGraph:
    l1 \in layerGraph[l2].requires => l2 \notin layerGraph[l1].requires

\* スコープベースリソース: 非アクティブスコープのリソースはliveでない
LiveResources == UNION {scopeResources[s] : s \in activeScopes}

ScopedResourceInvariant ==
  \A s \in ScopeId : s \notin activeScopes => scopeResources[s] \cap LiveResources = {}

\* ヘルパー
ReqSet == { logs[i].req : i \in 1..Len(logs) }
CanLog == Len(logs) < ReqCounterMax
DefaultScope == CHOOSE s \in Scope : TRUE

\* 初期状態
Init ==
  /\ policyApplied = FALSE
  /\ claims = [c \in ContentHash |-> [scope |-> DefaultScope, allow |-> {}]]
  /\ acs = [id \in ACId |-> [claims |-> {}, allow |-> {}, scope |-> {}]]
  /\ logs = << >>
  /\ critic = [c \in ContentHash |-> MinScore]
  /\ reqCounter = 0
  /\ effectStack = << >>
  /\ layerGraph = [l \in LayerName |-> [provides |-> {}, requires |-> {}]]
  /\ activeScopes = {}
  /\ scopeResources = [s \in ScopeId |-> {}]

\* Layer登録
RegisterLayer(name, provides, requires) ==
  /\ name \in LayerName
  /\ DependenciesSatisfied(requires)
  /\ layerGraph' = [layerGraph EXCEPT ![name] = [provides |-> provides, requires |-> requires]]
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, effectStack, activeScopes, scopeResources>>

\* スコープ開始
EnterScope(sid) ==
  /\ sid \in ScopeId
  /\ sid \notin activeScopes
  /\ activeScopes' = activeScopes \cup {sid}
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, effectStack, layerGraph, scopeResources>>

\* スコープ終了（自動リソース解放）
ExitScope(sid) ==
  /\ sid \in activeScopes
  /\ activeScopes' = activeScopes \ {sid}
  /\ scopeResources' = [scopeResources EXCEPT ![sid] = {}]  \* 自動解放
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, effectStack, layerGraph>>

\* Effect発行
IssueEffect(name, requires) ==
  /\ DependenciesSatisfied(requires)
  /\ effectStack' = Append(effectStack, [name |-> name, requires |-> requires, status |-> "pending"])
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, layerGraph, activeScopes, scopeResources>>

\* Effect実行（依存が満たされている場合のみ）
RunEffect ==
  /\ Len(effectStack) > 0
  /\ LET eff == Head(effectStack) IN
     /\ DependenciesSatisfied(eff.requires)
     /\ effectStack' = Tail(effectStack)
  /\ UNCHANGED <<policyApplied, claims, acs, logs, critic, reqCounter, layerGraph, activeScopes, scopeResources>>

\* ポリシー適用（Effect経由）
ApplyPolicy ==
  /\ ~policyApplied
  /\ DependenciesSatisfied({})  \* Policyは依存なし
  /\ policyApplied' = TRUE
  /\ UNCHANGED <<claims, acs, logs, critic, reqCounter, effectStack, layerGraph, activeScopes, scopeResources>>

\* Upsert操作（Effect + Layer経由）
V2_Upsert(ch, sc, allowSet, rid, sid) ==
  /\ policyApplied
  /\ rid \notin ReqSet
  /\ CanLog
  /\ sid \in activeScopes  \* スコープ内でのみ実行可能
  /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
  /\ claims' = [claims EXCEPT ![ch] = [scope |-> sc, allow |-> allowSet]]
  /\ critic' = [critic EXCEPT ![ch] = MinScore]
  /\ logs' = Append(logs, [op |-> "upsert", ok |-> TRUE, req |-> rid])
  /\ reqCounter' = reqCounter + 1
  /\ scopeResources' = [scopeResources EXCEPT ![sid] = scopeResources[sid] \cup {ch}]
  /\ UNCHANGED <<policyApplied, acs, effectStack, layerGraph, activeScopes>>

\* Activate操作
V2_Activate(id, scopeSet, allowSet, rid) ==
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
     /\ UNCHANGED <<policyApplied, claims, critic, effectStack, layerGraph, activeScopes, scopeResources>>

\* Feedback操作
V2_Feedback(ch, rid) ==
  /\ policyApplied
  /\ ch \in DOMAIN claims
  /\ claims[ch].allow # {}
  /\ rid \notin ReqSet
  /\ CanLog
  /\ critic' = [critic EXCEPT ![ch] = IF critic[ch] < MaxScore THEN critic[ch] + 1 ELSE MaxScore]
  /\ logs' = Append(logs, [op |-> "feedback", ok |-> TRUE, req |-> rid])
  /\ reqCounter' = reqCounter + 1
  /\ UNCHANGED <<policyApplied, claims, acs, effectStack, layerGraph, activeScopes, scopeResources>>

\* 次状態
Next ==
  \/ ApplyPolicy
  \/ \E name \in LayerName, provides \in SUBSET Capability, requires \in SUBSET LayerName:
       RegisterLayer(name, provides, requires)
  \/ \E sid \in ScopeId: EnterScope(sid)
  \/ \E sid \in ScopeId: ExitScope(sid)
  \/ \E ch \in ContentHash, sc \in Scope, allowSet \in SUBSET AllowTag, rid \in Rid, sid \in ScopeId:
       V2_Upsert(ch, sc, allowSet, rid, sid)
  \/ \E id \in ACId, scopeSet \in SUBSET Scope, allowSet \in SUBSET AllowTag, rid \in Rid:
       V2_Activate(id, scopeSet, allowSet, rid)
  \/ \E ch \in ContentHash, rid \in Rid:
       V2_Feedback(ch, rid)

Spec == Init /\ [][Next]_vars

\* V2固有の不変条件
Inv_LayerAcyclic == LayerAcyclic

Inv_ScopedResource == ScopedResourceInvariant

Inv_CriticBounds ==
  \A ch \in DOMAIN critic : MinScore <= critic[ch] /\ critic[ch] <= MaxScore

Inv_LogReqUnique ==
  \A i, j \in 1..Len(logs) : i # j => logs[i].req # logs[j].req

Inv_AC_Allowed ==
  \A id \in DOMAIN acs :
    \A ch \in acs[id].claims :
      claims[ch].scope \in acs[id].scope /\ claims[ch].allow \cap acs[id].allow # {}

\* ライブネス: 全Effectが最終的に解決
Liveness_EffectsResolve == <>[] (effectStack = << >>)

====
