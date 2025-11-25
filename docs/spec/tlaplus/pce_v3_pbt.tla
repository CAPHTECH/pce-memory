---- MODULE pce_v3_pbt ----
\* V3: PBT-First Design (Property-Based Testing as Specification)
\* fast-checkスタイルのトレースベース仕様

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  ContentHash,
  Scope,
  AllowTag,
  ACId,
  Rid,
  MinScore,
  MaxScore,
  MinCoverage     \* 最小カバレッジ要件

VARIABLES
  policyApplied,
  claims,
  acs,
  critic,
  \* V3固有: トレースとオラクル
  traceLog,       \* 実行トレース [(cmd, args, observation)]
  coverageCount   \* カバレッジカウンタ

vars == <<policyApplied, claims, acs, critic, traceLog, coverageCount>>

\* 定数: シードの範囲
MaxSeed == 100

\* トレースレコード
TraceRec == [cmd: STRING, args: STRING, obs: STRING]

\* 型制約
TypeInv ==
  /\ policyApplied \in BOOLEAN
  /\ claims \in [ContentHash -> [scope: Scope, allow: SUBSET AllowTag]]
  /\ acs \in [ACId -> [claims: SUBSET ContentHash, allow: SUBSET AllowTag, scope: SUBSET Scope]]
  /\ critic \in [ContentHash -> MinScore..MaxScore]
  /\ traceLog \in Seq(TraceRec)
  /\ coverageCount \in 0..100

\* オラクル関数（期待される観測値）
Oracle(cmd, args, state) ==
  CASE cmd = "upsert" ->
    IF args \in DOMAIN claims /\ claims[args].allow # {}
    THEN "duplicate"
    ELSE "ok"
  [] cmd = "activate" -> "ok"
  [] cmd = "feedback" ->
    IF args \in DOMAIN claims /\ claims[args].allow # {}
    THEN "ok"
    ELSE "not_found"
  [] OTHER -> "unknown"

\* オラクル整合性: 全トレースが期待と一致
OracleConsistency ==
  \A i \in 1..Len(traceLog):
    LET entry == traceLog[i] IN
    entry.obs = Oracle(entry.cmd, entry.args, claims)

\* カバレッジ境界
CoverageBound == coverageCount >= MinCoverage

\* ヘルパー
DefaultScope == CHOOSE s \in Scope : TRUE

\* 初期状態
Init ==
  /\ policyApplied = FALSE
  /\ claims = [c \in ContentHash |-> [scope |-> DefaultScope, allow |-> {}]]
  /\ acs = [id \in ACId |-> [claims |-> {}, allow |-> {}, scope |-> {}]]
  /\ critic = [c \in ContentHash |-> MinScore]
  /\ traceLog = << >>
  /\ coverageCount = 0

\* ポリシー適用
ApplyPolicy ==
  /\ ~policyApplied
  /\ policyApplied' = TRUE
  /\ traceLog' = Append(traceLog, [cmd |-> "policy", args |-> "", obs |-> "ok"])
  /\ coverageCount' = coverageCount + 1
  /\ UNCHANGED <<claims, acs, critic>>

\* Upsert操作（トレース記録）
V3_Upsert(ch, sc, allowSet) ==
  /\ policyApplied
  /\ coverageCount < 100
  /\ LET obs == IF ch \in DOMAIN claims /\ claims[ch].allow # {}
                THEN "duplicate"
                ELSE "ok"
     IN
     /\ traceLog' = Append(traceLog, [cmd |-> "upsert", args |-> "ch", obs |-> obs])
     /\ IF obs = "ok"
        THEN claims' = [claims EXCEPT ![ch] = [scope |-> sc, allow |-> allowSet]]
        ELSE claims' = claims
     /\ critic' = IF obs = "ok"
                  THEN [critic EXCEPT ![ch] = MinScore]
                  ELSE critic
     /\ coverageCount' = coverageCount + 1
     /\ UNCHANGED <<policyApplied, acs>>

\* Activate操作
V3_Activate(id, scopeSet, allowSet) ==
  /\ policyApplied
  /\ coverageCount < 100
  /\ id \in ACId
  /\ LET matchedClaims == {ch \in DOMAIN claims :
         claims[ch].scope \in scopeSet /\ claims[ch].allow \cap allowSet # {}}
     IN
     /\ acs' = [acs EXCEPT ![id] = [claims |-> matchedClaims, allow |-> allowSet, scope |-> scopeSet]]
     /\ traceLog' = Append(traceLog, [cmd |-> "activate", args |-> "id", obs |-> "ok"])
     /\ coverageCount' = coverageCount + 1
     /\ UNCHANGED <<policyApplied, claims, critic>>

\* Feedback操作
V3_Feedback(ch) ==
  /\ policyApplied
  /\ coverageCount < 100
  /\ LET obs == IF ch \in DOMAIN claims /\ claims[ch].allow # {}
                THEN "ok"
                ELSE "not_found"
     IN
     /\ traceLog' = Append(traceLog, [cmd |-> "feedback", args |-> "ch", obs |-> obs])
     /\ IF obs = "ok"
        THEN critic' = [critic EXCEPT ![ch] = IF critic[ch] < MaxScore THEN critic[ch] + 1 ELSE MaxScore]
        ELSE critic' = critic
     /\ coverageCount' = coverageCount + 1
     /\ UNCHANGED <<policyApplied, claims, acs>>

\* 次状態
Next ==
  \/ ApplyPolicy
  \/ \E ch \in ContentHash, sc \in Scope, allowSet \in SUBSET AllowTag:
       V3_Upsert(ch, sc, allowSet)
  \/ \E id \in ACId, scopeSet \in SUBSET Scope, allowSet \in SUBSET AllowTag:
       V3_Activate(id, scopeSet, allowSet)
  \/ \E ch \in ContentHash:
       V3_Feedback(ch)

Spec == Init /\ [][Next]_vars

\* V3固有の不変条件（最小限）
\* オラクル整合性は実行時にfast-checkが検証

Inv_CriticBounds ==
  \A ch \in DOMAIN critic : MinScore <= critic[ch] /\ critic[ch] <= MaxScore

Inv_AC_Allowed ==
  \A id \in DOMAIN acs :
    \A ch \in acs[id].claims :
      claims[ch].scope \in acs[id].scope /\ claims[ch].allow \cap acs[id].allow # {}

\* ライブネス: カバレッジ達成
Liveness_Coverage == <>(CoverageBound)

====
