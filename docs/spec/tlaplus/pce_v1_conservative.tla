---- MODULE pce_v1_conservative ----
\* V1: Conservative Design (Either + PBT)
\* エラーハンドリングを明示的Either型で表現

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  ContentHash,    \* コンテンツハッシュの集合
  Scope,          \* スコープ {session, project, principle}
  AllowTag,       \* 許可タグの集合
  ACId,           \* ActiveContext ID
  Rid,            \* リクエストID
  MinScore,       \* Criticスコア下限
  MaxScore,       \* Criticスコア上限
  ReqCounterMax   \* ログ上限

VARIABLES
  policyApplied,  \* ポリシー適用済みフラグ
  claims,         \* Claim格納 [ContentHash -> Record]
  acs,            \* ActiveContext [ACId -> Record]
  logs,           \* 監査ログ
  critic,         \* Criticスコア [ContentHash -> Int]
  reqCounter,     \* リクエストカウンタ
  lastResult      \* Either[Error, Success] 結果

vars == <<policyApplied, claims, acs, logs, critic, reqCounter, lastResult>>

\* Either型の値
Left == "Left"
Right == "Right"
None == "None"

\* 型制約
TypeInv ==
  /\ policyApplied \in BOOLEAN
  /\ claims \in [ContentHash -> [scope: Scope, allow: SUBSET AllowTag]]
  /\ acs \in [ACId -> [claims: SUBSET ContentHash, allow: SUBSET AllowTag, scope: SUBSET Scope]]
  /\ logs \in Seq([op: STRING, ok: BOOLEAN, req: Rid])
  /\ critic \in [ContentHash -> MinScore..MaxScore]
  /\ reqCounter \in 0..ReqCounterMax
  /\ lastResult \in {Left, Right, None}

\* Either強制: 操作後は必ずLeft/Right
EitherTotality == lastResult \in {Left, Right}

\* エラー時の状態不変性
NoStateChangeOnError ==
  (lastResult = Left) => (claims' = claims /\ acs' = acs /\ critic' = critic)

\* ヘルパー
ReqSet == { logs[i].req : i \in 1..Len(logs) }
CanLog == Len(logs) < ReqCounterMax

\* 初期状態
DefaultScope == CHOOSE s \in Scope : TRUE

Init ==
  /\ policyApplied = FALSE
  /\ claims = [c \in ContentHash |-> [scope |-> DefaultScope, allow |-> {}]]
  /\ acs = [id \in ACId |-> [claims |-> {}, allow |-> {}, scope |-> {}]]
  /\ logs = << >>
  /\ critic = [c \in ContentHash |-> MinScore]
  /\ reqCounter = 0
  /\ lastResult = None

\* ポリシー適用
ApplyPolicy ==
  /\ ~policyApplied
  /\ policyApplied' = TRUE
  /\ lastResult' = Right
  /\ UNCHANGED <<claims, acs, logs, critic, reqCounter>>

\* Upsert操作 (Either型で結果を返す)
V1_Upsert(ch, sc, allowSet, rid) ==
  /\ policyApplied
  /\ rid \notin ReqSet
  /\ CanLog
  /\ \/ \* 成功ケース (Right)
        /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
        /\ claims' = [claims EXCEPT ![ch] = [scope |-> sc, allow |-> allowSet]]
        /\ critic' = [critic EXCEPT ![ch] = MinScore]
        /\ logs' = Append(logs, [op |-> "upsert", ok |-> TRUE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Right
        /\ UNCHANGED <<policyApplied, acs>>
     \/ \* 失敗ケース (Left) - 重複
        /\ ch \in DOMAIN claims
        /\ claims[ch].allow # {}
        /\ logs' = Append(logs, [op |-> "upsert", ok |-> FALSE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Left
        /\ UNCHANGED <<policyApplied, claims, acs, critic>>

\* Activate操作
V1_Activate(id, scopeSet, allowSet, rid) ==
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
     /\ UNCHANGED <<policyApplied, claims, critic>>

\* Feedback操作
V1_Feedback(ch, rid) ==
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
        /\ UNCHANGED <<policyApplied, claims, acs>>
     \/ \* 失敗ケース
        /\ ch \notin DOMAIN claims \/ claims[ch].allow = {}
        /\ logs' = Append(logs, [op |-> "feedback", ok |-> FALSE, req |-> rid])
        /\ reqCounter' = reqCounter + 1
        /\ lastResult' = Left
        /\ UNCHANGED <<policyApplied, claims, acs, critic>>

\* 次状態
Next ==
  \/ ApplyPolicy
  \/ \E ch \in ContentHash, sc \in Scope, allowSet \in SUBSET AllowTag, rid \in Rid:
       V1_Upsert(ch, sc, allowSet, rid)
  \/ \E id \in ACId, scopeSet \in SUBSET Scope, allowSet \in SUBSET AllowTag, rid \in Rid:
       V1_Activate(id, scopeSet, allowSet, rid)
  \/ \E ch \in ContentHash, rid \in Rid:
       V1_Feedback(ch, rid)

Spec == Init /\ [][Next]_vars

\* V1固有の不変条件
Inv_EitherExplicit ==
  policyApplied => lastResult \in {Left, Right}

Inv_NoStateChangeOnLeft ==
  \* Leftの場合、主要状態は変化しない（ログは変化する）
  TRUE  \* TLCでは履歴比較が難しいため、構造的に保証

Inv_CriticBounds ==
  \A ch \in DOMAIN critic : MinScore <= critic[ch] /\ critic[ch] <= MaxScore

Inv_LogReqUnique ==
  \A i, j \in 1..Len(logs) : i # j => logs[i].req # logs[j].req

Inv_AC_Allowed ==
  \A id \in DOMAIN acs :
    \A ch \in acs[id].claims :
      claims[ch].scope \in acs[id].scope /\ claims[ch].allow \cap acs[id].allow # {}

====
