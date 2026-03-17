# pce-memory 実用化レビュー

## 1. 概要

### 一言でいうと

pce-memory は、エージェントがプロジェクト知識をローカルに保存し、次のタスク開始時に想起するための MCP サーバーです。

### いまのシステム像

- `claims`: 長期記憶。`fact / preference / task / policy_hint` を保存する
- `observations`: 短期記憶。TTL 付きで保持し、必要に応じて Claim 化する
- `active_contexts`: 想起結果。`activate` でその時点の作業文脈を作る
- `feedback / critic`: 想起結果への評価を次回ランキングに反映する
- `entities / relations`: 知識をグラフとして補助的に構造化する
- `boundary policy`: `scope` と `boundary_class` で越境を防ぐ

### 役に立つとき

- 作業再開時に、前回の判断や未完了タスクを思い出したい
- 設計判断や命名規約を、毎回人間が説明し直すのをやめたい
- バグの再発防止知識を、会話ログではなく検索可能な形で残したい
- チームでローカル知識を同期したい

## 2. 現状の強み

### 土台はかなり良い

- Boundary-first で、記憶より先に越境防止を考えている
- DuckDB ベースで自己ホストしやすい
- `observe / upsert / activate / feedback` の最低限の流れは実装済み
- Graph Memory と sync まで視野に入っている
- テストは広く、現時点で `pnpm test` と `pnpm typecheck` は通る

### 「プロダクトの芯」は明確

このリポジトリは単なるメモ帳ではなく、以下のループを狙っています。

1. 作業前に `activate` で想起する
2. 作業中の重要な決定だけを `upsert` する
3. 使えた知識を `feedback` で重み付けする
4. 次回の想起精度を上げる

このループが回れば、pce-memory は実際に価値を出せます。

## 3. いま「実際に役立つ」を阻害している点

### 3.1 取り込みがまだ手作業寄り

`observe` はあるものの、抽出モードは実質 `noop` と `single_claim_v0` だけです。つまり「良い記憶を自動で作る」より、「人間かエージェントが上手に upsert する」ことに依存しています。

この状態だと、毎回の運用コストが高くなり、継続利用されにくいです。

### 3.2 検索面が仕様に比べて弱い

- ドキュメントでは `pce_memory_search` が前面に出ていますが、実装は `activate` 中心です
- ランキングの主要パラメータは policy ではなく定数で固定されています
- `active_contexts` は最小保存で、ドキュメントが想定する `expires_at` や `policy_version` を持つ AC 管理にはなっていません

これだと「思い出せるか」「なぜそれが出たか」を改善しにくいです。

### 3.3 統合面に未完成が残っている

- `@pce/sdk-ts` は README 上でもプレースホルダーです
- ドキュメントが想定する starter / SDK / package 構成と、現リポジトリの実装にズレがあります
- このセッション環境でも `pce_memory_*` ツールは直接使えず、導入経路がまだ安定していません

良いメモリでも、エージェントが自然に使えなければ役に立ちません。

### 3.4 ドキュメントと実装のドリフトがある

- 仕様書にある機能が未実装、または挙動が簡略化されている箇所がある
- plugin / skill 側の前提と、サーバー側の型や機能にズレがある箇所がある

これは信頼を下げます。メモリ基盤は「書いてある通りに動く」が重要です。

## 4. 実用化のための優先順位

### P0: まず 1 人のエージェント作業で毎日使えるようにする

最優先は、理想機能より運用摩擦の低減です。

#### やること

1. 公式の導入経路を 1 本に絞る
   - 例: Claude Code plugin を正式経路にする
   - 初期化、DB パス、policy 適用、初回 activate を自動化する

2. `activate` 前提の運用を完成させる
   - 「新しいタスク開始時に必ず recall される」ことを保証する
   - compaction 後の再 activate を自動化する

3. 記録テンプレートを固定する
   - 記録対象を `design decision / convention / bug root cause / task state` に絞る
   - 長文自由入力ではなく、短い構造化テンプレートにする

4. ドキュメントと実装を一致させる
   - ない機能は docs から外すか、最小実装を入れる
   - まず「期待を外さない」状態にする

### P1: 記憶の質を上げる

P0 ができても、記録の質が低いとノイズが増えます。

#### やること

1. `observe` からの抽出を強化する
   - task state
   - decision
   - constraint
   - root cause
   - convention

2. 古い知識と重複知識を整理する
   - 同一内容の統合
   - task 完了時の陳腐化処理
   - contradiction 候補の検知

3. retrieval を policy 駆動にする
   - `alpha / k_txt / k_vec / threshold` を policy から読む
   - score の内訳を返して改善可能にする

4. provenance を使いやすくする
   - commit / file / note を自動付与
   - 「どこから来た知識か」を必ず辿れるようにする

### P2: チーム知識基盤として効くようにする

ここまで行って初めて「個人用メモ」から「共有知識基盤」になります。

#### やること

1. sync を日常運用に入れる
   - push / pull を git hook と自然に接続する
   - conflict の見え方を改善する

2. Graph Memory を recall に使う
   - いまは主に保管用途なので、依存関係や関連コンポーネント経由で recall に効かせる

3. 健全性を可視化する
   - helpful rate
   - outdated rate
   - task recovery success rate
   - activate latency
   - claim reuse rate

## 5. 「実際に役立つ」を判断する基準

次の 4 つを満たせば、pce-memory は実用品になり始めています。

1. 新しいタスク開始時に、関連知識が自動で 1 回は recall される
2. recall された知識のうち、一定割合が `helpful` になる
3. タスク終了時に、重要知識だけが短く記録される
4. 1 週間後に同じ問題へ戻ったとき、人間が過去ログを掘らずに再開できる

## 6. 具体的な次アクション案

### いま着手するならこの順番

1. `実装と docs の差分棚卸し`
   - `search`, `AC expiry`, `SDK`, plugin 前提の差分を潰す

2. `P0 運用の固定`
   - Claude Code plugin 経由で
     - state check
     - policy apply
     - task start activate
     - stop 時の task upsert / feedback
     を一連で確実に動かす

3. `記録テンプレートの導入`
   - 英語で短く書く
   - task と fact を分ける
   - completed task を新規 upsert しない

4. `observe 抽出の強化`
   - ファイル変更や会話から、上記テンプレートに沿って Claim 化する

5. `運用指標の追加`
   - helpful / outdated / duplicate の件数を見える化する

## 7. 結論

pce-memory は「実用性の核」はすでにあります。足りないのは新機能の量より、次の 3 点です。

- 使い方を 1 本化すること
- 良い記憶を低コストで残せること
- 仕様と実装のズレを減らすこと

要するに、今やるべきは「より賢い記憶」より「毎回ちゃんと使われる記憶」に寄せることです。
