# ewasm / SuperStack 残ギャップ分析

更新データ: `bench-results/wsouper/raw/{ewasm,superstack}-{sign_test,mux1_1}.csv`（2026-07-02、両方 `--split 12`, segment timeout 5s）

**比較前提:** 今回の CSV は ewasm / SuperStack とも `initial_length` max が 12。したがって、以前の split 12 vs 15 による `block_id` ずれではなく、`block_id + initial_length` 一致 subset の差は実ギャップとして扱う。

**計測条件:** seed-closed SAT encoding（`V=SubExpr(EqSat(SubExpr(seed)))`、edge 構造抽出、`⊤` 削除、`≡_R` boundary、invalid model blocking）適用後の再計測。

---

## サマリ

| benchmark | tool | blocks | total initial | total saved | reduction |
|-----------|------|--------|---------------|-------------|-----------|
| sign_test | ewasm | 1447 | 12752 | **851** | **6.67%** |
| sign_test | SuperStack | 1444 | 12746 | **958** | **7.52%** |
| mux1_1 | ewasm | 1416 | 12292 | **741** | **6.03%** |
| mux1_1 | SuperStack | 1413 | 12286 | **849** | **6.91%** |

seed-closed encoding 後、全体差は sign_test **107 命令**、mux1_1 **108 命令**。合計 **215 命令**で、総 initial 約 25k に対して **約 0.8%**。

`block_id + initial_length` 一致 subset で、SS が ewasm より短い分だけを足すと:

| benchmark | matched blocks | SS > ewasm gap | gap blocks |
|-----------|----------------|----------------|------------|
| sign_test | 1444 | **111** | **109** |
| mux1_1 | 1413 | **112** | **110** |
| 合計 | 2857 | **223** | **219** |

前回（encoding 修正前）の **229 / 225** から **6 命令 / 6 blocks** 縮小。差分の大半は ewasm 側も `outcome=optimal` で終わっている。timeout ではなく、残る completeness gap（主に tee/spill schedule と stack height `H`）が主因。

| benchmark | ewasm outcome (gap blocks) | gap | blocks |
|-----------|----------------------------|-----|--------|
| sign_test | `optimal` | **111** | **109** |
| sign_test | `non_optimal` | **0** | **0** |
| mux1_1 | `optimal` | **111** | **109** |
| mux1_1 | `non_optimal` | **1** | **1** |

gap size は **1 命令差が 215 blocks**、**2 命令差が 4 blocks**。残りは大きな未解決カテゴリというより、同型の小さな `tee/spill` 差が多数残っている。

ewasm 全体の `non_optimal` は sign_test **7 blocks**、mux1_1 **15 blocks**（encoding 不完全や invalid model 等）。うち SS より短い gap に寄与するのは mux1_1 の `function_24_block_0_109` の 1 block のみ。

---

## 残 gap の分類

分類は raw CSV の `previous_solution` / `solution_found` を見た heuristic。重複なしで、SS が ewasm より短い matched blocks のみを集計。

| 分類 | sign_test gap / blocks | mux1_1 gap / blocks | 合計 gap / blocks | 典型 |
|------|------------------------|---------------------|-------------------|------|
| **tee / spill schedule** | **111 / 109** | **112 / 110** | **223 / 219** | `local.set; local.get` を `local.tee` に寄せ、ローカル退避をスタック保持に変更 |
| **const-fold / algebra** | **0 / 0** | **0 / 0** | **0 / 0** | `function_111_block_8_4` は SS と同じ 8 命令まで到達 |
| **zero / bitmask fold + tee** | **0 / 0** | **0 / 0** | **0 / 0** | `function_14_block_0_0` は 4 命令まで到達 |
| **other** | **0 / 0** | **0 / 0** | **0 / 0** | 現 CSV では主要 residual は tee/spill に集約 |

関数別に見ると、残り gap は 5 系統に集中している:

| function | gap / blocks | 主な形 |
|----------|--------------|--------|
| `function_24_*` | **67 / 63** | carry/shift の中間値を `set/get` せずスタック保持し、後段で `tee` |
| `function_25_*` | **60 / 60** | load/`tee` 済み値を使う mul/add の後、更新値を `tee` で残す |
| `function_14_*` | **34 / 34** | 0/bitmask 系は閉じたが、通常の add/shift 更新で `set/get` が残る |
| `function_23_*` | **34 / 34** | load/mul/add の順序変更 + `tee` によるローカル退避削減 |
| `function_13_*` | **28 / 28** | load32 + mul/add + high-word shift の `tee` スケジュール差 |

encoding 修正で `function_24_*` が **71→67 命令 / 67→63 blocks**、`function_25_*` が **62→60 命令** に改善。`function_14/23/13` は変化なし。

---

## 1. const-fold / algebra（resolved）

### 典型例

`function_111_block_8_4`:

```text
prev:
i32.add local.get[7] i32.const[120] i32.add
i32.const[7] i32.const[40] i32.mul
local.get[6] i32.add
i32.const[4] i32.const[40] i32.mul

ewasm:
... i32.const[7] i32.const[40] i32.mul ... i32.const[4] i32.const[40] i32.mul

SuperStack:
... local.get[6] i32.const[280] i32.add i32.const[160]
```

### 原因

`V` に元トレースで出た定数や `0,1,2,-1` は入るが、`40*7=280` や `40*4=160` のような**元トレースにない合成定数**が入らない。

`build_ops` の binop table は `V×V` に対する結果が `V` 内の e-class にある場合だけ edge を作るため、結果定数が `V` に無いと `Const(280)` や `Const(160)` を使う短い解が探索空間外になる。**（2026-07-02 修正後）** `V = SubExpr(EqSat(SubExpr(seed)))` に閉じ、edge は `V` 内の式構造から抽出する方式に変更済み。

### 修正案

**P1 done: symbolic execution seed での constant folding。**

- `V × V` や rewrite table 側で定数閉包を広げると、語彙・CNF が膨らみ timeout が増える
- `SymMachine::exec` / `apply_value_op` の段階で、引数が concrete integer literal のときだけ deterministic に fold する
- まずは trap しない `i32/i64 add/sub/mul/and/or/xor/shl/shr` に限定する（`div/rem` は後回し）
- これにより、オリジナル命令列の記号実行 seed と trace witness が自然に `280`, `160`, `0` などを拾う
- `function_111_block_8_4` はこの方式で SuperStack と同じ **8 命令**まで到達
- 現 CSV ではこの分類の residual gap は見えていない

---

## 2. tee / spill schedule（223 命令 / 219 blocks）

### 典型例

`function_24_block_0_75`:

```text
prev:
i64.add local.set[3]
local.get[4] local.get[3] i64.const[32] i64.shr_u i64.add local.set[4]
local.get[4] i64.const[32] i64.shr_u local.set[3]

ewasm:
i64.add i64.const[32] i64.shr_u local.set[3]
local.get[4] local.get[3] i64.add local.tee[4]
i64.const[32] i64.shr_u local.set[3]

SuperStack:
i64.add i64.const[32] i64.shr_u
local.get[4] i64.add local.tee[4]
i64.const[32] i64.shr_u local.set[3]
```

（再計測 CSV: ewasm **11 命令**、SuperStack **9 命令**、gap **2**。unit test では `scratch_locals: 1` 等で SS 長まで到達。）

### 原因

`local.set` / `local.get` をさらに深く融合し、ローカル退避をスタック保持へ寄せるスケジュールを SS が見つけている。ewasm は `Tee` を持つが、SAT が `optimal` と報告しているにもかかわらず SS より短い valid solution がある — これは **completeness bug**（soundness bug ではない）。

主因候補:

- ~~`V×V` から pure op table を作り `⊤` に逃がす encoding~~（修正済み、gap 6 命令分改善）
- final boundary の exact `V` index pin（checker は `≡_R`）（修正済み）
- e-class 内 result を 1 代表に潰す pure op table（修正済み）
- invalid SAT model 発見後、同じ長さを再探索しない（修正済み）
- stack height `H` 不足（代表例 function_14/24 では `scratch_locals: 1` で改善）

timeout が主因ではない（gap **222 / 223** は `outcome=optimal`）。残りはほぼ全て 1 命令差で、典型的には `set x; get x` を `tee x` に寄せるか、計算値をローカルに落とさずスタックに保持するだけで閉じる。

### 修正案

**P1 done: seed-closed SAT encoding（completeness 修正）。greedy tee seed / 上界導入は撤回。**

探索空間を **`V = SubExpr(EqSat(SubExpr(seed)))`** に閉じる:

- `build_vocab`: seed の subtree を joint eqsat 後 materialize して `V` に挿入
- `build_ops`: `V×V` 候補投入をやめ、`V` 内の式構造から pure op edge を抽出
- pure op の `⊤` fallback を削除し、domain 外 operand では op を選べない partial function 制約に
- final boundary を `≡_R`（`pin_stack_equiv` / `pin_local_equiv`）に揃える
- invalid model は blocking clause で同長再探索
- `|V|` cap で打ち切った場合や invalid model ありは `proven_optimal=false` → CSV `outcome=non_optimal`
- stack height `H` slack は副作用抑制のため P2 で継続検討

**再計測結果:** residual gap **229→223 命令**（**-2.6%**）、**225→219 blocks**。主に `function_24/25` で改善。残 **223 命令**は上記 P2（`H` slack）と診断が次の焦点。

---

## 3. zero / bitmask fold + tee（representative resolved）

### 典型例

`function_14_block_0_0`:

```text
prev:
i64.const[0] local.set[2]
i64.const[0] local.set[3]
local.get[2] i64.const[4294967295] i64.and
i64.const[1] i64.shl local.set[2]
local.get[3] i64.const[1]

ewasm:
i64.const[0] local.tee[3]
i64.const[0] i64.const[4294967295] i64.and
i64.const[1] i64.shl local.set[2]
i64.const[1]

SuperStack:
i64.const[0] local.tee[2] local.tee[3] i64.const[1]
```

### 原因

ルールとしては `i64.and 0 ?a -> 0` や `i64.shl 0 ?a -> 0` 系は存在するが、短い解では「0 を一度作って、複数ローカルへ `tee` で伝播」する必要がある。ewasm は途中まで畳むが、`0` のスタック保持 + 複数 slot への `tee` 連鎖を最短化できていない。

### 修正案

**P1 done (代表例): constant propagation via symbolic execution seed（zero はその特殊例）。**

- `local.set x` に入る値が concrete constant と分かる場合、連続する同一定数代入を `const c; tee ...; set ...` へまとめるのは seed 側の eqsat で扱う
- bitmask / shift をまたぐ 0 伝播は symbolic execution の constant folding で seed 上は `0` になる
- `function_14_block_0_0` は現在 ewasm も **4 命令**まで到達
- 残る `function_14_*` は zero 専用ではなく、通常の tee/spill schedule として扱う

---

## 4. other（0 命令 / 0 blocks）

現 CSV では主要 residual は `tee / spill schedule` に集約された。

---

## 5. 残 gap 詳細調査（2026-07-02）

219 gap blocks / 223 命令を CSV 分析 + SAT probe（`gap_probe_csv_blocks` / `--classify-sat-gaps`）で分解。

### 5.1 4 バケット

| 分類 | ew_saved | gap | ew→ss | blocks | 命令 |
|------|----------|-----|-------|--------|------|
| **A: 無改善** | 0 | 1 | 12→11 | **199** | **199** |
| **B: 部分改善** | 1 | 1 | 11→10 | **14** | **14** |
| **C: 二段融合不足** | 1 | 2 | 11→9 | **4** | **8** |
| **D: 深い部分改善** | 5 | 1 | 7→6 | **2** | **2** |

unique `block_id` は **110**（sign_test / mux1_1 で重複）。

### 5.2 共通パターン（219 blocks 中）

- **213 blocks**: SS が ewasm より `local.tee` を 1 本多く使う
- **217 blocks**: SS が `local.set` + `local.get` を合計 2 本少ない（スタック保持 + tee 融合）
- **215 blocks** が 1 命令差、**4 blocks** が 2 命令差（いずれも `function_24_block_0_3` / `_75`）

典型（`function_14_block_0_13`）:

```text
ewasm (12, saved=0):
  add → set[2] → get[3] → get[2] → shr → add → get[5] → add → set[3] → get[1] → get[2]

SuperStack (11):
  add → tee[2] → shr → get[3] → add → get[5] → add → set[3] → get[1] → get[2]
```

ewasm は**元列をそのまま返す**（`saved=0`）か、`set/get` 1 回分だけ改善して止まる。

### 5.3 SAT 診断結果

`--classify-sat-gaps`（sign_test, 99 unique block_id, 10s timeout）:

```text
99/99  Solved { best_len: 12, proven_optimal: true, timed_out: false }
```

timeout ではなく、**encoding 内で L=12 が最短と証明**されている。SS の L=11 は encoding 外の valid schedule。

代表 block の probe（60s, `scratch_locals=1`, `H=stack_height_bound+1`）:

| block | solve | probe@L-1 | 備考 |
|-------|-------|-----------|------|
| `function_14_block_0_13` | 12, proven | **UNSAT** @11 | H=5,6,7 でも UNSAT |
| `function_25_block_0_10` | 12, proven | **UNSAT** @11 | |
| `function_13_block_0_10` | 12, proven | **UNSAT** @11 | |
| `function_23_block_0_12` | 12, proven | **UNSAT** @11 | |
| `function_24_block_0_101` | 12, proven | **UNSAT** @11 | |
| `function_24_block_0_75` | **11**, proven | **SAT** @11 | L=10,9 は H≤7 でも **UNSAT** |

### 5.4 主因（優先度順）

1. **tee / stack-hold スケジュールの encoding 不足（A+B+D, ~215 命令）**
   - SAT は `Tee` op を持つが、`set→get` を `tee` + スタック保持に置き換えた**短い並べ替え列**を L-1 で UNSAT と判定
   - **H 不足が主因ではない**: `function_14_block_0_13` は H=7 まで試しても L=11 UNSAT
   - 候補: Get/Set の `≡_R` ピン不足（final のみ `pin_local_equiv`）、pure op edge の並べ替え不足、step 列が許すスタックスケジュールの狭さ

2. **多段 tee 融合の上限（C, 8 命令）**
   - `function_24_block_0_3/_75`: L=11 は SAT+valid だが L=10/9 は UNSAT（SS=9）
   - 1 回分の `set/get` 削除はできるが、**2 回分の同時融合**（carry/shift 中間値のスタック保持）が encoding 外

3. **timeout / vocab cap / invalid model は主因ではない**
   - cat A の solver 時間: median ~1.8s, max ~5s（segment timeout 5s 内）
   - `proven_optimal=true` が 218/219 gap blocks

### 5.5 次の修正候補

| 優先 | 修正 | 状態 |
|------|------|------|
| **P2a (部分実装)** | Get/Set/Tee `pin_transfer_equiv`、Binop/Unop positive `≡_R` + ec-pair forbid | **実装済・102 tests pass**。`function_14_block_0_13` は L=11 依然 UNSAT |
| **P2a+** | set→tee 単点 variant の vocab + witness table 行追加 | **実装済・gap 変化なし** |
| **P2b** | 多段 stack-hold（function_24 L=9） | 未着手 |
| **P2c** | Ruler `≡_R` 網羅化（0701_suboptimal_cause §5.2 A） | 未着手・commutative reorder の前提 |
| **P2d** | fin 起点ゴール指向語彙（§5.2 C） | 未着手 |

**2026-07-02 実装メモ:** `≡_R` 境界拡張だけでは cat A（199 blocks）の L-1 probe は解消しない。`0701_suboptimal_cause.md` の通り、**スケジュール表現力**（tee + 命令並べ替え + スタック系列の語彙外）が残る。次は **A→B 完成** または **C（fin 閉包語彙）** が必要。

診断用: `cargo test --release gap_probe_csv_blocks -- --nocapture`

---

## 実装優先度

| 優先度 | 修正 | 狙う gap | 結果 |
|--------|------|----------|------|
| **P1 done** | **symbolic execution seed constant folding** | const-fold / algebra | `function_111_block_8_4` は SS と同じ 8 命令。residual **0** |
| **P1 done (代表例)** | **constant/zero propagation via symbolic execution** | zero / bitmask + tee | `function_14_block_0_0` は SS と同じ 4 命令。残りは tee/spill 問題 |
| **P1 done** | **seed-closed SAT encoding（completeness 修正）** | tee / spill **229→223** | `function_24` **-4** 命令、`function_25` **-2** 命令。残 **223 命令 / 219 blocks** |
| **P2a** | **Get/Set/Tee 境界の `≡_R` 化 + スケジュール制約見直し** | 残 tee/spill **~215** | cat A/B: L-1 probe UNSAT。H 増加では解消せず |
| **P2b** | **多段 stack-hold（function_24 二段融合）** | bucket C **8** | L=11 SAT だが L=9 UNSAT |
| **P3** | selective H slack / 二段階 solve | 副作用 block | `function_14_block_0_95` 等。cat A 単独では効果薄 |

次にやるなら **P2a: local/operand 境界の `≡_R` 化**（final だけでなく Get/Set/Tee step でも e-class 許容）と、**P2b: function_24 の二段融合**の witness 調査。
