# ewasm / SuperStack 残ギャップ分析

更新データ: `bench-results/wsouper/raw/{ewasm,superstack}-{sign_test,mux1_1}.csv`（2026-07-02、両方 `--split 12`, segment timeout 5s）

**比較前提:** 今回の CSV は ewasm / SuperStack とも `initial_length` max が 12。したがって、以前の split 12 vs 15 による `block_id` ずれではなく、`block_id + initial_length` 一致 subset の差は実ギャップとして扱う。

---

## サマリ

| benchmark | tool | blocks | total initial | total saved | reduction |
|-----------|------|--------|---------------|-------------|-----------|
| sign_test | ewasm | 1447 | 12752 | **667** | **5.23%** |
| sign_test | SuperStack | 1444 | 12746 | **958** | **7.52%** |
| mux1_1 | ewasm | 1416 | 12292 | **675** | **5.49%** |
| mux1_1 | SuperStack | 1413 | 12286 | **849** | **6.91%** |

全体差は sign_test **291 命令**、mux1_1 **174 命令**。合計 **465 命令**で、総 initial 約 25k に対して **約 1.9%**。

`block_id + initial_length` 一致 subset で、SS が ewasm より短い分だけを足すと:

| benchmark | matched blocks | SS > ewasm gap | gap blocks |
|-----------|----------------|----------------|------------|
| sign_test | 1444 | **295** | **188** |
| mux1_1 | 1413 | **178** | **139** |
| 合計 | 2857 | **473** | **327** |

差分の大半は ewasm 側も `outcome=optimal` で終わっている。timeout ではなく、現 SAT 符号化上の探索空間・語彙・上界の不足が主因。

| benchmark | ewasm outcome | gap | blocks |
|-----------|---------------|-----|--------|
| sign_test | `optimal` | **291** | **184** |
| sign_test | `non_optimal` | **4** | **4** |
| mux1_1 | `optimal` | **174** | **135** |
| mux1_1 | `non_optimal` | **4** | **4** |

---

## 残 gap の分類

分類は raw CSV の `previous_solution` / `solution_found` を見た heuristic。重複なしで、SS が ewasm より短い matched blocks のみを集計。

| 分類 | sign_test gap / blocks | mux1_1 gap / blocks | 合計 gap / blocks | 典型 |
|------|------------------------|---------------------|-------------------|------|
| **const-fold / algebra** | **139 / 60** | **22 / 11** | **161 / 71** | `i32.const 7; i32.const 40; i32.mul` → `i32.const 280` |
| **tee / spill schedule** | **86 / 84** | **86 / 84** | **172 / 168** | `local.set; local.get` をさらに tee 融合、ローカル退避をスタック保持に変更 |
| **zero / bitmask fold + tee** | **67 / 43** | **67 / 43** | **134 / 86** | `(0 & 0xffffffff) << 1` を 0 に畳み、`local.tee` で複数 slot に伝播 |
| **other** | **3 / 1** | **3 / 1** | **6 / 2** | 少数の複合ケース |

---

## 1. const-fold / algebra（161 命令 / 71 blocks）

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

`build_ops` の binop table は `V×V` に対する結果が `V` 内の e-class にある場合だけ edge を作るため、結果定数が `V` に無いと `Const(280)` や `Const(160)` を使う短い解が探索空間外になる。

### 修正案

**P1: symbolic execution seed での constant folding。**

- `V × V` や rewrite table 側で定数閉包を広げると、語彙・CNF が膨らみ timeout が増える
- `SymMachine::exec` / `apply_value_op` の段階で、引数が concrete integer literal のときだけ deterministic に fold する
- まずは trap しない `i32/i64 add/sub/mul/and/or/xor/shl/shr` に限定する（`div/rem` は後回し）
- これにより、オリジナル命令列の記号実行 seed と trace witness が自然に `280`, `160`, `0` などを拾う
- `function_111_block_8_4` はこの方式で SuperStack と同じ **8 命令**まで到達
- 期待効果: `const-fold / algebra` の大半（最大 161 命令）

---

## 2. tee / spill schedule（172 命令 / 168 blocks）

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

### 原因

`local.set` / `local.get` をさらに深く融合し、ローカル退避をスタック保持へ寄せるスケジュールを SS が見つけている。ewasm は `Tee` を持つが、降順 SAT が現 encoding 内で `optimal` に到達しており、短いスケジュールの探索が弱い。

timeout が主因ではない（gap の大半は `outcome=optimal`）。

### 修正案

**P1: greedy tee seed / 上界導入。**

- `set x; get x`、または `set x` 後に値がすぐ再利用される形を局所的に `tee x` へ置換する greedy pass を作る
- 生成した短い候補を SAT の初期上界として使う
- SAT は「候補より短い解がないか」の証明に集中させる
- 期待効果: tee / spill schedule の一部（最大 172 命令）

---

## 3. zero / bitmask fold + tee（134 命令 / 86 blocks）

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

**P1: constant-propagation tee seed。**

- `local.set x` に入る値が concrete constant と分かる場合、連続する同一定数代入を `const c; tee ...; set ...` へまとめる greedy seed を作る
- bitmask / shift をまたぐ 0 伝播は symbolic execution の constant folding で seed 上は `0` になる
- zero は一般の constant propagation の特殊例として扱う
- 期待効果: zero / bitmask fold + tee の大半（最大 134 命令）

---

## 4. other（6 命令 / 2 blocks）

少数の複合ケース。上の 3 系統を入れた後に再分類する。

---

## 実装優先度

| 優先度 | 修正 | 狙う gap | 理由 |
|--------|------|----------|------|
| **P1 done** | **symbolic execution seed constant folding** | const-fold / algebra **161** | `V × V` 定数閉包ではなく、記号実行後の seed を畳む。`function_111_block_8_4` は SS と同じ 8 命令 |
| **P1** | **constant-propagation tee seed** | zero / bitmask + tee **134** | zero を一般の定数伝播として扱い、`function_14_*` 系の `const; tee; tee` 形を狙う |
| **P1** | **greedy tee seed / 上界導入** | tee / spill **172** | gap 最大だが設計はやや重い。SAT に候補上界を渡す形が安全 |
| **P2** | selective H slack / 二段階 solve | timeout **8** | 現 gap の主因ではないが、H slack の副作用抑制に必要 |

最初の **symbolic execution seed constant folding** は実装済み。次は **constant-propagation tee seed**。この 2 つで algebra/zero 系の最大 **295 命令**（重複なし heuristic 上）を狙える。
