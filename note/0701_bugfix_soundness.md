# ewasm / SuperStack 残ギャップ分析

更新データ: `bench-results/wsouper/combined_blocks.csv`（2026-07-02、更新済み `sign_test` / `mux1_1`, `--split 12`）

**比較前提:** ewasm / SuperStack とも `initial_length` max は 12。`block_id + initial_length` 一致 subset の差を実ギャップとして扱う。

**現在の実装状態:** seed-closed SAT encoding（`V=SubExpr(EqSat(SubExpr(seed)))`、edge 構造抽出、`⊤` 削除、`≡_R` boundary、invalid model blocking）に加えて、typed zero identity の canonicalization 前処理を追加済み。`function_14_block_0_52` の 7→6 gap は解消。

---

## サマリ

| benchmark | tool | blocks | total initial | total saved | reduction |
|-----------|------|--------|---------------|-------------|-----------|
| sign_test | ewasm | 1447 | 12752 | **957** | **7.50%** |
| sign_test | SuperStack | 1444 | 12746 | **958** | **7.52%** |
| mux1_1 | ewasm | 1416 | 12292 | **847** | **6.89%** |
| mux1_1 | SuperStack | 1413 | 12286 | **849** | **6.91%** |

全体削減量では ewasm と SuperStack はほぼ同等。total saved 差は sign_test **1 命令**、mux1_1 **2 命令**。

`block_id + initial_length` 一致 subset で、SS が ewasm より短い分だけを足すと:

| benchmark | matched blocks | SS > ewasm gap | gap blocks |
|-----------|----------------|----------------|------------|
| sign_test | 1444 | **5** | **5** |
| mux1_1 | 1413 | **6** | **6** |
| 合計 | 2857 | **11** | **11** |

前回の residual **223 命令 / 219 blocks** から **11 命令 / 11 blocks** まで縮小。残る gap はすべて **1 命令差**で、ewasm 側はすべて `outcome=non_optimal`。以前のように `optimal` と誤証明して SS 解を encoding 外に落とす状態ではない。

---

## 何が直ったか

### 1. seed-closed SAT encoding（完了）

主な変更:

- `build_vocab`: trace / boundary / fin-oriented seed の subtree を joint eqsat 後に materialize
- `build_ops`: `V×V` 候補投入ではなく、`V` 内の式構造と operational witness から pure-op edge を構築
- pure op の `⊤` fallback を削除し、domain 外 operand では op を選べない partial function 制約に変更
- final boundary と Get/Set/Tee transfer を `≡_R` ベースに拡張
- invalid model は同じ長さで blocking clause を追加して再探索
- `|V|` cap や invalid model が絡む場合は `proven_optimal=false`

この段階で、代表的な tee/spill gap は大きく縮小した。

### 2. i64 identity / typed zero canonicalization（完了）

`function_14_block_0_52` で、SuperStack の 6 命令解:

```text
local.get[7] local.get[13] i64.mul
i64.const[0] local.set[3] local.set[2]
```

に対して、ewasm は以前:

```text
local.get[7] local.get[13] i64.mul
i64.const[0] local.tee[3] i64.add local.set[2]
```

の 7 命令で止まっていた。

根本原因は `(i64.add 0 (i64.mul ?L7 ?L13))` と `(i64.mul ?L7 ?L13)` が canonicalization で同値にならなかったこと。`rules-ast3.cache` には `(i64.add 0 ?a) -> ?a` があるが、`ValueLang` 上の `I64Const(0)` と rewrite pattern の bare `0` の扱いがずれ、typed zero identity が効かない場合があった。

修正:

- `Canonizer::canon`
- `Canonizer::values_equivalent`
- `joint_saturate_materialize`
- `equiv_partition`

の前に、Wasm 型付き定数に依存する identity を明示的に正規化:

- `i32.add 0 x`, `i32.add x 0`
- `i32.and 0 x`, `i32.and x 0`
- `i64.add 0 x`, `i64.add x 0`
- `i64.and 0 x`, `i64.and x 0`

結果:

- `function_14_block_0_52`: ewasm **6 命令**、SuperStack **6 命令**
- `p2_schedule_gap_blocks_reach_superstack_length`: pass
- `gap_probe_csv_blocks`: pass

---

## 現在の残 gap

残 gap は 11 blocks / 11 命令。すべて 1 命令差。

| 分類 | sign_test gap / blocks | mux1_1 gap / blocks | 合計 gap / blocks | 典型 |
|------|------------------------|---------------------|-------------------|------|
| **function_24 tee/stack-hold** | **5 / 5** | **5 / 5** | **10 / 10** | load/mul/add 後の `set[4]; get[3]; get[4]; shr; add; set[3]` を `tee[4]` + stack-hold に寄せる |
| **function_25 tee/stack-hold** | **0 / 0** | **1 / 1** | **1 / 1** | load/tee 済み値を使う mul/add 後の更新値を `tee` で残す |
| **const-fold / algebra** | **0 / 0** | **0 / 0** | **0 / 0** | resolved |
| **zero / bitmask fold + tee** | **0 / 0** | **0 / 0** | **0 / 0** | `function_14_block_0_52` を含め resolved |

残 block:

| benchmark | block | ewasm | SuperStack | gap |
|-----------|-------|-------|------------|-----|
| sign_test | `function_24_block_0_7` | 12 | 11 | 1 |
| sign_test | `function_24_block_0_13` | 12 | 11 | 1 |
| sign_test | `function_24_block_0_43` | 12 | 11 | 1 |
| sign_test | `function_24_block_0_55` | 12 | 11 | 1 |
| sign_test | `function_24_block_0_121` | 12 | 11 | 1 |
| mux1_1 | `function_24_block_0_7` | 12 | 11 | 1 |
| mux1_1 | `function_24_block_0_13` | 12 | 11 | 1 |
| mux1_1 | `function_24_block_0_49` | 12 | 11 | 1 |
| mux1_1 | `function_24_block_0_81` | 12 | 11 | 1 |
| mux1_1 | `function_24_block_0_93` | 12 | 11 | 1 |
| mux1_1 | `function_25_block_0_2` | 12 | 11 | 1 |

典型（`function_24_block_0_7`）:

```text
ewasm:
i64.load32_u local.tee[13] local.get[8] i64.mul i64.add local.set[4]
local.get[3] local.get[4] i64.const[32] i64.shr_u i64.add local.set[3]

SuperStack:
i64.load32_u local.tee[13] local.get[8] i64.mul i64.add local.tee[4]
i64.const[32] i64.shr_u local.get[3] i64.add local.set[3]
```

現在残っているのは、ほぼ `set[4]` → `get[4]` を `tee[4]` に寄せ、`shr` の結果をスタック上で保持したまま後段の `add` に渡す 1 命令差。

---

## 以前の分類の現在地

| 旧分類 | 以前 | 現在 | 状態 |
|--------|------|------|------|
| const-fold / algebra | residual 0 | residual 0 | resolved |
| zero / bitmask fold + tee | representative resolved, `function_14_block_0_52` が残 | residual 0 | typed zero canonicalization で resolved |
| tee / spill schedule | **223 / 219** | **11 / 11** | 大部分 resolved。残りは `function_24/25` の 1 命令差 |
| multi-stage stack-hold | `function_24_block_0_75` など | `function_24_block_0_75` は ewasm=SS=9 | resolved |

---

## 検証コマンド

```bash
cargo test --release p2_schedule_gap_blocks_reach_superstack_length -- --nocapture
cargo test --release gap_probe_csv_blocks -- --nocapture
cargo test --release analyze_function_14_block_0_52 -- --nocapture
cargo test --release i64_typed_zero_identities -- --nocapture
cargo test --release i64_add -- --nocapture
cargo test --release i64_unary_signature -- --nocapture
```

確認済み:

- `p2_schedule_gap_blocks_reach_superstack_length`: pass
- `gap_probe_csv_blocks`: pass
- `function_14_block_0_52`: probe L=6 SAT + valid
- i64 add / unary synthesis regression: pass

---

## 次にやること

優先度は低くなった。残り 11 命令はすべて `function_24/25` の 1 命令差で、全体削減率への影響は小さい。

次に追うなら:

1. `function_24_block_0_7` の SS witness を CNF で固定し、どの final / stack transition が L=11 を拒否するかを見る
2. `local.set[4]` → `local.tee[4]` 後に、`shr` 結果と `local.get[3]` の operand order を許す edge / stack transition を確認
3. `non_optimal` になっている 37 + 42 blocks のうち、SS gap に寄与しないものは後回し

現時点では「SAT が最短を誤証明して大きく負ける」状態は解消済み。
