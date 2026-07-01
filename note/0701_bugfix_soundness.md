ewasmのSATは、タイムアウトしないならば、superstackと同じまたはそれよりも短い命令列を見つけるはずである。
ベンチマークの結果を分析して、これに反するケースがないか確認してください。
もし、反例があれば、ewasmのバグの原因を突き止めてください。

# ewasm 健全性・ベンチギャップ分析

更新データ: `bench-results/wsouper/raw/ewasm-{sign_test,mux1_1}.csv`（2026-07-01 21:57 実行、`--split 12`, segment timeout 5s, `-j 28`）  
SuperStack 参照: `superstack-{sign_test,mux1_1}.csv`（**旧実行** `--split 15`, segment timeout 10s）  
詳細分析: [`0701_ewasm_bug.md`](0701_ewasm_bug.md)、手法分析: [`0701_suboptimal_cause.md`](0701_suboptimal_cause.md)

**設計不変条件:** SAT 失敗時に A* へフォールバックしてはならない。

**SS 比較の前提:** 新 ewasm は `--split 12` でセグメント境界が変わるため、`block_id` だけでは `initial_length` が一致しないブロックが大半（sign_test **699/1214**、mux1_1 **664/1189**）。健全性・ギャップ比較は **`block_id` + `initial_length` 一致**（sign_test **515**、mux1_1 **525** ブロック）のみを用いる。

---

## 修正済み（2026-07-01）: OriginalUnsat / EncodeFailed

[`src/optimize/sat.rs`](../src/optimize/sat.rs) に以下を実装。

| 項目 | 内容 |
|------|------|
| **トレースエッジ注入** | `inject_trace_edges` — 元トレースの Binop/Unop/Const 遷移を E-graph とは独立に `ops` へマージ（OriginalUnsat 解消） |
| **ローカル op  pruning** | `active_local_slots` — セグメントで使用するスロットのみ `Get`/`Set`/`Tee` を生成（`\|OP\|` 削減） |
| **CNF 圧縮** | `classify_local_slots` + `pin_fixed_locals` — 不変ローカルの `locals_unchanged` を unit 節に短絡（EncodeFailed 解消） |
| **診断細分化** | `OriginalWitnessMissingOp` / `OriginalWitnessUnsat`（旧 `OriginalUnsat`） |

旧ギャップ 377 ブロックの `--classify-sat-gaps` 再診断（split 15 実行）: **OriginalWitnessMissingOp / OriginalWitnessUnsat / EncodeFailed は 0 件**（sign_test / mux1_1 とも）。

---

## 健全性チェック（修正後・split 12 実行）

**健全性バグ（誤って長い解を受理）は見つからなかった。**

| 観点 | 結果 |
|------|------|
| ewasm `no_solution` | **0 / 0 件**（sign_test 1447 blk / mux1_1 1416 blk） |
| ewasm `non_optimal`（タイムアウト劣後解） | **0 / 0 件** |
| ewasm `outcome` | **全ブロック `optimal`** |
| `shown_optimal=false`（改善あり・最適性未証明） | **1 / 1 件**（両 suite とも `function_18_block_13`、saved 4） |
| checker が false | **0 件** |
| ソルバー時間 | max **2.08s** / **1.92s**、合計 **394s** / **369s**、タイムアウト到達 **0** |
| ewasm が SS より短い（`initial_length` 一致のみ） | **0 件** |
| ewasm が SS より長い（`initial_length` 一致・両方 `optimal`） | **5 / 5 件**（合成 scratch 実装後）— いずれも各 1 命令 |

**合成 scratch local（`tee[-1]`, `--scratch-locals 1`）実装により、旧 10 件のうち 5 件（`41`/`42`/`43`/`61`/`69`）が解消。** 残る 5 件は全て**既存ローカルへの `set;get → tee` 融合**（下記「削減量ギャップの主因」）。詳細は [`0701_ewasm_bug.md`](0701_ewasm_bug.md)。

> **注意（`optimal` ラベルの弱さ）:** これらの `optimal`／`shown_optimal=true` は**誤った最適**である。真の融合解は符号化空間に存在し `validate_solution_ops=true` になる（下記で実証）が、探索が到達できないだけ。`optimal` は「符号化＋規則集合に相対的」であるだけでなく、「長さごとに `forward_valid` が最初に受理したモデルに相対的」でもある。

---

## ベンチマーク概要（split 12 実行）

### ewasm 単体

| | sign_test | mux1_1 |
|--|-----------|--------|
| ブロック数 | **1447** | **1416** |
| 命令数 | 12752 → **12486** | 12292 → **12017** |
| ewasm 削減率 | 266 / 12752 (**2.09%**) | 275 / 12292 (**2.24%**) |
| 改善ブロック数 | **122**（全て `final_solution_tag=astar`） | **105**（全て `astar`） |
| ewasm `no_solution` | **0** | **0** |
| 全ブロック `optimal` | **1447** | **1416** |

`function_24` / `25`: 各 **169 / 179 ブロックすべて `optimal`**。削減合計 **4 / 25 命令**（sign_test・mux1_1 同一）。修正前（split 15）は OriginalUnsat / EncodeFailed で無反応だった。

改善の多い関数（sign_test）: `function_111`（90）、`function_113`（48）、`function_109`（47）、`function_25`（25）、`function_14`（16）。  
改善の多い関数（mux1_1）: `function_117`（67）、`function_111`（54）、`function_113`（43）、`function_25`（25）、`function_109`（21）。

### SuperStack との比較（`initial_length` 一致ブロックのみ）

SuperStack CSV は旧 split 15 実行のため、一致ブロックは全体の **~42%** に限定される。

| | sign_test | mux1_1 |
|--|-----------|--------|
| 比較ブロック数 | **515** | **525** |
| ewasm 削減量（一致 subset） | 13（旧 8） | 17（旧 12） |
| superstack 削減量（一致 subset） | 18 | 22 |
| 削減量ギャップ（SS − ewasm） | **5 命令**（5 blk、旧 10） | **5 命令**（5 blk、旧 10） |
| ewasm が SS より長い | **5**（各 +1 命令、旧 10） | **5**（各 +1 命令、旧 10） |

合成 scratch local 実装で ewasm 削減量は +5 / +5、ギャップ blk は 10→5 に半減した（両 suite で残存 5 blk は同一）。

※ split 15 同条件での旧比較（sign_test ギャップ **909** / mux1_1 **773**）はセグメント境界が異なるため、上記数値と直接比較できない。旧結果の tee 融合・関数別分析は SS を split 12 で再実行後に更新が必要。

---

## 削減量ギャップの主因（split 12・一致ブロック）

残ギャップ: sign_test **5** + mux1_1 **5**（いずれも同一 5 ブロック、各 1 命令）。全て **① ewasm 0 削減・SS のみ 1 命令改善**。

### 残存 5 ブロックは全て「既存ローカルへの `set;get → tee` 融合」

| block | init→SS | 内訳 |
|-------|---------|------|
| `94_block_8` | 9→8 | **純粋な `set 2;get 2→tee 2`**（可換並べ替えも opaque も無し） |
| `94_block_2` | 10→9 | `set 3;get 3→tee 3` ＋ 可換 `i32.add` 並べ替え ＋ opaque load |
| `18_block_12` | 12→11 | `set 8;get 8→tee 8` ＋ 可換 `i32.add` 並べ替え ＋ opaque load |
| `24_block_0_132` | 12→11 | `tee 3` 融合 ＋ opaque `i64.store32` の並べ替え |
| `14_block_0_76` | 12→11 | `tee 4` 融合 ＋ opaque `i64.store32` 並べ替え ＋ 新規 `set 5` |

（`94_block_2` は旧「`tee[-1]`」分類だったが、実際は**既存**ローカル `tee 3` の融合＋可換 add であり scratch では解消されないと判明。）

### 主因: 緩和符号化 ＋ 長さごと単一モデル検証 ＝ 擬似モデルによる遮蔽（**誤った「最適」**）

SAT 符号化は健全性のための**緩和（relaxation）**であり、実行に対応しない**擬似モデル**を許す（だから `forward_valid` で事後再検査している）。降順探索は**各長さで返ってきた 1 モデルだけ**を `forward_valid` で検査し、棄却したら長さを 1 縮めて次へ進む。目標長に擬似モデルが存在すると、**同じ長さに存在する真の（有効な）短縮解を列挙し直さず**、その長さを飛ばして短い長さで UNSAT に達し、**元の長い長さを「最適」と誤報**する。

**実証（`94_block_8`, `18_block_12`）:**

- 真の融合解を手で構成（元列の `set n;get n` を `tee n` に置換）すると `validate_solution_ops = **true**`（＝**符号化空間に存在する有効解**）。
  - `94_block_8`: `local.get 2; i32.const 1; i32.add; i32.const 255; i32.and; local.tee 2; local.get 1; i32.eq`（8 命令、valid）
  - `18_block_12`: 11 命令（並べ替え無しでも valid）
- ところが `solve_sat` は `94_block_8`→**9** / `18_block_12`→**12** を返し `proven_optimal=true`。目標長で返ったモデルは `local.get 1; local.tee 1; …` のような**擬似モデル**（`valid=false`）で、真の 8/11 命令解は列挙されなかった。

改善済み 5 blk（`41`/`42`/`43`/`61`/`69`）は SAT が偶々**有効**モデルを先に返した（scratch slot 由来）ため到達できた、という差でしかない。つまり `set;get→tee` は**表現不能ではなく、探索が単発モデルに阻まれて到達できない**のが本質。

**結論:** 健全性問題は無し。残る SS 優位は全て **1 命令の探索到達ギャップ**で、単一の機構的原因（緩和符号化における擬似モデルの遮蔽）に集約される。対策は「`forward_valid` 棄却時に**そのモデルを禁止節で除外して同じ長さで再解**する（CEGAR 型の反復精緻化）」ことで、上記 5 blk はいずれも解消可能と見込まれる。

### 修正前との対比（参考）

| 指標 | 修正前（split 15） | 修正後（split 12） |
|------|-------------------|-------------------|
| `no_solution`（sign_test / mux1_1） | 290 / 302 | **0 / 0** |
| classify OriginalUnsat | ~200 / ベンチ | **0**（split 15 再診断） |
| classify EncodeFailed | ~104 / ベンチ | **0**（split 15 再診断） |
| ewasm 削減量（全ブロック） | 275 / 282（split 15） | **266 / 275** |
| ギャップ主因 | ① `no_solution` **51%** | ① 擬似モデル遮蔽（既存ローカル tee 融合）**100%**（一致 5 blk） |

---

## 修正の優先度

| 優先度 | 項目 | 状態 | ギャップ寄与（目安） | 内容 |
|--------|------|------|---------------------|------|
| ~~**P1**~~ | ~~**OriginalUnsat** の符号化修正~~ | **完了** | （旧 ~51%） | `inject_trace_edges` |
| ~~**P1**~~ | ~~**EncodeFailed** / CNF 上限~~ | **完了** | （旧 ~28% of no_solution） | `active_local_slots` + 不変ローカル短絡 |
| ~~**P2**~~ | ~~合成 scratch local（`tee[-1]`）~~ | **完了** | 旧 5/10 を解消 | `max_local+1` 以降に Tee スロット追加（`--scratch-locals`） |
| ~~**P1**~~ | ~~**擬似モデル棄却時の同長再解**（CEGAR）~~ | **方針転換** | — | 20万回精緻化でも60秒で収束せず非現実的。**⊤-sink 全域関数化**で源流を締める（2026-07-01 実装） |
| ~~**P1**~~ | **⊤-sink 付き全域テーブル化** | **完了** | 残 5/5 blk（tee 融合） | binop/unop を全域関数化、$\top$ 遮断、CEGAR 撤去。`94_block_8`/`18_block_12` で 1 命令短縮を回帰テスト確認 |
| **P2** | `opaque_inputs_equivalent` 正規化 | 未着手 | 上記の一部（`14`/`18`/`24`/`94_2` の opaque・可換要素） | `i32.add` 等のオペランド順のみ異なる式を同一視 |
| **P3** | segment timeout / 劣後解の棄却 | 要検討 | 現状 **0%** | 修正後 `non_optimal` 0。将来の保険 |

---

## 実装順の推奨（更新）

1. ~~**OriginalUnsat** / **EncodeFailed** / **合成 `tee[-1]`**~~ — 完了
2. ~~**⊤-sink 付き全域テーブル化**~~ — 完了（CEGAR は方針転換で撤去）。`94_block_8`/`18_block_12` で tee 融合 1 命令短縮を `cargo test topsink_totalization_enables_tee_fusion` で確認
3. **`opaque_inputs_equivalent` 正規化** — 残ギャップ（opaque・可換ケース）の補完

---

## 検証

```bash
uv run --project scripts wasm-bench-run --suite wsouper -j 28 --split 12 --segment-timeout 5 --ewasm-solver sat
uv run --project scripts wasm-bench-plot --suite wsouper
uv run --project scripts wasm-bench-classify-gaps --suite wsouper -j 28 --split 12 --segment-timeout 5
cargo test function_2  # function_24/25 witness 回帰
```

確認指標:

- 削減量ギャップ（SS `saved_length` − ewasm `saved_length`、`initial_length` 一致ブロックのみ）
- `no_solution` 件数と classify の OriginalWitnessMissingOp / EncodeFailed 比率
- SS より長いブロック数（健全性反例の有無）

**修正後の確認結果（2026-07-01 ewasm CSV）:**

- `no_solution`: **0**
- 全ブロック `outcome=optimal`: **1447 / 1416**
- `shown_optimal=false`: **1 / 1**（`function_18_block_13`、A* 改善 4 命令・最適性未証明）
- checker false: **0**
- 改善ブロック: sign_test **122** / mux1_1 **105**（いずれも A* 経由、`original` 未変更 1325 / 1311 blk）
- SS 比較（`initial_length` 一致）: 合成 scratch 実装後ギャップ **5 / 5 命令**（旧 10 / 10、残 5 blk は既存ローカル tee 融合）
- ewasm 削減量: sign_test **266**（12752→12486、2.09%）、mux1_1 **275**（12292→12017、2.24%）
- 残 5 blk 検証: `94_block_8`/`18_block_12` で手構成の融合解が `validate_solution_ops=true` だが `solve_sat` は元長を `proven_optimal` と誤報（擬似モデル遮蔽の実証）
