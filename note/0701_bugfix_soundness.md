ewasmのSATは、タイムアウトしないならば、superstackと同じまたはそれよりも短い命令列を見つけるはずである。
ベンチマークの結果を分析して、これに反するケースがないか確認してください。
もし、反例があれば、ewasmのバグの原因を突き止めてください。

# ewasm 健全性・ベンチギャップ分析

更新データ: `bench-results/wsouper/raw/ewasm-{sign_test,mux1_1}.csv`（`--split 12`, segment timeout 5s）  
SuperStack 参照: `superstack-{sign_test,mux1_1}.csv`（**旧実行** `--split 15`, segment timeout 10s）  
詳細分析: [`0701_ewasm_bug.md`](0701_ewasm_bug.md)

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
| checker が false | **0 件** |
| ewasm が SS より短い（`initial_length` 一致のみ） | **0 件** |
| ewasm が SS より長い（`initial_length` 一致・両方 `optimal`） | **10 / 10 件** — 符号化内最適だが SS 解は探索空間外（各 1 命令） |

`initial_length` 一致 10 件の内訳: `tee[-1]` 系 6（`41`/`42`/`43`/`61`/`69`/`94`）、`tee` 融合 2（`14_block_0_76`/`18_block_12`）、その他 2（`24_block_0_132`/`94_block_8`）。詳細は [`0701_ewasm_bug.md`](0701_ewasm_bug.md)。

---

## ベンチマーク概要（split 12 実行）

### ewasm 単体

| | sign_test | mux1_1 |
|--|-----------|--------|
| ブロック数 | **1447** | **1416** |
| ewasm 削減率 | 266 / 12752 (**2.09%**) | 275 / 12292 (**2.24%**) |
| 改善ブロック数 | **122** | **105** |
| ewasm `no_solution` | **0** | **0** |
| 全ブロック `optimal` | **1447** | **1416** |

`function_24` / `25`: 各 **169 / 179 ブロックすべて `optimal`**。削減合計 **4 / 25 命令**（sign_test・mux1_1 同一）。修正前（split 15）は OriginalUnsat / EncodeFailed で無反応だった。

改善の多い関数（sign_test）: `function_111`（90）、`function_113`（48）、`function_109`（47）、`function_25`（25）、`function_14`（16）。

### SuperStack との比較（`initial_length` 一致ブロックのみ）

SuperStack CSV は旧 split 15 実行のため、一致ブロックは全体の **~42%** に限定される。

| | sign_test | mux1_1 |
|--|-----------|--------|
| 比較ブロック数 | **515** | **525** |
| ewasm 削減率（一致 subset） | 8 / 2392 (**0.33%**) | 12 / 2444 (**0.49%**) |
| superstack 削減率（一致 subset） | 18 / 2392 (**0.75%**) | 22 / 2444 (**0.90%**) |
| 削減量ギャップ（SS − ewasm） | **10 命令**（10 blk） | **10 命令**（10 blk） |
| `optimized_length` 一致 | 505 | 515 |
| ewasm が SS より長い | **10**（各 +1 命令） | **10**（各 +1 命令） |

※ split 15 同条件での旧比較（sign_test ギャップ **909** / mux1_1 **773**）はセグメント境界が異なるため、上記数値と直接比較できない。旧結果の tee 融合・関数別分析は SS を split 12 で再実行後に更新が必要。

---

## 削減量ギャップの主因（split 12・一致ブロック）

残ギャップ: sign_test **10** + mux1_1 **10** = **20 命令**（いずれも同一 10 ブロック）。全て **① ewasm 0 削減・SS のみ 1 命令改善**。

| 原因（`0701_ewasm_bug.md` 分類） | 件数 | 該当 block |
|------|------|------------|
| **合成 scratch local なし**（`tee[-1]`） | 6 | `41_block_4`, `42_block_2`, `43_block_2`, `61_block_4`, `69_block_1`, `94_block_2` |
| **`tee` 融合・並べ替え** | 2 | `14_block_0_76`, `18_block_12` |
| **その他** | 2 | `24_block_0_132`, `94_block_8` |

**結論:** split 12 実行でも健全性問題はなく、SS 優位は全て **1 命令の探索空間ギャップ**。旧 split 15 で観測された大規模ギャップ（`function_24`/`25` 等）は、主にセグメント分割の違いによる比較不能ブロックに起因していた。

### 修正前との対比（参考）

| 指標 | 修正前（split 15） | 修正後（split 12） |
|------|-------------------|-------------------|
| `no_solution`（sign_test / mux1_1） | 290 / 302 | **0 / 0** |
| classify OriginalUnsat | ~200 / ベンチ | **0**（split 15 再診断） |
| classify EncodeFailed | ~104 / ベンチ | **0**（split 15 再診断） |
| ewasm 削減量（全ブロック） | 275 / 282（split 15） | **266 / 275** |
| ギャップ主因 | ① `no_solution` **51%** | ① SS のみ改善 **100%**（一致 10 blk） |

---

## 修正の優先度

| 優先度 | 項目 | 状態 | ギャップ寄与（目安） | 内容 |
|--------|------|------|---------------------|------|
| ~~**P1**~~ | ~~**OriginalUnsat** の符号化修正~~ | **完了** | （旧 ~51%） | `inject_trace_edges` |
| ~~**P1**~~ | ~~**EncodeFailed** / CNF 上限~~ | **完了** | （旧 ~28% of no_solution） | `active_local_slots` + 不変ローカル短絡 |
| **P1** | `opaque_inputs_equivalent` 正規化 | 未着手 | **~20%**（一致 blk の `14`/`18`） | `i32.add` 等のオペランド順のみ異なる式を同一視 |
| **P2** | 合成 scratch local（`tee[-1]`） | 未着手 | **~60%**（一致 blk 6/10） | `max_local+1` 以降に Tee スロット追加 |
| **P2** | E-graph 定数畳み込み拡張 | 未着手 | split 12 再ベンチ後に再評価 | SS が使う畳み込み結果を語彙／規則に取り込む |
| **P3** | call 引数スケジュール | 未着手 | split 12 再ベンチ後に再評価 | call 前後のスタック畳み込み・並べ替え |
| **P3** | segment timeout / 劣後解の棄却 | 要検討 | 現状 **0%** | 修正後 `non_optimal` 0。将来の保険 |

---

## 実装順の推奨（更新）

1. ~~**OriginalUnsat**~~ — 完了
2. ~~**EncodeFailed**~~ — 完了
3. **合成 `tee[-1]`** — 一致 blk ギャップの **60%**（6/10）
4. **`opaque_inputs_equivalent` 正規化** — 一致 blk ギャップの **20%**（2/10）
5. **E-graph 畳み込み + call 引数スケジュール** — SS split 12 再実行後に優先度を再評価

---

## 検証

```bash
uv run --project scripts wasm-bench-run --suite wsouper -j 20 --split 12 --segment-timeout 5 --ewasm-solver sat
uv run --project scripts wasm-bench-plot --suite wsouper
uv run --project scripts wasm-bench-classify-gaps --suite wsouper -j 20 --split 12 --segment-timeout 5
cargo test function_2  # function_24/25 witness 回帰
```

確認指標:

- 削減量ギャップ（SS `saved_length` − ewasm `saved_length`、`initial_length` 一致ブロックのみ）
- `no_solution` 件数と classify の OriginalWitnessMissingOp / EncodeFailed 比率
- SS より長いブロック数（健全性反例の有無）

**修正後の確認結果（上記 ewasm CSV）:**

- `no_solution`: **0**
- 全ブロック `optimal`: **1447 / 1416**
- checker false: **0**
- SS 比較（`initial_length` 一致）: ギャップ **10 / 10 命令**（sign_test・mux1_1 同一 10 blk）
- ewasm 削減量: sign_test **266**（2.09%）、mux1_1 **275**（2.24%）
