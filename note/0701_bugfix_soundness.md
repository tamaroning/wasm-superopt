ewasmのSATは、タイムアウトしないならば、superstackと同じまたはそれよりも短い命令列を見つけるはずである。
ベンチマークの結果を分析して、これに反するケースがないか確認してください。
もし、反例があれば、ewasmのバグの原因を突き止めてください。

# ewasm 健全性・ベンチギャップ修正の優先度

更新データ: `bench-results/wsouper/raw/ewasm-{sign_test,mux1_1}.csv`（`--split 60`, segment timeout 5s）  
詳細分析: [`0701_ewasm_bug.md`](0701_ewasm_bug.md)

**設計不変条件:** SAT 失敗時に A* へフォールバックしてはならない。

---

## ベンチマーク概要（更新後）

比較対象: 759 / 760 ブロック（`block_id` でマージ）

| | sign_test | mux1_1 |
|--|-----------|--------|
| ewasm 削減率 | 20 / 12752 (**0.16%**) | 22 / 12294 (**0.18%**) |
| superstack 削減率 | 1363 (**10.69%**) | 1244 (**10.12%**) |
| **SS と同じ**（`optimized_length` 一致） | **559** | **569** |
| **SS と同じ**（`saved_length` 一致） | **572** | **581** |
| ewasm の方が短い（`optimized_length`） | 181 | 172 |
| ewasm の方が長い（`optimized_length`） | **19**（+36 命令） | **19**（+36 命令） |
| SS の方が多く削減（`saved_length`） | **168** | **162** |
| ewasm の方が多く削減（`saved_length`） | 19 | 17 |
| ewasm `no_solution` | **181** | **172** |

`optimized_length` 一致 559/569 件のうち、ewasm outcome は `optimal` 551/561・`non_optimal` 8/8（いずれも SS と同長でタイムアウトなし）。

両ベンチで **劣後 19 ブロック（`optimized_length` で SS より長い）は同一集合**（`function_106_block_7` の +7 を含む）。

---

## ギャップの内訳

### 1. `no_solution`（支配的）

| | sign_test | mux1_1 |
|--|-----------|--------|
| 件数 | 181 | 172 |
| うち SS が改善したブロック | 149 | 143 |
| SS 削減命令数（ewasm は 0） | **1307** | **1186** |
| 全体ギャップに占める割合 | **≈97%** | **≈97%** |

60 命令チャンクが中心（sign_test: 137 件で SS が 1072 命令削減、mux1_1: 128 件で 930 命令削減）。

`--classify-sat-gaps` 診断（timeout / `non_optimal` を除く）:

| 診断 | sign_test | mux1_1 | 意味 |
|------|-----------|--------|------|
| **EncodeFailed** | **98** | **92** | CNF 生成失敗（句数上限・encode タイムアウト等） |
| **VocabBuildFailed** | **41** | **41** | 語彙 `|V| > MAX_VOCAB(64)` 等で構築失敗 |
| **OriginalUnsat** | **10** | **10** | 符号化が元プログラムを witness できない |
| **Solved + proven_optimal**（SSより長い） | **14** | **14** | 符号化内では最適だが SS 解は探索空間外 |
| TooLong | **0** | **0** | — |

### 2. SAT は動いたが SS より長い（19 件）

| ewasm outcome | 件数 | 代表 block |
|---------------|------|------------|
| `optimal`（符号化内最適） | **14** | `41_block_4/5`, `34_block_2`, `17_block_0/3`, `18_block_22` 等 |
| `non_optimal`（5s timeout） | **5** | `106_block_7`(+7), `58_block_9`, `16_block_0_1`, `19_block_18`, `96_block_8` |

SS 解のパターン（19 件共通）:

| 原因 | 件数 | 該当 |
|------|------|------|
| SS が `local.tee[-1]` を使用 | **10** | `41_block_4/5`, `42/43_block_2`, `61_block_4`, `69_block_1`, `17_block_0/3`, `58_block_9`, `106_block_7` |
| SS が `tee`（実在 local）で融合・並べ替え | **8** | `34_block_2`, `94_block_2/8`, `32_block_9`, `14_block_0_19`, `19_block_18`, `96_block_8` 等 |
| スタック直結（set/get 迂回不要） | **1** | `18_block_22` |

---

## 修正の優先度

| 優先度 | 項目 | 対象件数 | 内容 |
|--------|------|----------|------|
| **P1** | `EncodeFailed` / CNF 上限 | classify **90〜98** / no_solution の大半 | 60 命令チャンクの CNF が `MAX_CNF_CLAUSES` 等で失敗。緩和・段階 encode・分割の見直し |
| **P1** | `VocabBuildFailed` | classify **41** × 2 ベンチ | `MAX_VOCAB=64` 超過。語彙 pruning または上限引き上げ |
| **P1** | 合成 scratch local（`tee[-1]` 相当） | 劣後 **10** / `optimal` **8** | `max_local+1` 以降に Tee スロット追加。fin では `★` 扱い |
| **P1** | `opaque_inputs_equivalent` の可換演算正規化 | 劣後 **6〜8**（tee 融合系） | `i32.add` 等のオペランド順のみ異なる式を同一視 |
| **P2** | `OriginalUnsat` の符号化修正 | classify **10** × 2 ベンチ | 例: `function_40_block_0`（3 命令）で witness 不可 |
| **P3** | call 前後のスタック保持スケジュール | 劣後の一部 | `tee[5]` を call 後へ移す等、SS 解固有の並べ替え |
| **P3** | スタック直結 | **1**（`18_block_22`） | `i64.load` → `i64.div_u` の local 迂回除去 |
| **P4** | segment timeout 延長 | **5**（`non_optimal`） | 5s 打ち切り。`106_block_7` の +7 が最大 |
| **P4** | `optimal` ラベルの修正 | 表示のみ | 符号化内最適とグローバル最適を区別（`statistics.rs`） |

---

## 実装順の推奨

1. **P1 EncodeFailed + VocabBuildFailed** — `no_solution` 181/172 件の本体（60 命令チャンク）
2. **P1 合成 local** — `41/42/43` 系・`106_block_7` など
3. **P1 チェッカー正規化** — SAT が見つけても棄却される経路
4. **P2 OriginalUnsat** — 短ブロックの即失敗
5. **P3–P4** — 残件・UX

---

## 検証

```bash
uv run --project scripts wasm-bench-run --suite wsouper -j 20 --split 60 --segment-timeout 5
uv run --project scripts wasm-bench-plot --suite wsouper
cargo run --release -- benchmarks/wsouper/sign_test.wasm --split 60 --classify-sat-gaps bench-results/wsouper/combined_blocks.csv
```

確認指標:

- `no_solution` 件数（目標: EncodeFailed / VocabBuildFailed の減少）
- SS より長いブロック数（timeout 除き 0 に近づける）
- `reduction_by_benchmark.png` の削減率
