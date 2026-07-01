ewasmのSATは、タイムアウトしないならば、superstackと同じまたはそれよりも短い命令列を見つけるはずである。
ベンチマークの結果を分析して、これに反するケースがないか確認してください。
もし、反例があれば、ewasmのバグの原因を突き止めてください。

# ewasm 健全性・ベンチギャップ分析

更新データ: `bench-results/wsouper/raw/ewasm-{sign_test,mux1_1}.csv`（`--split 15`, segment timeout 10s）  
詳細分析: [`0701_ewasm_bug.md`](0701_ewasm_bug.md)

**設計不変条件:** SAT 失敗時に A* へフォールバックしてはならない。

---

## 健全性チェック

**健全性バグ（誤って長い解を受理）は見つからなかった。**

| 観点 | 結果 |
|------|------|
| ewasm が SS より短い | **301 / 302 件** — いずれも `no_solution`。ewasm は解を返せず SS のみ改善 |
| ewasm が SS より長い（タイムアウトなし） | **113 / 135 件** — `outcome=optimal`。符号化内最適だが SS 解は探索空間外 |
| ewasm が SS より長い（タイムアウト） | **166 / 102 件** — `non_optimal`（10s 打ち切り） |
| ewasm が短い解を見つけたケース | **0 件** |
| checker が false の劣後ケース | **0 件** |

---

## ベンチマーク概要

比較対象: **1251 / 1227** ブロック（`block_id` でマージ）

| | sign_test | mux1_1 |
|--|-----------|--------|
| ewasm 削減率 | 124 / 12752 (**0.97%**) | 151 / 12292 (**1.23%**) |
| superstack 削減率 | 1184 / 12746 (**9.29%**) | 1055 / 12286 (**8.59%**) |
| 削減量ギャップ（SS − ewasm） | **1060 命令** | **904 命令** |
| SS と同じ（`optimized_length` 一致） | 671 | 688 |
| ewasm `no_solution` | 290 | 302 |
| ewasm が SS より長い | 279（+558 命令） | 237（+390 命令） |

---

## 削減量ギャップの主因

ewasm が SS より少なく削減した命令数（`saved_length` の差）を原因別に分解する。

### 3 分類（`saved_length` ベース）

| 原因 | sign_test | mux1_1 | 合計 | 割合 |
|------|-----------|--------|------|------|
| **① `no_solution`**（ewasm は 0 削減、SS のみ改善） | 489 / 1060 | 514 / 904 | **1003** | **51%** |
| **② segment timeout**（`non_optimal` で SS より長い解を返却） | 406 / 1060 | 209 / 904 | **615** | **31%** |
| **③ 符号化の不完全性**（`optimal` だが SS より長い） | 152 / 1060 | 181 / 904 | **333** | **17%** |

**結論:** ギャップの過半数は ewasm が解を一切返せない `no_solution`（①）。次いで 10s セグメントタイムアウトによる劣後解の採用（②）が 3 割。

### ① `no_solution` の内訳（`--classify-sat-gaps` 再診断）

SS が改善したが ewasm が追いつかなかったブロック（sign_test **376** / mux1_1 **377** 件）を診断:

| 診断 | sign_test | mux1_1 | 意味 |
|------|-----------|--------|------|
| **OriginalUnsat** | **199** | **200** | 符号化が元プログラムすら witness できない |
| **EncodeFailed** | **104** | **104** | CNF 生成失敗（句数上限等。`n_ops≈125`, `r=38` が集中） |
| **Solved + proven_optimal**（SS より長い） | **63** | **63** | SAT は動いたが SS 解は探索空間外 |
| **Solved + timed_out** | **9** | **9** | 再診断時の SAT タイムアウト |

`no_solution` 寄与の **約 3 割は EncodeFailed**、**過半数は OriginalUnsat** が支配的。いずれも SAT がそもそも探索を開始できない／元トレースを満たせない系。

### 関数別の集中

ギャップの **65〜76%** が `function_25` / `24` / `14` / `13` の 4 関数に集中:

| 関数 | sign_test ギャップ | 主因 |
|------|-------------------|------|
| `function_25` | 249（135 ブロック） | `no_solution` **211**、timeout 23 |
| `function_24` | 180（126 ブロック） | `no_solution` **180**（全件） |
| `function_14` | 161（76 ブロック） | 符号化不完全 **62**、no_solution 73、timeout 26 |
| `function_111` | 190（53 ブロック） | timeout **188**（call 引数畳み込み系） |

`function_24` / `25` は 64bit 乗算加算チェーン（`i64.mul` / `i64.add` / `i64.shr_u`）の 15 命令セグメント。SS は定数畳み込み・`tee` 融合で 1〜3 命令削減するが、ewasm は OriginalUnsat / EncodeFailed で無反応。

`function_111` / `109` / `113` は call 前後の引数畳み込み。10s タイムアウトでも SS より +6〜+8 命令長い解を返す（② の典型）。

### ③ 符号化不完全性のパターン（SS 解 `solution_found` ベース）

| 原因 | sign_test | mux1_1 |
|------|-----------|--------|
| SS が `tee` で融合・並べ替え | 193 | 203 |
| SS が `local.tee[-1]` を使用 | 21 | 14 |
| その他 | 65 | 20 |

`optimal` 劣後に限ると tee 融合系が **97/113**（sign_test）、**122/135**（mux1_1）を占める。

---

## 修正の優先度

| 優先度 | 項目 | ギャップ寄与 | 内容 |
|--------|------|-------------|------|
| **P1** | **OriginalUnsat** の符号化修正 | ① の **~53%**（~200 件/ベンチ） | 64bit 演算チェーンで元トレースが witness 不可。`function_24/25` が中心 |
| **P1** | **EncodeFailed** / CNF 上限 | ① の **~28%**（~104 件/ベンチ） | `n_ops≈125`, `r=38` セグメントで CNF 膨張 |
| **P1** | segment timeout / 劣後解の棄却 | ② **31%**（615 命令） | 10s 打ち切りで SS より長い解を返す。`function_111` 系が典型 |
| **P1** | `opaque_inputs_equivalent` 正規化 | ③ の tee 融合系 | `i32.add` 等のオペランド順のみ異なる式を同一視 |
| **P2** | 合成 scratch local（`tee[-1]`） | ③ の **21/14** 件 | `max_local+1` 以降に Tee スロット追加 |
| **P3** | call 引数スケジュール | ② の `function_109/111/113` | call 前後のスタック畳み込み・並べ替え |

---

## 実装順の推奨

1. **OriginalUnsat** — `function_24/25` の 64bit チェーン（ギャップ最大、全 no_solution）
2. **EncodeFailed** — 同セグメントの CNF 上限
3. **segment timeout 方針** — 劣後解を返さない／timeout 時は元プログラムを維持
4. **チェッカー正規化 + 合成 local** — ③ の残り

---

## 検証

```bash
uv run --project scripts wasm-bench-run --suite wsouper -j 20 --split 15 --segment-timeout 10 --ewasm-solver sat
uv run --project scripts wasm-bench-plot --suite wsouper
uv run --project scripts wasm-bench-classify-gaps --suite wsouper -j 20 --split 15 --segment-timeout 10
```

確認指標:

- 削減量ギャップ（SS `saved_length` − ewasm `saved_length`）
- `no_solution` 件数と classify の OriginalUnsat / EncodeFailed 比率
- SS より長いブロック数
