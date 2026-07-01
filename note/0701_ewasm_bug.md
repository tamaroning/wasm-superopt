ewasmはtimeoutしない限り、superstackと同じかそれよりも短いケースを見つけるはずである。ewasmがssに負けるケースの原因分析をしてください。

## 結論

12件は**健全性バグ（間違った長い解を受理）ではなく、探索空間の不完全性**です。ewasm の SAT は「これより短い解は存在しない」と判定して `outcome=optimal` を付けていますが、SuperStack が見つけた短い解は ewasm の符号化では**表現できないか、制約で刈られている**ためです。

---

## 12件の分類

| 原因 | 件数 | 該当 block |
|------|------|------------|
| **合成用 scratch local がない** (`local.tee[-1]`) | 6 | `41_block_4/5`, `42_block_2`, `43_block_2`, `61_block_4`, `69_block_1`, `58_block_9` |
| **tee 融合 + 命令並べ替え**（実在 local、チェッカー問題あり） | 4 | `14_block_0_19`, `34_block_2`, `19_block_18`, `96_block_8` |
| **スタック直結（set/get 迂回）** | 1 | `18_block_22` |
| **タイムアウト（5s）** | 4 | `18_block_22`, `58_block_9`, `96_block_8`, `19_block_18` |

※ タイムアウト4件は上と重複あり。

---

## 主因1: 合成 scratch local の欠如（6件）

SuperStack の短い解の多くは **`local.tee[local_index(-1)]`** を使っています。`-1` は WASM に元々ない**最適化用の仮想ローカル**です。

SuperStack 側（`greedy/algorithm.py`）:

```186:204:/home/tamaron/work/superstack/wasm/greedy/algorithm.py
    def available_local(self) -> int:
        ...
        # Return -1 if there is no available local to store the value
        return -1

    def new_local(self) -> int:
        """
        Introduces a null local to store an element
        """
        self.locals.append('')
        ...
```

ewasm 側は `0..=max_local` の**実在ローカルだけ**に `Tee` を割り当てます:

```586:589:/home/tamaron/work/ewasm/src/optimize/sat.rs
    for slot in 0..r as u32 {
        ops.push(SatOp::Get(slot));
        ops.push(SatOp::Set(slot));
        ops.push(SatOp::Tee(slot));
```

例: `function_41_block_4`（`Fr_toMontgomery`）は **param 1個・local 0個** だけです。

- **SS (9命令)**: `local.get[0] i32.const 8 i32.add local.tee[-1] local.get[-1] ...`
- **ewasm (10命令)**: 元プログラムのまま（`local.get[0]` を2回 + `i32.add` を2回）

`Tee(0)` は引数 `pR` を上書きするため使えず、CSE 用の scratch がなく **9命令解が探索空間に存在しない** → SAT は UNSAT と判定し「optimal」と報告します。

---

## 主因2: tee 融合 + 命令並べ替え（4件）— `local.tee` は合成されている

**訂正:** `local.tee` は SAT アルファベットに含まれており、合成されていないわけではない。

```586:589:/home/tamaron/work/ewasm/src/optimize/sat.rs
    for slot in 0..r as u32 {
        ops.push(SatOp::Get(slot));
        ops.push(SatOp::Set(slot));
        ops.push(SatOp::Tee(slot));
```

`SatOp::Tee` の意味論も `encode` に実装済み。問題は「tee がない」ことではない。

### SS 解は単純な set→tee 置換ではない

`function_34_block_2` の例:

| | 流れ |
|--|------|
| 元 (15) | `… sub → set[4] → get[1] → get[4] → add → load8 → **set[5]** → call → **get[5]** → ge_u` |
| SS (13) | `… sub → **tee[4]** → get[1] → add → load8 → call → **tee[5]** → ge_u` |

- `tee[4]`: set+get の融合
- `tee[5]`: **call の前後で spill タイミングを変更**（set[5] を call 後の tee[5] に移動）
- つまり **スタック上の値を call を挟んで保持するスケジューリング**が必要

`function_14_block_0_19`・`function_19_block_18` も store の移動や local.set 列の並べ替えを含む。

### なぜ ewasm がその解を見つけられないか

`function_34_block_2` で診断した結果:

#### (A) SAT は長さ 14 で UNSAT（`proven_optimal: true`）

現符号化では「15 より短い解は存在しない」と証明される。tee がアルファベットにあっても、**そのスケジュールを満たす短い命令列が CNF 上表現できていない**。

#### (B) SS 形の 13 命令列を手で組んでも `opaque_inputs_equivalent` が落ちる

| 変形 | `validate_ops` | `opaque_inputs_equivalent` | `solution_valid` |
|------|----------------|---------------------------|------------------|
| tee[4] のみ (14命令) | ✓ | **✗** | ✗ |
| SS 形 (13命令) | ✓ | **✗** | ✗ |

失敗箇所は `i32.load8_u`（opaque id=0）のオペランド比較:

```
got:  (i32.add (i32.sub ?L4 1) ?L1)
want: (i32.add ?L1 (i32.sub ?L4 1))
```

`tee[4]` によりスタック経路が変わり、**可換な `i32.add` のオペランド順だけが違う**式になる。実行上は同値だが、`canon.values_equivalent` が同一とみなさず、チェッカーが解を拒否する。

```146:151:/home/tamaron/work/ewasm/src/optimize/search.rs
                for (got, want) in actual.input_symbols.iter().zip(exp.input_symbols.iter()) {
                    let got_expr = parse_value_expr(got);
                    let want_expr = parse_value_expr(want);
                    if !canon.values_equivalent(&got_expr, &want_expr) {
                        return false;
```

`solve_sat` は SAT で見つけた候補を `forward_valid`（= 上記チェック含む）で弾くため、**正しい tee スケジュールがあっても採用されない**。

### 主因2のまとめ

| 以前の説明 | 実際 |
|-----------|------|
| tee が合成されていない | **誤り**。`SatOp::Tee` はある |
| fin / 依存 / 語彙のせい | 部分的要因だが本質ではない |
| **本質** | (A) SS 解は tee 融合 + **命令並べ替え**のセット (B) **`opaque_inputs_equivalent` が可換 add のオペランド順を同一視しない** (C) その結果 SAT も短い解に到達できず UNSAT と判定 |

---

## 主因3: 可換演算まわりのスケジュール（一部）

`function_69_block_1` などでは SS が次の並びを使う:

```
i32.const[8] local.get[0] i32.add   // SS
local.get[0] i32.const[8] i32.add   // ewasm（元のまま）
```

`i32.add` は可換なので意味は同じ。以前は symmetry breaking（`sat.rs` §5.6）が逆順スケジュールを禁止していた可能性があったが、**symmetry breaking は削除済み**（`0701_symmetry_breaking.md` に基づく実装を一旦除去）。

残る問題は主因1の `tee(-1)` と、主因2の **`opaque_inputs_equivalent` における可換演算のオペランド順**の組み合わせ。

---

## 副次: `optimal` ラベルの誤り

`statistics.rs` の `classify_outcome` は、改善なし・タイムアウトなしなら常に `optimal` になります:

```148:161:/home/tamaron/work/ewasm/src/optimize/statistics.rs
    if improved && checker {
        return ("optimal".to_string(), true, true, "astar".to_string());
    }

    (
        "optimal".to_string(),
        true,
        true,
        ...
    )
```

SAT の降下探索が L-1 で UNSAT になった時点で「証明完了」とみなしますが、それは**現在の符号化に対する相対的最適性**に過ぎず、SuperStack より長くても `optimal` と出ます。

---

## 修正の方向性

1. **SuperStack 同様に合成 scratch local を導入**（`Tee` 用スロットを `max_local+1` 以降に追加し、fin では `★` 扱い）— 主因1（6件）
2. **`opaque_inputs_equivalent` で可換演算のオペランド順を正規化して比較**（e-graph に add の交換律が無ければルール追加）— 主因2の本質
3. call 前後のスタック保持が必要なケース向けの符号化・スケジュール表現の見直し — 主因2の補助
4. **`optimal` 表示の修正**（符号化の完全性を仮定しないラベルに変更）

優先度が高いのは **1（合成 local）** と **2（チェッカー）**。6件が `tee(-1)` に依存し、`41/42/43` 系は関数に local がほぼ無い。4件の主因2は tee 自体はあるが、チェッカーが SS 同等の解を拒否している。