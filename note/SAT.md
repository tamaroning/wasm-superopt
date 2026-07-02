# 直線 Wasm 命令列の最短化:Pure-SAT 帰着

**目的:** 直線的 WebAssembly コードの初期状態 $\mathit{init}$、最終状態 $\mathit{fin}$、およびオリジナルの命令列(長さ $L_{\mathrm{orig}}$)が与えられたとき、$\mathit{init}$ から $\mathit{fin}$ へ遷移する命令数最小の命令列を、命題充足性判定 (SAT) ソルバへの反復呼び出しのみで合成する手法を定める。後方探索や MaxSAT を用いず、$L_{\mathrm{orig}}$ から 1 ずつ減らす **降順 Pure-SAT 反復** で命令長を最小化する。タイムアウト時もそれまでに発見された最短解を出力できる。

---

## A. 背景と動機

**スーパー最適化における位相順序問題**

算術演算とデータフロー（スタック／ローカル変数）を別フェーズで最適化すると、位相順序問題により本質的に準最適解に陥る。

* **SuperStack (PLDI '24):** 前方記号実行で算術形式を早期に固定し、その後 SAT/MaxSAT でスタック／ローカルを最適化する。
* *欠点:* 算術の選択とレジスタ・スピルのトレードオフを大域的に評価できない。

* **Ruler (OOPSLA '21):** ハッシュコンシングにより書き換え規則を効率的に生成するが、算術等価性のみに焦点を当て、状態を伴うスタック操作は扱わない。

**本手法の目標:** ループ・分岐のない（直線的な）Wasm プログラムについて、算術演算とデータフローを同時に最適化し、絶対的最適性を保証する。

---

## B. 二段階スーパー最適化アーキテクチャ

形式的正しさと命令スケジューリングの最適性を両立するため、アーキテクチャは厳密に二段階に分離する。

### フェーズ 1: 書き換え規則の導出

Wasm 命令の意味を形式的に符号化し、算術演算に限定した書き換え規則の組 $(LHS \to RHS)$ を導出する。

* **設計意図:** 算術等価性のみを扱い、規則の健全性を探索前に保証する。状態を伴うデータフローやスタック操作はフェーズ 2 に委ねる。

### フェーズ 2: 最短命令列探索（A\*）

フェーズ 1 で得た規則を用い、最終残余目標から初期状態へ向かう後方最短経路探索を行う。

* **設計意図:** 算術の選択、スピル、スケジューリング、副作用の順序づけを単一の状態空間グラフに統合する。

---

## C. 問題定義（フェーズ 2）

**入力:** 直線的 Wasm プログラムにおける初期状態と最終状態の組。

* **状態:** `(スタック, ローカル)`
* **スタック:** 下から積まれた値の列。
* **ローカル:** スロット番号から値（または「不要」）への写像。

> **実行例:**
> `init = (stack=[], local={0: L})`
> `fin  = (stack=[(L≪1)≪2, L≪1], local={0: L≪1})`
>
> ここで `L≪1` は `L` を 1 ビット左シフトした値（すなわち `L×2`）を表す。

**出力:** `init` を `fin` に変換する、厳密に最短の Wasm 命令列。

---

## 1. 設定

### 1.1 入力

- 初期状態 $\mathit{init} = (S_0, M_0)$
- 最終状態 $\mathit{fin} = (S_*, M_*)$
- オリジナル命令列 $\sigma_{\mathrm{orig}}$(長さ $L_{\mathrm{orig}}$):$\mathit{init}$ から $\mathit{fin}$ への遷移を実現する既知の命令列

ここで:

- $S_0, S_*$: 値の有限列(スタック内容)
- $M_0, M_*$: スロット番号から値 $\cup \{\star\}$ への写像($\star$ は don't-care、つまりそのスロットの値は最終的に問わない)

$\sigma_{\mathrm{orig}}$ は素朴なコンパイラ出力など、最適とは限らないが正しい命令列であればよい。これが降順反復の初期上界と「自明な解」を提供する。

### 1.2 前提

直線(分岐・ループなし)コードを扱う。算術書き換え規則 $\equiv_R$(例: $x \cdot 2^n \equiv x \ll n$, $\mathrm{mul}$/$\mathrm{shl}$ の同値性、結合律、可換律など)が外部から与えられているとする。これは健全性が事前に保証された有限規則集合とする。

副作用（メモリ・グローバル・関数呼び出し・その他の非 i32 命令）も SuperStack (§2.4) の流儀で**非解釈命令**として同じエンコーディングに統合する（§11）。本文 §2–§9 はまず副作用なしの場合を述べ、§11 でその拡張を与える。

### 1.3 パラメータ

| 記号 | 意味 |
| --- | --- |
| $L_{\mathrm{orig}}$ | オリジナル命令列の長さ(エンコーディング上界、固定) |
| $H$ | スタック高さの上界 |
| $R$ | 使用可能ローカルスロット数 |
| $k_{\mathrm{sat}}$ | 等価類飽和の反復回数 |

$R$ は $\mathit{init}$, $\mathit{fin}$, $\sigma_{\mathrm{orig}}$ に現れるスロット番号の最大値 + 1 で初期化する。$H$ は $\sigma_{\mathrm{orig}}$ の実行中の最大スタック高さから開始する。本手法では命令長の上界 $L$ を $L_{\mathrm{orig}}$ に固定するため、別途上界探索は不要。

### 1.4 表記の固定

- スタックは **top-to-bottom 表記**:$\mathrm{stack}[0]$ が天端、$\mathrm{stack}[j]$ ($j > 0$) が深い側
- 二項演算 $\oplus$ の引数順は WebAssembly 慣習: $\mathrm{stack}[1]$ が第 1 引数、$\mathrm{stack}[0]$ が第 2 引数、結果は新しい天端

例: `i32.shl` は $\mathrm{stack}[1]$ を被シフト値、$\mathrm{stack}[0]$ をシフト量とし、$\mathrm{stack}[1] \ll \mathrm{stack}[0]$ を計算して天端に積む。

---

## 2. 値の有限語彙 $V$ の構築

SAT 帰着の前に、エンコーディングで使う値の有限集合 $V$ を確定する。

### 2.1 飽和手続き

```
V ← ∅
1. (起点) init.stack の全要素、init.local の非★要素を V に追加
2. (起点) fin.stack の全要素、fin.local の非★要素を V に追加
3. (部分式) V に含まれる各値について、その全ての部分式を V に追加
4. (オリジナル) オリジナル命令列を init から記号実行し、各ステップで
   出現する全ての中間値(スタックトップ・ローカル内容)を V に追加
   - 記号実行中、引数が concrete integer literal の pure op は deterministic に
     constant fold してよい（例: `i32.const 7; i32.const 40; i32.mul` → `280`）
   - これは `V × V` の定数閉包ではなく、オリジナルトレース上で実際に現れる
     seed を正規化する処理である
5. (等価表現) V に含まれる各値 v について、≡_R で v と同値な全ての
   表現を k_sat 回まで再帰的に展開し、生じた新たな部分式も V に追加
6. (定数) 関連する小定数(0, 1, 2, -1 など)と、ステップ 4 の記号実行で
   concrete fold された定数も V に追加
7. (特殊シンボル) ⊥, ★ を V に追加
```

ステップ 4 はオリジナル命令列が SAT エンコーディング上で必ず実行可能(初回 SAT 呼び出しが必ず SAT を返す)であることを保証する。降順反復方式(§6)の前提条件となる。

> **実装メモ:** constant folding は rewrite rule や `V × V` の online closure としてではなく、記号実行 seed の生成時に行う。全定数ペアの閉包を `V` や演算テーブルへ追加すると、語彙・CNF が膨らみ timeout が増えるため避ける。対象はまず trap しない整数演算（`add/sub/mul/and/or/xor/shl/shr`）に限定する。

> **注意（§7.5）:** ステップ 4–5 は**オリジナルトレースの閉包**を主とする。tee 融合などでオリジナルに無い中間スタックラベルが必要になる短縮は、$k_{\mathrm{sat}}$ の増加だけでは補えないことがある。§10・§11.8 の語彙拡張を参照。

### 2.2 正規代表 $c(\cdot)$

$\equiv_R$ による同値関係で $V$ を分割し、各同値類から代表 $c(v)$ を 1 つ選ぶ。実装上は E グラフ(例: `egg`)を用いるのが標準的。

以下、$V$ の要素は全て同値類代表とみなす。同値な複数の表現は 1 つの $v \in V$ に同定される。

### 2.3 演算結果テーブル

各単項演算 $\circ$ と $v \in V$ について
$$T_\circ(v) \;=\; c(\circ(v)) \quad \text{(}V \text{ の外なら未定義)}$$

各二項演算 $\oplus$ と $(v_1, v_2) \in V \times V$ について
$$T_\oplus(v_1, v_2) \;=\; c(\oplus(v_1, v_2)) \quad \text{(}V \text{ の外なら未定義)}$$

これらは SAT 呼び出し前に一度だけ計算しておく定数テーブル。$T$ が未定義の入力ペアは、対応する SAT 節を生成しない(すなわち、その遷移は禁止される)。

**算術等価性の吸収:** たとえば `mul` と `shl` で同じ結果に到達する場合、$T_{\mathrm{mul}}(L \ll 1, 4) = T_{\mathrm{shl}}(L \ll 1, 2)$ となる。SAT 探索はどちらの命令を選んでも同じ語彙要素に到達するため、§7 の「算術分岐」の効果が自動的に得られる。

### 2.3.1 可換二項演算の遷移表双方向化

$\equiv_R$ に可換律（例: $(a \oplus b) \equiv_R (b \oplus a)$）が含まれていても、**値の同値性**と**スタック上の実行可能なオペランド順**は別問題である。

- **$\equiv_R$ の役割:** 式どうしが同じ正規代表 $c(\cdot)$ に落ちることを保証する。$V$ への挿入は代表 $c(v)$ で dedup されるため、可換で同値な**逆向き構文**（$(b \oplus a)$ と $(a \oplus b)$）は、$V$ 内に別エントリとして残らないことが多い。
- **$T_\oplus$ の構築:** $V$ に残った代表式の**構文上の子順**から $(v_1, v_0) \mapsto v_{\mathrm{res}}$ を抽出する。したがって、トレース上で一度しか現れない向きだけが edge になりうる。
- **問題:** `tee` 融合や pure op / local op の並べ替え後、スタック天端の物理配置は $\mathrm{stack}[1]=v_a$, $\mathrm{stack}[0]=v_b$ だが、$T$ に載っているのは $(v_b, v_a)$ のみ、という不一致が起きる。語彙 $V$ やスタック高さ $H$ は足りていても、**遷移表の向き**だけが探索空間外になる。

**対策（Wasm 意味論ベース）:** 可換と分かっている二項演算（整数・浮動小数の `add`, `mul`, `and`, `or`, `xor`）について、$T_\oplus$ に $(v_1, v_0) \mapsto r$ があるなら **$(v_0, v_1) \mapsto r$ も追加**する。判定は $\equiv_R$ ルールファイルから推論せず、命令の操作的意味論（可換性が仕様で保証される演算）に基づく。

| 観点 | 内容 |
| --- | --- |
| **健全性** | 可換演算では $(v_1, v_0)$ と $(v_0, v_1)$ は同じ結果類 $c(\oplus(v_1,v_0))$ に到達する。逆向き edge は新しい値を生まない |
| **$\equiv_R$ との関係** | 可換律は $c(\cdot)$ の統合に効くが、$T_\oplus$ の operand pair 閉包は別途必要 |
| **非可換演算** | `sub`, `div`, `rem`, `shl`, `shr`, `rotl`, `rotr`, 比較等は双方向化しない |
| **支配制約との関係** | §5.5 の「可換二項演算の引数順正規化」は探索加速用の**任意**ヒューリスティック。本節の双方向化は**表現力**（completeness）のための必須閉包 |

典型例: オリジナル列では `(add ?L3 shr)` の向きだけが $T_{\mathrm{add}}$ に載る。`tee` + `get` 並べ替え後の短い列ではスタック上 `(shr, ?L3)` の順で `add` する必要がある。双方向化が無いと L-1 probe が UNSAT になり、符号化内で「最短」と誤証明されうる（§7.5）。

---

## 3. 命令集合 $\mathit{OP}$

| 命令 | 説明 |
| --- | --- |
| $\mathrm{const}_c$ | 定数 $c$ を天端に積む |
| $\mathrm{get}_x$ | ローカル $x$ の値を天端に積む |
| $\mathrm{set}_x$ | 天端をポップしてローカル $x$ に格納 |
| $\mathrm{tee}_x$ | 天端をローカル $x$ に格納(スタックは変化しない) |
| $\circ$(単項演算) | 天端を取り、結果を天端に積む |
| $\oplus$(二項演算) | 上位 2 要素を取り、結果を天端に積む |
| $\mathrm{NOP}$ | 何もしない(命令長最小化のための仮想命令) |

$\mathrm{const}_c$ は §2 で確定した定数集合 $C \subseteq V$ について用意する。$\mathrm{get}_x, \mathrm{set}_x, \mathrm{tee}_x$ は $x \in \{0, \ldots, R-1\}$ について用意する。単項・二項演算は問題で関心のあるもの全て(`shl`, `shr`, `add`, `mul`, `xor`, `and`, ...)を含める。

---

## 4. 決定変数

各 $i \in \{0, \ldots, L\}$(ステップ番号、$i=0$ は実行前)、$o \in \mathit{OP}$、$j \in \{0, \ldots, H-1\}$、$r \in \{0, \ldots, R-1\}$、$v \in V$ について命題変数を導入する。

| 変数 | 意味 |
| --- | --- |
| $x_{i,o}$ | ステップ $i$ ($i \geq 1$) で命令 $o$ が選ばれる |
| $y_{i,j,v}$ | ステップ $i$ 終了時にスタック位置 $j$ に値 $v$ がある |
| $w_{i,r,v}$ | ステップ $i$ 終了時にローカル $r$ に値 $v$ がある |

$y$ で $v = \bot$ はそのセルが「空」を意味する。$w$ で $v = \star$ はそのスロットが don't-care を意味する。

---

## 5. 制約

以下、$i$ は明示しない限り $\{1, \ldots, L\}$ を動く。

### 5.1 整合性制約

**命令一意性:** 各ステップで命令はちょうど 1 つ
$$\sum_{o \in \mathit{OP}} x_{i,o} \;=\; 1$$

**値一意性:** 各スタックセル・各ローカルにちょうど 1 つの値
$$\sum_{v \in V} y_{i,j,v} \;=\; 1 \quad (i = 0, \ldots, L;\; j = 0, \ldots, H-1)$$
$$\sum_{v \in V} w_{i,r,v} \;=\; 1 \quad (i = 0, \ldots, L;\; r = 0, \ldots, R-1)$$

これらは標準的な at-most-one + at-least-one の組合せで CNF 化する(Sinz エンコーディング等を使用)。

### 5.2 境界制約

**$i = 0$(初期状態):**

- $j < |S_0|$ について $y_{0,j,c(S_0[j])} = 1$
- $j \geq |S_0|$ について $y_{0,j,\bot} = 1$
- $M_0[r] \neq \star$ について $w_{0,r,c(M_0[r])} = 1$
- $M_0[r] = \star$ について $w_{0,r,\star} = 1$

**$i = L$(最終状態):**

- $j < |S_*|$ について $y_{L,j,c(S_*[j])} = 1$
- $j \geq |S_*|$ について $y_{L,j,\bot} = 1$
- $M_*[r] = \star$ について $w_{L,r,\cdot}$ は任意(制約なし)
- $M_*[r] \neq \star$ について $w_{L,r,c(M_*[r])} = 1$

### 5.3 命令意味論

各命令の意味論を、$x_{i,o} = 1$ ならば $(y_{i-1}, w_{i-1})$ と $(y_i, w_i)$ が次の関係を満たすという形で符号化する。

#### 共通: ローカル不変式

$\mathrm{set}_x, \mathrm{tee}_x$ 以外の全命令はローカルを変化させない:
$$x_{i,o} \;\to\; \bigwedge_{r, v}\bigl(w_{i,r,v} \leftrightarrow w_{i-1,r,v}\bigr) \qquad (o \notin \{\mathrm{set}_x, \mathrm{tee}_x\}_x)$$

#### $\mathrm{NOP}$

状態を変化させない:
$$x_{i,\mathrm{NOP}} \;\to\; \bigwedge_{j, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j,v}\bigr)$$

#### $\mathrm{const}_c$(0 入力 → 1 出力)

スタックオーバーフロー防止と、スタックを 1 段下にずらしながら天端に $v_c = c(c)$ を置く:
$$x_{i,\mathrm{const}_c} \;\to\; y_{i-1,H-1,\bot} = 1$$
$$x_{i,\mathrm{const}_c} \;\to\; y_{i,0,v_c} = 1$$
$$x_{i,\mathrm{const}_c} \;\to\; \bigwedge_{j \geq 1, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j-1,v}\bigr)$$

#### $\mathrm{get}_x$(0 入力 → 1 出力)

ローカル $x$ から値を読み(don't-care は読めない)、天端に積む:
$$x_{i,\mathrm{get}_x} \;\to\; w_{i-1,x,\star} = 0$$
$$x_{i,\mathrm{get}_x} \;\to\; y_{i-1,H-1,\bot} = 1$$
$$x_{i,\mathrm{get}_x} \;\to\; \bigwedge_v\bigl(y_{i,0,v} \leftrightarrow w_{i-1,x,v}\bigr)$$
$$x_{i,\mathrm{get}_x} \;\to\; \bigwedge_{j \geq 1, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j-1,v}\bigr)$$

#### $\mathrm{set}_x$(1 入力 → 0 出力)

天端をポップしてローカル $x$ に書き込む(空スタックからはポップ不可):
$$x_{i,\mathrm{set}_x} \;\to\; y_{i-1,0,\bot} = 0$$
$$x_{i,\mathrm{set}_x} \;\to\; \bigwedge_v\bigl(w_{i,x,v} \leftrightarrow y_{i-1,0,v}\bigr)$$
$$x_{i,\mathrm{set}_x} \;\to\; \bigwedge_{r \neq x, v}\bigl(w_{i,r,v} \leftrightarrow w_{i-1,r,v}\bigr)$$
$$x_{i,\mathrm{set}_x} \;\to\; \bigwedge_{j, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j+1,v}\bigr)$$
$$x_{i,\mathrm{set}_x} \;\to\; y_{i,H-1,\bot} = 1$$

ただし $j = H-1$ について $y_{i-1,j+1,\cdot}$ は存在しないので、その節は $y_{i,H-1,\bot} = 1$ で代替(最後の式)。

#### $\mathrm{tee}_x$(1 入力 → 1 出力、スタック不変)

天端をローカル $x$ に書き込むがスタックは保つ:
$$x_{i,\mathrm{tee}_x} \;\to\; y_{i-1,0,\bot} = 0$$
$$x_{i,\mathrm{tee}_x} \;\to\; \bigwedge_v\bigl(w_{i,x,v} \leftrightarrow y_{i-1,0,v}\bigr)$$
$$x_{i,\mathrm{tee}_x} \;\to\; \bigwedge_{r \neq x, v}\bigl(w_{i,r,v} \leftrightarrow w_{i-1,r,v}\bigr)$$
$$x_{i,\mathrm{tee}_x} \;\to\; \bigwedge_{j, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j,v}\bigr)$$

#### 単項演算 $\circ$(1 入力 → 1 出力)

天端 $v_0$ を取り、$T_\circ(v_0) = c(\circ(v_0))$ を天端に置く:
$$x_{i,\circ} \;\to\; y_{i-1,0,\bot} = 0$$
$$x_{i,\circ} \;\to\; \bigwedge_{v_0 \in V}\Bigl[y_{i-1,0,v_0} \;\to\; y_{i,0,T_\circ(v_0)}\Bigr]$$
$$x_{i,\circ} \;\to\; \bigwedge_{j \geq 1, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j,v}\bigr)$$

$T_\circ(v_0)$ が未定義の $v_0$ については、対応する節を $y_{i-1,0,v_0} \to \bot$、すなわち $\neg y_{i-1,0,v_0}$ を $x_{i,\circ}$ で含意する形にする(その引数では演算不可)。

#### 二項演算 $\oplus$(2 入力 → 1 出力)

上位 2 要素 $\mathrm{stack}[1] = v_1$、$\mathrm{stack}[0] = v_0$ を取り、$T_\oplus(v_1, v_0) = c(\oplus(v_1, v_0))$ を天端に置く:
$$x_{i,\oplus} \;\to\; y_{i-1,0,\bot} = 0 \;\wedge\; y_{i-1,1,\bot} = 0$$
$$x_{i,\oplus} \;\to\; \bigwedge_{(v_1, v_0) \in V \times V}\Bigl[\bigl(y_{i-1,1,v_1} \wedge y_{i-1,0,v_0}\bigr) \;\to\; y_{i,0,T_\oplus(v_1, v_0)}\Bigr]$$
$$x_{i,\oplus} \;\to\; \bigwedge_{j \geq 1, v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,j+1,v}\bigr)$$
$$x_{i,\oplus} \;\to\; y_{i,H-1,\bot} = 1$$

$T_\oplus(v_1, v_0)$ が未定義のペアについては $y_{i-1,1,v_1} \wedge y_{i-1,0,v_0}$ の組合せ自体を $x_{i,\oplus}$ のもとで禁止する。

**可換演算の operand pair 閉包:** §2.3.1 に従い、$\oplus$ が可換なら $T_\oplus$ 構築時に $(v_1, v_0)$ と $(v_0, v_1)$ の**両方**を許可する。正節（入力 → 結果）と禁止節（許可されていない pair の排除）の**両方**を同じ双方向 edge 集合から生成する。禁止節だけ緩めて正節を追加しないと、逆向き入力に対する結果制約が欠落する。

#### 実装: $\top$ sink による全域関数化（2026-07-01）

疎な $T_\oplus/T_\circ$（e-graph 由来の valid-edge リスト）だけでは、第1オペランドがエッジを持たないクラスで結果セル $y_{i,0,\cdot}$ が `exactly_one` 以外に無拘束になり、**擬似モデル**（でたらめな算術で最終クラスに合わせた列）が指数的に湧く。CEGAR 型の後段精緻化では組み合わせ爆発のため実用的でない。

**対策:** スタック値ドメインに語彙外 sink $\top$（index $n+1$、$\bot$ は $n$）を追加し、演算を**全域関数**として符号化する。

- **正節:** 既存の sparse edge $(v_1, v_0) \mapsto v_{\mathrm{res}}$ を維持（同一対に複数 rep がある場合は最小 index に dedup）
- **per-$v_1$ domain 節（全 $v_1 \in V$）:** $x_{i,\oplus} \wedge y_{i-1,1,v_1} \wedge \neg\bigvee_{v_0 \in S_{v_1}} y_{i-1,0,v_0} \;\to\; y_{i,0,\top}$（$S_{v_1}=\emptyset$ なら常に $\top$ へ）
- **吸収節:** $x_{i,\oplus} \wedge y_{i-1,1,\top} \;\to\; y_{i,0,\top}$
- **単項演算:** 既存の無条件 domain 節に $\vee y_{i,0,\top}$ を追記
- **$\top$ 遮断:** $\mathrm{set}_x/\mathrm{tee}_x$ は $y_{i-1,0,\top}=0$ を要求（ローカルへ $\top$ を書かない）。境界・opaque オペランドは real のみ pin するため $\top$ はゴールに到達不能

これにより「抽象で目標クラスに到達 $\Leftrightarrow$ 真に正しい $\equiv_R$ 値を計算」が成り立ち、擬似モデルは源流で排除される。節数は per-$v_1$ domain（$O(L \cdot |\oplus| \cdot |V|)$）に抑え、素朴な $|V|^2$ 正節×$L$ より大幅に小さい。

### 5.4 NOP 伝播

末尾固定:一度 NOP が出現したら、それ以降も全て NOP:
$$x_{i,\mathrm{NOP}} \;\to\; x_{i+1,\mathrm{NOP}} \quad (i = 1, \ldots, L-1)$$

この制約により、命令長 $\ell$ とは「$x_{i,\mathrm{NOP}} = 0$ である最大の $i$」になる。

### 5.5 (オプション)支配・冗長制約

最適性を損なわず探索を加速するため、以下を追加してよい。

- **不要な値の早期処理:** $\mathit{init.stack}$ にあり $\mathit{fin}$ にも演算引数にも現れない値は、$\mathrm{set}_x$ で死ぬローカルへ送るしかない。これを最初の数命令に集中させる。
- **連続する $\mathrm{set}_x$ → $\mathrm{get}_x$ の禁止:** $\mathrm{tee}_x$ で常に置換可能(等価かつ命令数は同じか少ない)。
- **使われない $\mathrm{get}_x$ → $\mathrm{set}_y$ の禁止:** 同じスロット間ならコピー、それ以外なら無意味。
- **可換二項演算の引数順正規化:** $\oplus$ が可換なら、$(v_0, v_1)$ で辞書順小の方を $\mathrm{stack}[0]$ に置く。

これらは元手法の支配制約(SuperStack §4.3 と同等)に対応する。

---

## 6. 命令長最小化:降順 Pure-SAT 反復

### 6.1 観察と方針

NOP 伝播制約 (§5.4) のもとでは:

- **「長さ $\ell$ 以下の解が存在する」** $\Leftrightarrow$ **「$x_{\ell+1, \mathrm{NOP}} = 1$ を仮定した CNF が SAT」** (ただし $\ell < L$)
- $\ell = L$ では仮定なしで SAT を呼ぶ(NOP が出現しない長さ $L$ の解)

エンコーディングの上界 $L$ を **オリジナル命令列の長さ $L_{\mathrm{orig}}$** に取る。すると初回の SAT 呼び出しは **必ず SAT を返す**(オリジナルがそのまま解だから)。あとは「もう 1 つ短くできるか?」を反復で確認する。具体的には、$\ell$ を $L_{\mathrm{orig}} - 1, L_{\mathrm{orig}} - 2, \ldots$ と 1 ずつ減らしながら $x_{\ell+1, \mathrm{NOP}} = 1$ を assumption として SAT を呼び、**UNSAT が出た瞬間に止める**。最後に SAT を返した $\ell + 1$ が最適長 $L^*$ となる。

### 6.2 アルゴリズム

```python
def minimize_length_descending(phi, L_orig):
    """
    phi: §5.1–§5.4 の全制約を含む CNF (上界 L = L_orig でエンコード)
    L_orig: オリジナル命令列の長さ
    戻り値: 最短長 L*, 対応する命令列
    """
    solver = IncrementalSATSolver()
    solver.add_clauses(phi)

    # ステップ 1: 上界 L_orig での充足性確認
    # オリジナル命令列が解として含まれているはずなので SAT
    result = solver.solve(assumptions=[])
    if result != SAT:
        # 語彙 V またはパラメータ H, R に不備
        raise EncodingError("L_orig での SAT が失敗。語彙やパラメータを見直すこと")

    best_model = solver.get_model()
    L_star = L_orig

    # ステップ 2: 1 ずつ減らしながら降下
    ell = L_orig - 1
    while ell >= 0:
        # 「長さ ell 以下の解は存在するか?」を問う
        # NOP 伝播により x_{ell+1, NOP} = 1 で位置 ell+1 以降が全 NOP
        assumptions = [x[ell + 1, NOP]]
        result = solver.solve(assumptions=assumptions)

        if result == SAT:
            best_model = solver.get_model()
            L_star = ell
            ell -= 1
        else:
            # UNSAT: 長さ ell 以下では実現不可能。1 つ前の L_star が最適
            break

    instructions = reconstruct(best_model, L_star)
    return L_star, instructions


def reconstruct(model, L_star):
    """SAT 解から命令列を抽出(NOP を除く)"""
    seq = []
    for i in range(1, L_star + 1):
        for o in OP:
            if model[x[i, o]] == 1 and o != NOP:
                seq.append(o)
                break
    return seq
```

### 6.3 この方式の利点

| 利点 | 説明 |
| --- | --- |
| **初回呼び出しが自明に SAT** | $L_{\mathrm{orig}}$ がそのまま解。UNSAT 判定の難しさを初期化段階で回避 |
| **常に有効な解を保持** | 反復のどの時点で止めても $\mathit{best\_model}$ は実行可能な命令列を表す |
| **タイムアウト耐性** | 時間切れで打ち切っても、それまでに得られた最短解を出力できる |
| **incremental SAT との相性** | 制約本体は不変、assumption のみ変化。学習節が累積する |
| **早期終了** | UNSAT が 1 回出れば停止。二分探索より呼び出し回数が多い場合があるが、各呼び出しが SAT で完結する間は速いことが多い |

### 6.4 タイムアウト付き運用

実用では時間制限を設けて、その時点での暫定最良解を返すことが多い:

```python
def minimize_length_with_timeout(phi, L_orig, time_budget):
    solver = IncrementalSATSolver()
    solver.add_clauses(phi)
    deadline = time.time() + time_budget

    # 初回(オリジナル長で確認)
    solver.solve(assumptions=[])  # 必ず SAT
    best_model = solver.get_model()
    L_star = L_orig

    ell = L_orig - 1
    while ell >= 0 and time.time() < deadline:
        remaining = deadline - time.time()
        result = solver.solve(
            assumptions=[x[ell + 1, NOP]],
            time_limit=remaining
        )
        if result == SAT:
            best_model = solver.get_model()
            L_star = ell
            ell -= 1
        elif result == UNSAT:
            break
        else:  # TIMEOUT
            break

    is_proven_optimal = (result == UNSAT) or (L_star == 0)
    instructions = reconstruct(best_model, L_star)
    return L_star, instructions, is_proven_optimal
```

`is_proven_optimal` は「真に最適であることが証明できた」場合のみ True。タイムアウトの場合は False(さらに短縮可能な可能性が残る)。

### 6.5 オリジナル命令列の SAT 表現可能性

降順方式が成立するためには **「$L_{\mathrm{orig}}$ でのエンコーディングが必ず SAT になる」** 性質が必要。これは §2.1 の語彙構築でオリジナル命令列の中間値を確実に取り込むことで保証される(§2.1 の修正を参照)。

万一オリジナルが SAT で表現できない(語彙の取りこぼし)場合の対処:

1. $V$ にオリジナル命令列を実行して得られる全中間値を追加して $V$ を拡張
2. 等価類飽和の反復回数 $k_{\mathrm{sat}}$ を増やす
3. それでも失敗するなら、フェーズ 1 の規則 $\equiv_R$ が不十分

### 6.6 (参考)昇順との比較

| 観点 | 降順(本方式) | 昇順 |
| --- | --- | --- |
| 初回呼び出し | 確実に SAT | UNSAT の可能性大(短すぎる仮定) |
| 暫定解 | 常に保持 | 最初の SAT 呼び出しまで存在しない |
| タイムアウト時の出力 | これまでの最短解 | 一切の解が出ない可能性 |
| 必要な呼び出し回数 | $L_{\mathrm{orig}} - L^* + 1$ 回(最良) | $L^*$ 回(最良) |
| UNSAT 判定 | 1 回のみ(終端) | 毎回 |

降順は **「実用上常に何らかの改善された解を返す」** 点で実装に向く。昇順は理論的にはステップ数が少ないことがあるが、UNSAT 判定が SAT 判定より一般に重いため、実時間では降順が勝つことが多い。

---

## 7. 健全性と最適性

### 7.1 健全性

各命令の意味論制約 §5.3 が WebAssembly の操作的意味論を正確に反映していれば、SAT 解 $\mu$ から再構成された命令列 $\sigma = o_1 o_2 \cdots o_{\ell}$ は次を満たす:

- $\mathit{init}$ を $\sigma$ で実行すると(NOP を除き)$\mathit{fin}$ に到達する
- 途中でスタックアンダーフロー・$\star$ ローカルの読み出しは起こらない

これは数学的帰納法で示せる:$\mu$ が制約 §5.1–§5.4 を満たすので、各 $i$ について「$y_i, w_i$ は $y_{i-1}, w_{i-1}$ に $o_i$ を適用した結果と一致する」が成り立つ。境界条件 §5.2 と合わせて全体が成立。

### 7.2 最適性(語彙 $V$ と上界 $L, H, R$ の下で)

降順反復 (§6.2) が長さ $L^*$ で停止したとき(つまり長さ $L^* - 1$ 以下が UNSAT で長さ $L^*$ で SAT)、$L^*$ は **語彙 $V$ で表現可能な命令列のうち最短** である。

**証明スケッチ:**

- (達成可能性) 最後に SAT を返した反復のモデル $\mathit{best\_model}$ が長さ $L^*$ の実行可能命令列を与える
- (下界) 長さ $L^* - 1$ 以下の問い合わせが UNSAT であったため、語彙 $V$ で表現可能な長さ $L^* - 1$ 以下の命令列は存在しない
- (語彙の十分性) $V$ がオリジナル命令列の中間値を含み、かつ $\equiv_R$ で閉じていれば、エンコーディングは関連する全ての等価表現を網羅する

タイムアウトで打ち切った場合は、$L^*$ は「**$L^*$ 以下の長さで実現可能であることが確認された最良値**」にとどまる(真の最適とは限らない)。

### 7.3 最適性の限界

次の場合は真の最適解を見逃し得る:

| 原因 | 対処 |
| --- | --- |
| $V$ が $\equiv_R$ で完全に飽和されていない | $k_{\mathrm{sat}}$ を増やす |
| $H$ が真の最適解より小さい | $H$ を増やして再試行 |
| $R$ が小さすぎる | $R$ を増やす |
| 真の最適解が $L_{\mathrm{orig}}$ より長い経路を経由する場合 | 通常起こり得ない(オリジナルが達成可能なため $L^* \leq L_{\mathrm{orig}}$ は保証される) |
| $\equiv_R$ が不完全(必要な等価規則を含まない) | フェーズ 1 の規則集合を拡張 |
| **$V$ がオリジナルトレース外の中間スタック状態を含まない** | §10 の CEGAR 的語彙拡張、または候補スケジュールからの種追加 |
| **$T_\oplus, T_\circ$ に未定義の遷移が必要なスケジュール** | $V$ 拡張に伴う $T$ 再計算。可換 binop の operand 順反転は §2.3.1 |
| **不透明命令のオペランドが元 $\mathit{in}[k]$ と構造が異なる同値経路** | §11.3 のオペランド要求を $\equiv_R$ 同値類で緩和（§11.8） |
| **call 前後の spill タイミング変更（スタック直結）** | §11.8 のスケジュール表現の見直し |

最後から 4 行目までは本手法の外側または符号化設計の問題。$\equiv_R$ 規則の不足だけがフェーズ 1 の責任、とは限らない。

**重要:** §7.2 の「$L^*$ は語彙 $V$ で表現可能な命令列のうち最短」は、**グローバルな Wasm 最適性**や **SuperStack 等の別探索器との一致**を意味しない。降順反復が UNSAT で止まっても、それは**現行符号化の閉世界内**の証明に過ぎる。

### 7.4 「同時最適化」の保持（限定的な主張）

本帰着は、**探索空間に含まれるスケジュール**については、算術選択・スピル・命令順序を同時に最適化できる:

- **算術の選択:** §2.3 の $T_\oplus$ が $\equiv_R$ で同値な表現を同じ正規代表に潰すため、$T$ に載った遷移に限り算術形式の選択は統合される。
- **スピル:** $\mathrm{set}_x, \mathrm{get}_x, \mathrm{tee}_x$ は $\mathit{OP}$ に含まれ、ステップ $i$ の割当として他命令と同列に選べる。
- **スケジューリング:** ステップ番号 $i$ が命令順序を表現する。

ただし次は**自動的には保証されない**（詳細は §7.5, §11.8, [`0701_suboptimal_cause.md`](0701_suboptimal_cause.md)）:

- `local.tee` による set/get 融合と、call を挟んだ spill タイミング変更の**組み合わせ**（多段融合）
- オリジナルトレースに無かった中間スタック構成を経由するデータフロー（語彙 $V$ 不足）
- 不透明命令のオペランドが、元 $\mathit{in}[k]$ と $\equiv_R$ 同値だが構造が異なる経路

**緩和済み:** pure 可換 binop（`add` 等）について、命令並べ替え後のスタック operand 順反転は §2.3.1 の $T_\oplus$ 双方向化で表現可能。

### 7.5 tee 融合・spill スケジュール変更の表現限界（既知のギャップ）

`local.tee` は §3 の $\mathit{OP}$ に含まれるが、SuperStack 型の短縮は単純な局所置換ではない。典型例では次が同時に起きる:

1. **局所 tee 融合:** $\mathrm{set}_x$ 直後の $\mathrm{get}_x$ を $\mathrm{tee}_x$ に置換（1 命令削減）
2. **spill スケジュール変更:** call 前の $\mathrm{set}_y$ + call 後の $\mathrm{get}_y$ を、call を挟んだスタック保持 + call 後の $\mathrm{tee}_y$ に置換
3. **命令並べ替え:** 上記を成立させる純粋演算・副作用命令の順序変更

Pure-SAT がこれに到達できない主因は、§3 に $\mathrm{tee}$ が無いことではなく、次の組み合わせである:

| 要因 | 関連節 |
| --- | --- |
| $V$ がオリジナル記号実行の中間値中心で、新スケジュールのスタックラベルが不足 | §2.1, §7.3 |
| **$T$ が事前計算の遷移のみ許可し、新データフローの演算ペアを拒否** | §2.3, §5.3。**可換 binop の operand 順**については §2.3.1 の双方向化で緩和済み。非可換演算や $V$ に無い中間値は依然として拒否されうる |
| 不透明命令のオペランドが元 $\mathit{in}[k]$ に固定され、同値別表現の入力経路が閉じる | §11.3 |
| call の固定 $(p,q)$ スタックシフトと $\mathit{deplist}$ が、オリジナルと異なるスタック系列を実現しにくい | §11.3, §11.5 |
| 符号化後の再検証が、符号化のオペランド固定と異なる軸で厳しい場合がある | §11.6, §11.8 |

---

## 8. 複雑度と実装上の注意

### 8.1 サイズ見積もり

| 項目 | 規模 |
| --- | --- |
| 変数 $x$ | $O(L \cdot |\mathit{OP}|)$ |
| 変数 $y$ | $O(L \cdot H \cdot |V|)$ |
| 変数 $w$ | $O(L \cdot R \cdot |V|)$ |
| 二項演算節 | $O(L \cdot |\oplus\text{の種類}| \cdot |V|^2)$ |
| 他の意味論節 | $O(L \cdot |\mathit{OP}| \cdot (H + R) \cdot |V|)$ |

二項演算の節数が最も支配的になる。$|V|^2$ の項を制御するため、$V$ の構築では $k_{\mathrm{sat}}$ を必要最小限に抑える。

### 8.2 実用上のスケール

参考として、SuperStack の実験報告(PLDI'24)によれば、命令長 40 程度までが Wasm における実用的な上限(タイムアウト 5 分)。本手法も同程度のスケールが期待される。長い直線コードは分割して各セグメントを最適化する。

### 8.3 incremental SAT

§6 の反復 SAT は incremental SAT ソルバで実装する:

- 同じ CNF 本体を保持
- 各反復で異なる assumption($x_{\ell+1, \mathrm{NOP}}$ の真偽)だけ切り替える
- 学習節が累積し、後続の呼び出しが高速化

PySAT (Glucose 3.0 / CaDiCaL / Kissat バックエンド) が選択肢。

### 8.4 等価類飽和の前処理

$V$ と $T$ の構築は SAT 呼び出しの前に一度だけ行う:

- E グラフライブラリ(`egg` の Rust 実装、Python バインディングあり)を使うと書き換え規則の適用と congruence closure が自動化される
- 飽和反復回数 $k_{\mathrm{sat}}$ は問題依存。$\equiv_R$ の規則が単純(算術恒等式のみ)なら $k_{\mathrm{sat}} = 3 \sim 5$ で十分

### 8.5 不要な値・命令の除去

ヒューリスティックで以下を除外すると SAT インスタンスが小さくなる:

- $\mathit{fin}$ から到達不可能なローカル番号
- $\mathit{fin}$ の部分式・$\mathit{init}$ の構成要素のいずれにも含まれない値
- 引数が $V$ に含まれないため $T$ が常に未定義になる演算

これらは最適性に影響しない(到達不可能な選択肢を消すだけ)。

---

## 9. 実行例

元手法 §12 の例で具体的に追う。

### 9.1 入力

- $\mathit{init} = (\mathrm{stack} = [], \mathrm{local} = \{0: L\})$
- $\mathit{fin} = (\mathrm{stack} = [(L \ll 1) \ll 2,\; L \ll 1], \mathrm{local} = \{0: L \ll 1\})$
- $\equiv_R$ は `mul`/`shl` の同値性、結合律、可換律を含む

### 9.2 語彙の構築

部分式と等価表現を集めると:

$$V = \{L,\; 1,\; 2,\; 4,\; L \ll 1,\; (L \ll 1) \ll 2,\; \bot,\; \star\}$$

正規代表の同定により:

- $c(\mathrm{mul}(L \ll 1, 4)) = c(\mathrm{shl}(L \ll 1, 2)) = (L \ll 1) \ll 2$
- $c(\mathrm{mul}(L, 2)) = c(\mathrm{shl}(L, 1)) = L \ll 1$

### 9.3 演算結果テーブルの抜粋

| 入力 | $T_{\mathrm{shl}}$ |
| --- | --- |
| $(L, 1)$ | $L \ll 1$ |
| $(L \ll 1, 2)$ | $(L \ll 1) \ll 2$ |
| その他 | 未定義(節を生成しない) |

| 入力 | $T_{\mathrm{mul}}$ |
| --- | --- |
| $(L, 2)$ | $L \ll 1$ |
| $(L \ll 1, 4)$ | $(L \ll 1) \ll 2$ |
| その他 | 未定義 |

### 9.4 パラメータ

オリジナル命令列の長さを $L_{\mathrm{orig}} = 10$ と仮定する(`get 0; const 0; set 0; get 0; const 1; shl; tee 0; get 0; const 2; shl` のような冗長な実装が与えられているとする)。エンコーディングは:

- $L = L_{\mathrm{orig}} = 10$
- $H = 4$(最大スタック高さ)
- $R = 1$(ローカルは 1 つ)
- $|V| = 8$
- $|\mathit{OP}|$:`const 1`, `const 2`, `const 4`, `get 0`, `set 0`, `tee 0`, `shl`, `mul`, `NOP` の 9 つ

### 9.5 降順反復 SAT の挙動

オリジナル長 $L_{\mathrm{orig}} = 10$ から始めて 1 ずつ減らす:

| $\ell$ | $x_{\ell+1, \mathrm{NOP}}$ 仮定 | SAT 結果 | $\mathit{best\_model}$ 更新 |
| --- | --- | --- | --- |
| 10 | (なし、初回) | **SAT**(オリジナルが解) | $L^* \leftarrow 10$ |
| 9 | $x_{10, \mathrm{NOP}} = 1$ | **SAT** | $L^* \leftarrow 9$ |
| 8 | $x_{9, \mathrm{NOP}} = 1$ | **SAT** | $L^* \leftarrow 8$ |
| 7 | $x_{8, \mathrm{NOP}} = 1$ | **SAT** | $L^* \leftarrow 7$ |
| 6 | $x_{7, \mathrm{NOP}} = 1$ | **UNSAT**(6 命令では不可能) | 停止 |

**結論:** $L^* = 7$。最後に SAT を返したときのモデルが最適解。

途中でタイムアウトしても、その時点までの $L^*$ は実行可能な解として返せる点に注目(例えば $\ell = 9$ で SAT を確認した時点で打ち切れば、9 命令の改善解が得られる)。

### 9.6 抽出された命令列

SAT 解から再構成された最適解の一例:

```
get 0      ; stack: [L],            local: {0: L}
const 1    ; stack: [1, L],         local: {0: L}
shl        ; stack: [L≪1],          local: {0: L}
tee 0      ; stack: [L≪1],          local: {0: L≪1}
get 0      ; stack: [L≪1, L≪1],     local: {0: L≪1}
const 2    ; stack: [2, L≪1, L≪1],  local: {0: L≪1}
shl        ; stack: [(L≪1)≪2, L≪1], local: {0: L≪1}
(NOP)      ; これ以降全て NOP
```

7 命令で $\mathit{fin}$ に到達。`shl` を `mul` で置き換えた等価な 7 命令解(`const 2; mul` の代わりに `const 4; mul`)も同じく SAT 解の候補だが、命令数が同じならどちらが選ばれてもよい。算術等価性 $\equiv_R$ は $T$ で吸収済みのため、SAT 探索は「同じ値に到達する複数経路」を意識せず統合的に評価する。

---

## 10. 拡張と今後の課題

本帰着の中核（§2–§9）は直線・副作用なしの場合に閉じて完結している。副作用の扱いは §11 で与える。元手法の §14 で挙げられた他の限界は本帰着でも引き継がれる:

- **副作用とメモリ:** メモリアクセス・グローバル変数・関数呼出しは §11 で扱う（非解釈命令 + `deplist` 順序制約）。
- **語彙の動的拡張:** $V$ を事前に確定せず、SAT が UNSAT を返したら $k_{\mathrm{sat}}$ を増やす、または候補スケジュールから中間値を追加して再エンコードする CEGAR 風の手続き（§7.5, §11.8）
- **支配制約の強化:** SuperStack §4.3 のような制約は健全性を損なわず追加可能で、特に大きな命令列で効果的（§5.5）。ただし可換演算の引数順固定などは、非可換経路を誤って刈る危険がある（実装時は §5.5 ルール4を演算側の可換性条件付きで適用すること）
- **tee 融合・spill スケジュール:** §7.5, §11.8。`local.tee` の存在だけでは SuperStack 型の短縮は保証されない

---

## 11. 副作用（メモリ・グローバル・関数呼び出し）の扱い

メモリアクセス・グローバル変数・関数呼び出し・その他の非 i32 命令（まとめて**不透明命令**, opaque op）を、SuperStack (§2.4) の流儀で**非解釈命令**としてエンコーディングに統合する。後方探索や別フェーズを追加せず、§4–§5 の同じ $x/y/w$ 変数と降順 Pure-SAT 反復（§6）の枠内で扱う。

### 11.1 不透明命令のモデル化

各不透明命令はパース時の記号実行から次のメタデータを得る（実装上は `OpaqueMeta`、依存解析は `deps.rs`）。

| 項目 | 意味 |
| --- | --- |
| $\mathit{id}$ | セグメント内で命令を一意に識別する番号 |
| $\mathit{storage}$ | 観測可能な副作用を持つか（store / global.set / call / storage 付き opaque） |
| $\mathit{in}[0..p)$ | 消費するオペランド値。top-to-bottom 表記で $\mathit{in}[k]$ が $\mathrm{stack}[k]$ |
| $\mathit{out}[0..q)$ | 生成する**フレッシュな結果シンボル**（`?load_id`, `?call_id_i`, `?global_get_id` 等） |

結果シンボルは「メモリ／呼び出しが返す未知の値」を表す不可分の葉で、$\equiv_R$ では他の式と同値化しない。これにより load 結果が算術的に再計算されることを防ぐ。

> **オペランド順序の注意:** $\mathit{in}[k]$ は前方実行のポップ順（$\mathit{op}$ 実行直前の $\mathrm{stack}[k]$）に一致させる。`load`/`store`/`global.*` はポップ順そのまま、`call`/`opaque` は記号実行が引数を反転して記録するため逆順に直す。これを誤ると store の格納値／アドレスや call の引数順が入れ替わり、健全性を損なう（前方検証では検出されない）。

### 11.2 語彙と命令集合の拡張

- **語彙 $V$:** §2.1 のステップに加え、全不透明命令の $\mathit{in}$・$\mathit{out}$ の値（および結果シンボル）を $V$ に追加する。これによりオリジナル命令列が $L_{\mathrm{orig}}$ で必ず表現可能（初回 SAT、§6.5）になる。
- **命令集合 $\mathit{OP}$:** 不透明命令は**命令種ごと**ではなく**命令インスタンスごと**に 1 つの $\mathit{op}$ を追加する（オペランド・結果が特定のプログラム点に固定されているため）。$x_{i,\mathit{op}}$ は「ステップ $i$ でその特定の副作用命令を実行する」を意味する。

### 11.3 命令意味論（§5.3 への追加）

$p$ 入力・$q$ 出力の不透明命令 $\mathit{op}$ を考える。$\delta = p - q$ とする。

**オペランド要求（天端 $p$ セルが指定値）:**

基本形は、不透明命令 $\mathit{op}$ の記録された入力 $\mathit{in}[k]$ とスタック位置 $k$ の値が一致することを要求する:

$$x_{i,\mathit{op}} \;\to\; y_{i-1,k,\,\mathit{in}[k]} = 1 \qquad (k = 0, \ldots, p-1)$$

ここで $\mathit{in}[k]$ は $V$ 内の**特定の代表元インデックス**である。実装では同一 $\equiv_R$ 類に属する別インデックスも許容する緩和（$\mathit{equiv}(v) = \{ v' \in V \mid c(v') = c(v) \}$）を入れてよいが、**$V$ に無い式や、$\mathit{in}[k]$ と $\equiv_R$ 同値だが構造が異なる式**までは自動的には許されない。

> **実装（2026-07-01）:** `build_vocab` 終端で `reals` 全体の joint saturation から `equiv_class` を計算し、`encode_opaque` のオペランド許容集合は `canon_ids` ではなく `equiv_class` 一致で閉じる（再検証 `values_equivalent` と整合）。$V$ に同一類の別表現が複数載っている場合にのみ効く。

> **既知のギャップ（§7.5, §11.8）:** `local.tee` によるスケジュール変更後、**pure 可換 binop** の operand 順反転は §2.3.1 で $T_\oplus$ 側に閉じる。**load / call 等の不透明命令**では、実行上は同値でも元トレースの $\mathit{in}[k]$ と異なる構文木になりうる。後者は §11.3 の要求が探索空間を過剰に狭め、tee 融合解を表現不能にしうる。対処は §11.8 を参照。

**結果生成（天端 $q$ セルに結果シンボル）:**
$$x_{i,\mathit{op}} \;\to\; y_{i,j,\,\mathit{out}[j]} = 1 \qquad (j = 0, \ldots, q-1)$$

**残りスタックのシフト（消費・生成域より下を $\delta$ ずらす）:**
$$x_{i,\mathit{op}} \;\to\; \bigwedge_{v}\bigl(y_{i,j,v} \leftrightarrow y_{i-1,\,j+\delta,\,v}\bigr) \qquad (q \le j < H,\; 0 \le j+\delta < H)$$
$$x_{i,\mathit{op}} \;\to\; y_{i,j,\bot} = 1 \qquad (q \le j < H,\; j+\delta \ge H)$$

**オーバーフロー防止（$q > p$ で天端が増える場合、底 $q-p$ セルは空でなければならない）:**
$$x_{i,\mathit{op}} \;\to\; y_{i-1,\,H-1-t,\,\bot} = 1 \qquad (t = 0, \ldots, q-p-1,\;\text{ただし } q > p)$$

**ローカル不変:** 不透明命令はローカルを変えない（§5.3 共通則と同様）。

オペランドを指定値で固定する要求は、store のアドレス・格納値や call の引数が正しく計算されることを保証する（健全性に必須）。$p = 0$（global.get 等）ならオペランド要求はなく、$q = 0$（store / global.set 等）なら結果生成はない。

### 11.4 出現回数制約

各不透明命令 $\mathit{op}$ の全ステップにわたる出現を制約する。

- **storage（厳密に 1 回）:** 観測可能な副作用は省略も重複もできない。
  $$\sum_{i=1}^{L} x_{i,\mathit{op}} \;=\; 1$$
- **非 storage（高々 1 回）:** load 等は結果が必要なときだけ使われ、重複再実行は禁止。
  $$\sum_{i=1}^{L} x_{i,\mathit{op}} \;\le\; 1$$

いずれも Sinz 系列エンコーディングで CNF 化する。非 storage 命令はその結果シンボルが下流（$\mathit{fin}$ や他命令の引数）で要求されない限り、最適化で自然に消える（死んだ load の除去）。

### 11.5 依存順序制約（deplist）

メモリ／グローバル／呼び出しの相対順序を、SuperStack §2.4.1 の依存リスト $\mathit{deplist}$（`deps.rs` が事前計算）として強制する。各辺 $(a \prec b)$（命令 $a$ は $b$ より前）について、$b$ を $a$ と同じか後のステップに置くことを禁止する:
$$\neg x_{i_a,\,a} \;\vee\; \neg x_{i_b,\,b} \qquad (1 \le i_b \le i_a \le L)$$

すなわち「$b$ がステップ $i_b$、$a$ がステップ $i_a \ge i_b$」の同時成立を禁じ、$\mathrm{step}(a) < \mathrm{step}(b)$ を保証する。辺数は $\mathit{deplist}$ のサイズ、節数は各辺 $O(L^2)$。

A\* が依存順序を解の受理時に事後検証するのに対し、SAT は**ハード制約として探索前から枝刈り**する点が異なる。

### 11.6 健全性と再検証

降順反復（§6）で得たモデルから命令列を再構成したのち、念のため

- 前方記号実行で $\mathit{init} \to \mathit{fin}$ 接地を確認（§7.1 と同じ）
- $\mathit{storage\_ops\_preserved}$（各 storage が 1 回）と $\mathit{ops\_respect\_dependencies}$（$\mathit{deplist}$ 順序）を確認
- **（推奨）各不透明命令の実際の入力式が、元セグメントの記録と $\equiv_R$ で一致すること**を確認

を行い、満たさないモデルは棄却する。

§11.3–§11.5 の制約が完全かつ再検証の前提が符号化と一致していれば、再検証は常に成立する。ただし再検証が「元 $\mathit{in}[k]$ の文字列」と「実行トレース上の式」の $\equiv_R$ 一致を別途要求する場合、**符号化が許した候補が再検証で落ちる**、あるいは**符号化自体がスケジュール変更後の同値入力を表現できない**ことがある（§7.5, §11.8）。このとき §7.2 の $L^*$ は符号化内最適にとどまる。

### 11.7 表現不能時の挙動

語彙やパラメータの都合で不透明命令を符号化できない、あるいは初回 SAT が UNSAT になる場合は、A\* 等へフォールバックせず**オリジナル命令列をそのまま保持**する（改善なし）。降順反復は常にオリジナルを初期解に持つため、出力は必ず正当である。

### 11.8 tee 融合・spill スケジュール変更への拡張方針

§3 に $\mathrm{tee}_x$ があるにもかかわらず SuperStack 型の短縮に届かない根本は、本符号化に残る**トレース指向の残滓**（語彙の種・$\mathit{in}[k]$ ピン・$L_{\mathrm{orig}}$ witness が元命令列由来）にある。Denali・SuperStack はいずれも**ゴール指向**（語彙・命令集合を最終状態 $\mathit{fin}$ から作り、スケジュールは `deplist` のみで自由化）であり、tee 融合はその自由から自然に出る。以下は残滓を外してゴール指向へ寄せる手法レベルの対処（[`0701_suboptimal_cause.md`](0701_suboptimal_cause.md) §5.2 の方向 A–F に対応）。

| 方向 | 内容 | 関連節 | 根拠論文 |
| --- | --- | --- | --- |
| **A: `≡_R` の網羅化** | 手書きで不完全になりがちな $\equiv_R$ を Ruler（equality saturation による規則合成）で健全・網羅的に生成。可換律・定数畳み込み等を canon が真に統合できるようにする | §2.2, §7.3 | Ruler |
| **B: 遷移表・オペランドの e-class 閉包** | §2.3 の $T_\oplus/T_\circ$ と §11.3 の $\mathit{in}[k]$ 固定を、代表元でなく $\equiv_R$ 同値類（e-class）全体で閉じる。**可換 binop については §2.3.1 の operand pair 双方向化**（Wasm 意味論ベース）を $T$ 構築に組み込む。A が供給した同値を探索空間に反映 | §2.3, §2.3.1, §5.3, §11.3 | Denali（`args(T)` = e-class, `B(i,Q)`） |
| **C: ゴール指向の語彙** | §2.1 の $V$ を「トレース閉包」でなく $\mathit{fin}$ 由来の記号要素を起点に $\equiv_R$ 閉包で構築。§10 の CEGAR 的拡張を包摂する本命 | §2.1, §7.3, §10 | Denali §5, SuperStack §2.4 |
| **D: スケジュールとトレースの分離** | 順序制約を `deplist` のみに限り、Denali の select-store 節で load/store 順序自由を与えて過剰な全順序を緩める。$L_{\mathrm{orig}}$ witness への依存も見直す | §11.3, §11.5 | Denali §6–7, SuperStack §4 |
| **E: greedy 融合 seed** | SuperStack の Wasm greedy で tee 融合済みの初期解を作り、上界 $L$ の短縮＋良い初期モデルとして SAT に渡す。A–D で符号化が SS 解を表現可能になれば、SAT は最適性証明に専念できる | §6, §8.5 | SuperStack §3.2 |
| **F: 最適性ラベルの分離** | 「符号化内で $L^*-1$ が UNSAT」と「グローバル最適」を出力上区別（§6.4 の `is_proven_optimal` を符号化・ルールセット相対と明示）。Denali の "near-optimal" 開示に倣う | §6, §7.2 | Denali §6 |

**符号化と再検証の整合**（§11.6）は A・B の前提: CNF が許すスタック値と再検証が要求する不透明入力の同値判定を、同一の $\equiv_R$ に揃える。

**現状の到達点（2026-07-02）:**

| 項目 | 状態 |
| --- | --- |
| 可換 binop の $T_\oplus$ 双方向化（§2.3.1） | **採用済み**。`tee` + 命令並べ替えでスタック operand 順が反転する cat A 型（pure-local block）の主要ブロッカーを解消 |
| Get/Set/Tee 境界の $\equiv_R$ 許容 | 部分採用。転送境界の e-class 統合 |
| 多段 `tee` 融合（2 命令以上の同時融合） | 未解決（bucket C）。別途 witness / 語彙拡張が必要 |
| ゴール指向語彙（方向 C） | 未着手 |

優先順は **B（可換 operand 閉包）→ A（$\equiv_R$ 網羅化）→ C・D**、実務的 **E**、正直さ **F**。可換 binop 双方向化は B の第一歩であり、$\equiv_R$ ルールに可換律があっても自動では効かない点（§2.3.1）に注意。詳細な現象分析は [`0701_suboptimal_cause.md`](0701_suboptimal_cause.md) §5 を参照。

---

## 付録 A: 制約数のチェックリスト(実装時の確認用)

SAT エンコーディングの完全性を保証するため、以下が全て揃っていることを実装時に確認する:

- [ ] §2.3: 各 $\circ, \oplus$ の $T$ テーブル構築
- [ ] §2.3.1: 可換 $\oplus$ について $(v_1,v_0)$ と $(v_0,v_1)$ の双方向 edge
- [ ] §5.1: 各 $i$ で命令一意性($\sum_o x_{i,o} = 1$)
- [ ] §5.1: 各 $(i, j)$ でスタック値一意性
- [ ] §5.1: 各 $(i, r)$ でローカル値一意性
- [ ] §5.2: 初期状態のスタックの全位置
- [ ] §5.2: 初期状態のローカルの全スロット
- [ ] §5.2: 最終状態のスタックの全位置
- [ ] §5.2: 最終状態のローカル(non-$\star$ のみ拘束)
- [ ] §5.3: $\mathrm{NOP}$ の状態保存
- [ ] §5.3: 各 $\mathrm{const}_c$ の遷移
- [ ] §5.3: 各 $\mathrm{get}_x, \mathrm{set}_x, \mathrm{tee}_x$ の遷移
- [ ] §5.3: 各単項演算 $\circ$ の遷移（$\top$-sink 全域化: domain 節に $\vee y_{i,0,\top}$）
- [ ] §5.3: 各二項演算 $\oplus$ の遷移（$\top$-sink 全域化: per-$v_1$ domain + 吸収節、sparse 正節 dedup）
- [ ] §5.3: 全非 $\mathrm{set}/\mathrm{tee}$ 命令のローカル不変
- [ ] §5.4: NOP 伝播
- [ ] §11.3: 各不透明命令のオペランド要求・結果生成・スタックシフト・オーバーフロー防止
- [ ] §11.4: storage の厳密 1 回 / 非 storage の高々 1 回
- [ ] §11.5: $\mathit{deplist}$ の各辺の順序制約

これらが全て揃って初めて、§7 の健全性・最適性が成立する。
