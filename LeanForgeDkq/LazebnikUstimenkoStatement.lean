/-
Copyright (c) 2026 Parker Lipscomb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Parker Lipscomb
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Tactic.Ring

/-!
# Statement Formalization: Exact Girth of Lazebnik–Ustimenko Graphs `D(12, F)`

This file formalizes the definitions, graph isomorphism, and girth conjecture statements from:

* **Primary recent papers:**
  * Xiaoyan Cheng, Chen Zhang, Yuansheng Tang, and Ming Xu,
    *The backtrackless circuits of $D(k, q)$ obtained by lifting*, `arXiv:2611.32201v1`
    (submitted 2026-11-24), Section 1 (`cycles-dkq-lifting.tex`, lines 68–114).
  * Felix Lazebnik and Ye Wang, *Some families of graphs, hypergraphs and digraphs defined by
    triangular systems of polynomial equations*, Electron. J. Combin. (2026), `#DS28`,
    `doi:10.37236/14054` (published 2026-02-13), Section 2.1 (p. 5), Section 6 (p. 36),
    Section 6.1 Proposition 38 (p. 37), and Table 7.
* **Original graph construction and conjecture:**
  * Felix Lazebnik and Vasiliy A. Ustimenko, *Explicit construction of graphs with an arbitrary
    large girth and of large size*, Discrete Appl. Math. 60 (1995), 275–284.
  * Zoltán Füredi, Felix Lazebnik, Ákos Seress, Vasiliy A. Ustimenko, and Andrew J. Woldar,
    *Graphs of prescribed girth and bi-degree*, J. Combin. Theory Ser. B 64 (1995), 228–239
    (Conjecture `conmain`).

## Prior Art & Novelty Positioning (Conservative Attribution)

For integer $k \ge 2$, Lazebnik and Ustimenko (1995) established the universal girth lower bound
$\mathrm{girth}(D(k, q)) \ge g_k$ (`#DS28`, Theorem 45), where $g_k = k + 4$ ($k$ even) and
$g_k = k + 5$ ($k$ odd). Füredi, Lazebnik, Seress, Ustimenko, and Woldar (1995) originally
conjectured sharpness for $q \ge 5$, extended to $q \ge 4$ in Lazebnik and Wang (`#DS28`,
Conjecture 46, p. 41; restated as Conjecture `conmain` in `arXiv:2611.32201v1`). At $k = 12$
($g_{12} = 16$), $\mathrm{girth}(D(12, q)) = 16$ was previously known for:

* **$4 \le q \le 97$ (mostly by computer):** listed in Lazebnik–Wang (`#DS28`,
  `doi:10.37236/14054`, Table 7).
* **Even $q$ (characteristic 2):** Cheng–Chen–Tang (2016) (when $g_k/2 = 8 = 2^3$ is a power of
  the characteristic).
* **$q \equiv 1 \pmod 8$ (and $q \equiv 1 \pmod 4$ caveat):** published infinite-family theorems
  unambiguously cover $q \equiv 1 \pmod 8$. While `arXiv:2611.32201v1` (Sec. 1) cites a $4(q - 1)$
  divisibility criterion from Sun (2017) and Xu–Cheng–Tang (2023, Finite Fields Appl. 92,
  `arXiv:2209.01896`) that would cover all $q \equiv 1 \pmod 4$, the formal theorem statements in
  Lazebnik–Wang (`#DS28`, Theorems 50 and 54(iv)) and Xu–Cheng–Tang (2023, Theorem 3) restrict to
  $k \equiv 3 \pmod 4$, so $q \equiv 5 \pmod 8$ for $q > 97$ may also have remained open in
  published form.
* **$q = 7^m$ (characteristic 7):** Zhang–Cheng–Tang–Xu (`arXiv:2611.16470`, Nov 12 2026,
  covering $k = 2(p^r + 1)p^t - 4$ with $p = 7, r = 1, t = 0$).
* **$k = 11$ for all $q \ge 4$:** Xu–Cheng–Tang (2023, Finite Fields Appl. 92, `arXiv:2209.01896`).

In any case, we give one uniform algebraic proof for every prime power $q \ge 4$ (in fact every
field $\mathbb{F}$ with $|\mathbb{F}| \ge 4$), formalized in Lean 4, settling all infinitely many
remaining cases $q \equiv 3 \pmod 4$ with $q > 97$ and $q \neq 7^m$ (e.g., $q = 103, 107, 127,
131, \dots$).

## Verbatim Primary-Source Definitions

* **Target girth (`cycles-dkq-lifting.tex`, lines 71–78):**
  > $g_k = k + 4$ if $k$ is even, and $g_k = k + 5$ if $k$ is odd.
* **Conjecture `conmain` (`cycles-dkq-lifting.tex`, lines 80–82):**
  > For $k \ge 2$ and $q \ge 4$, the girth of $D(k, q)$ is equal to $g_k$.
* **Lazebnik–Wang DS28 addition-form model (`#DS28`, Sec. 2.1 p. 5 & Sec. 6 p. 36):**
  > Points $(p) = (p_1, \ldots, p_k)$ and lines $[l] = [l_1, \ldots, l_k]$ are adjacent iff for all
  > $2 \le i \le k$, $p_i + l_i = p_1 l_1$ ($i = 2$), $p_1 l_2$ ($i = 3$), $-p_{i-2} l_1$
  > ($i \ge 4, i \equiv 0, 1 \pmod 4$), $p_1 l_{i-2}$ ($i \ge 4, i \equiv 2, 3 \pmod 4$).
  > Proposition 38 (Sec. 6.1 p. 37) gives the isomorphic all-positive sign variant
  > `lazebnikUstimenkoD_DS28_pos` with $+p_{i-2} l_1$ for $i \ge 4, i \equiv 0, 1 \pmod 4$.
* **Isomorphic model $\Lambda_{k, q}$ (`cycles-dkq-lifting.tex`, lines 105–112):**
  > $L_k = \{[l] = (l_0, l_1, \ldots, l_k) \in \mathbb{F}_q^{k+1} : l_1 = l_2\}$,
  > $R_k = \{\langle r \rangle = (r_0, r_1, \ldots, r_k) \in \mathbb{F}_q^{k+1} : r_1 = 0\}$,
  > with $[l] \sim \langle r \rangle$ iff for all $2 \le i \le k$,
  > $l_i + r_i = r_0 l_{i-2}$ if $i \equiv 2, 3 \pmod 4$, and $l_0 r_{i-2}$ if
  > $i \equiv 0, 1 \pmod 4$.

## Contents

1. `gK`: the conjectured girth $g_k$.
2. `lazebnikUstimenkoD`: subtraction-form Lazebnik–Ustimenko bipartite graph $D(k, R)$ over any
   commutative ring $R$, together with the verbatim Lazebnik–Wang DS28 addition-form models
   `lazebnikUstimenkoD_DS28` (Sec. 6 p. 36) and `lazebnikUstimenkoD_DS28_pos` (Sec. 6.1 Prop. 38).
3. `lambdaGraph`: Cheng–Xu–Tang bipartite model $\Lambda_{k, R}$ verbatim from eq. `(adj_con)`.
4. Explicit ring-universal graph isomorphisms over every commutative ring $R$:
   `lazebnikUstimenkoD_iso_lambdaGraph`, `lazebnikUstimenkoD_iso_DS28`,
   `lazebnikUstimenkoD_DS28_iso_DS28_pos`, and `lazebnikUstimenkoD_DS28_iso_lambdaGraph`, together
   with their Mathlib girth-invariance corollaries.
5. `girth_eq_of_bounds`: fidelity sanity check linking Mathlib's built-in `SimpleGraph.girth` /
   `SimpleGraph.egirth` directly to shortest simple cycles (`SimpleGraph.Walk.IsCycle`).
6. Headline statement propositions on both `lazebnikUstimenkoD` and the verbatim DS28 models
   `lazebnikUstimenkoD_DS28` / `lazebnikUstimenkoD_DS28_pos`. No girth proofs appear in this
   statement-only module.
-/

@[expose] public section

namespace LeanForgeDkq.LazebnikUstimenko

/-! ### 1. Target Girth Function `g_k` (`cycles-dkq-lifting.tex`, lines 71–78) -/

/-- The Lazebnik–Ustimenko conjectured girth: `g_k = k + 4` for even `k`, `k + 5` for odd `k`. -/
def gK (k : ℕ) : ℕ :=
  if Even k then k + 4 else k + 5

@[simp]
theorem gK_twelve : gK 12 = 16 := by decide

@[simp]
theorem gK_eleven : gK 11 = 16 := by decide

/-! ### 2. Original Lazebnik–Ustimenko Graph `D(k, R)` (Lazebnik–Ustimenko 1995) -/

/-- Incidence relation of the original Lazebnik–Ustimenko graph `D(k, R)` between a line
`x = (x_1, ..., x_k)` (`x ⟨j - 1, _⟩ = x_j`) and a point `y = (y_1, ..., y_k)`
(`y ⟨j - 1, _⟩ = y_j`):
* `j = 2`: `x_2 - y_2 = y_1 * x_1` (`l_{1,1} - p_{1,1} = p_1 l_1`),
* `j = 3`: `x_3 - y_3 = y_1 * x_2` (`l'_{1,2} - p'_{1,2} = p_1 l_{1,1}`),
* `j ≥ 4, j ≡ 2, 3 (mod 4)`: `x_j - y_j = y_1 * x_{j-2}`,
* `j ≥ 4, j ≡ 0, 1 (mod 4)`: `x_j - y_j = x_1 * y_{j-2}`. -/
def luAdj {k : ℕ} {R : Type*} [CommRing R] (x y : Fin k → R) : Prop :=
  ∀ (j : ℕ) (_hj2 : 2 ≤ j) (_hjk : j ≤ k),
    x ⟨j - 1, by omega⟩ - y ⟨j - 1, by omega⟩ =
      if j = 2 then
        y ⟨0, by omega⟩ * x ⟨0, by omega⟩
      else if j = 3 then
        y ⟨0, by omega⟩ * x ⟨1, by omega⟩
      else if j % 4 = 2 ∨ j % 4 = 3 then
        y ⟨0, by omega⟩ * x ⟨j - 3, by omega⟩
      else
        x ⟨0, by omega⟩ * y ⟨j - 3, by omega⟩

/-- The subtraction-form Lazebnik–Ustimenko bipartite graph `D(k, R)` on vertex set
`(Fin k → R) ⊕ (Fin k → R)` (lines on the left, points on the right). -/
def lazebnikUstimenkoD (k : ℕ) (R : Type*) [CommRing R] :
    SimpleGraph ((Fin k → R) ⊕ (Fin k → R)) where
  Adj u v :=
    match u, v with
    | Sum.inl x, Sum.inr y => luAdj x y
    | Sum.inr y, Sum.inl x => luAdj x y
    | Sum.inl _, Sum.inl _ => False
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

/-! ### 2b. Verbatim Lazebnik–Wang DS28 Addition-Form Models (`doi:10.37236/14054`) -/

/-- Incidence relation of the verbatim Lazebnik–Wang DS28 graph `D(k, R)` (Section 2.1 p. 5 and
Section 6 p. 36) between a point `p = (p_1, ..., p_k)` (`p ⟨j - 1, _⟩ = p_j`) and a line
`l = (l_1, ..., l_k)` (`l ⟨j - 1, _⟩ = l_j`):
* `j = 2`: `p_2 + l_2 = p_1 * l_1`,
* `j = 3`: `p_3 + l_3 = p_1 * l_2`,
* `j ≥ 4, j ≡ 0, 1 (mod 4)`: `p_j + l_j = -(p_{j-2} * l_1)`,
* `j ≥ 4, j ≡ 2, 3 (mod 4)`: `p_j + l_j = p_1 * l_{j-2}`. -/
def luDS28Adj {k : ℕ} {R : Type*} [CommRing R] (p l : Fin k → R) : Prop :=
  ∀ (j : ℕ) (_hj2 : 2 ≤ j) (_hjk : j ≤ k),
    p ⟨j - 1, by omega⟩ + l ⟨j - 1, by omega⟩ =
      if j = 2 then
        p ⟨0, by omega⟩ * l ⟨0, by omega⟩
      else if j = 3 then
        p ⟨0, by omega⟩ * l ⟨1, by omega⟩
      else if j % 4 = 0 ∨ j % 4 = 1 then
        -(p ⟨j - 3, by omega⟩ * l ⟨0, by omega⟩)
      else
        p ⟨0, by omega⟩ * l ⟨j - 3, by omega⟩

/-- The verbatim Lazebnik–Wang DS28 bipartite graph `D(k, R)` (`doi:10.37236/14054`, Sec. 2.1 p. 5
and Sec. 6 p. 36) on `(Fin k → R) ⊕ (Fin k → R)` with points `p` on `Sum.inl` and lines `l` on
`Sum.inr`. -/
def lazebnikUstimenkoD_DS28 (k : ℕ) (R : Type*) [CommRing R] :
    SimpleGraph ((Fin k → R) ⊕ (Fin k → R)) where
  Adj u v :=
    match u, v with
    | Sum.inl p, Sum.inr l => luDS28Adj p l
    | Sum.inr l, Sum.inl p => luDS28Adj p l
    | Sum.inl _, Sum.inl _ => False
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

/-- Incidence relation of the all-positive Lazebnik–Wang DS28 variant (Section 6.1 Proposition 38,
p. 37) between a point `p = (p_1, ..., p_k)` and a line `l = (l_1, ..., l_k)`:
* `j = 2`: `p_2 + l_2 = p_1 * l_1`,
* `j = 3`: `p_3 + l_3 = p_1 * l_2`,
* `j ≥ 4, j ≡ 0, 1 (mod 4)`: `p_j + l_j = p_{j-2} * l_1`,
* `j ≥ 4, j ≡ 2, 3 (mod 4)`: `p_j + l_j = p_1 * l_{j-2}`. -/
def luDS28PosAdj {k : ℕ} {R : Type*} [CommRing R] (p l : Fin k → R) : Prop :=
  ∀ (j : ℕ) (_hj2 : 2 ≤ j) (_hjk : j ≤ k),
    p ⟨j - 1, by omega⟩ + l ⟨j - 1, by omega⟩ =
      if j = 2 then
        p ⟨0, by omega⟩ * l ⟨0, by omega⟩
      else if j = 3 then
        p ⟨0, by omega⟩ * l ⟨1, by omega⟩
      else if j % 4 = 0 ∨ j % 4 = 1 then
        p ⟨j - 3, by omega⟩ * l ⟨0, by omega⟩
      else
        p ⟨0, by omega⟩ * l ⟨j - 3, by omega⟩

/-- The all-positive Lazebnik–Wang DS28 bipartite graph (`doi:10.37236/14054`, Sec. 6.1 Prop. 38,
p. 37) on `(Fin k → R) ⊕ (Fin k → R)` with points `p` on `Sum.inl` and lines `l` on `Sum.inr`. -/
def lazebnikUstimenkoD_DS28_pos (k : ℕ) (R : Type*) [CommRing R] :
    SimpleGraph ((Fin k → R) ⊕ (Fin k → R)) where
  Adj u v :=
    match u, v with
    | Sum.inl p, Sum.inr l => luDS28PosAdj p l
    | Sum.inr l, Sum.inl p => luDS28PosAdj p l
    | Sum.inl _, Sum.inl _ => False
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

/-! ### 3. Isomorphic Model `Λ_{k, R}` (`cycles-dkq-lifting.tex`, eq. `(adj_con)`) -/

/-- Left bipartition `L_k = {l ∈ R^{k+1} | l_1 = l_2}` (for `k ≥ 2`). -/
abbrev LambdaLeft (k : ℕ) (R : Type*) :=
  {l : Fin (k + 1) → R // ∀ _h : 2 ≤ k, l ⟨1, by omega⟩ = l ⟨2, by omega⟩}

/-- Right bipartition `R_k = {r ∈ R^{k+1} | r_1 = 0}` (for `k ≥ 1`). -/
abbrev LambdaRight (k : ℕ) (R : Type*) [Zero R] :=
  {r : Fin (k + 1) → R // ∀ _h : 1 ≤ k, r ⟨1, by omega⟩ = 0}

/-- Incidence relation `(adj_con)` of `Λ_{k, R}` (`cycles-dkq-lifting.tex`, lines 107–112):
for all `2 ≤ i ≤ k`, `l_i + r_i = r_0 l_{i-2}` if `i ≡ 2, 3 (mod 4)`, and
`l_i + r_i = l_0 r_{i-2}` if `i ≡ 0, 1 (mod 4)`. -/
def lambdaAdj {k : ℕ} {R : Type*} [CommRing R] (l r : Fin (k + 1) → R) : Prop :=
  ∀ (i : ℕ) (_hi2 : 2 ≤ i) (_hik : i ≤ k),
    l ⟨i, by omega⟩ + r ⟨i, by omega⟩ =
      if i % 4 = 2 ∨ i % 4 = 3 then
        r ⟨0, by omega⟩ * l ⟨i - 2, by omega⟩
      else
        l ⟨0, by omega⟩ * r ⟨i - 2, by omega⟩

/-- The Cheng–Xu–Tang bipartite graph `Λ_{k, R}` on `LambdaLeft k R ⊕ LambdaRight k R`. -/
def lambdaGraph (k : ℕ) (R : Type*) [CommRing R] :
    SimpleGraph (LambdaLeft k R ⊕ LambdaRight k R) where
  Adj u v :=
    match u, v with
    | Sum.inl l, Sum.inr r => lambdaAdj l.1 r.1
    | Sum.inr r, Sum.inl l => lambdaAdj l.1 r.1
    | Sum.inl _, Sum.inl _ => False
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨fun u v h => by cases u <;> cases v <;> exact h⟩
  loopless := ⟨fun u h => by cases u <;> exact h⟩

/-! ### 4. Explicit Ring-Universal Isomorphism `D(k, R) ≃g Λ_{k, R}` -/

/-- Periodic sign `s(j) = (-1)^⌊j/4⌋ ∈ {1, -1}` in any ring `R`. -/
def luSign {R : Type*} [Ring R] (j : ℕ) : R :=
  if (j / 4) % 2 = 1 then -1 else 1

private lemma luSign_mul_self {R : Type*} [Ring R] (j : ℕ) :
    (luSign j : R) * luSign j = 1 := by
  unfold luSign
  split_ifs <;> simp

private lemma luSign_one {R : Type*} [Ring R] : (luSign 1 : R) = 1 := by
  simp [luSign]

private lemma luSign_two {R : Type*} [Ring R] : (luSign 2 : R) = 1 := by
  simp [luSign]

private lemma luSign_three {R : Type*} [Ring R] : (luSign 3 : R) = 1 := by
  simp [luSign]

private lemma luSign_sub_two_mod23 {R : Type*} [Ring R] {j : ℕ}
    (hj : 4 ≤ j) (hmod : j % 4 = 2 ∨ j % 4 = 3) :
    (luSign (j - 2) : R) = luSign j := by
  have hdiv : (j - 2) / 4 = j / 4 := by omega
  simp [luSign, hdiv]

private lemma luSign_sub_two_mod01 {R : Type*} [Ring R] {j : ℕ}
    (hj : 4 ≤ j) (hmod : ¬ (j % 4 = 2 ∨ j % 4 = 3)) :
    (luSign (j - 2) : R) = -luSign j := by
  unfold luSign
  split_ifs with h1 h2
  · omega
  · rfl
  · simp
  · omega

private lemma luSign_mul_cancel {R : Type*} [Ring R] (j : ℕ) {a b : R} :
    luSign j * a = luSign j * b ↔ a = b := by
  constructor
  · intro h
    calc a = luSign j * (luSign j * a) := by rw [← mul_assoc, luSign_mul_self, one_mul]
      _ = luSign j * (luSign j * b) := congrArg _ h
      _ = b := by rw [← mul_assoc, luSign_mul_self, one_mul]
  · intro h
    rw [h]

/-- Forward left coordinate map `x ↦ L` sending `D(k, R)` lines to `Λ_{k, R}` left vertices. -/
def toLambdaLeft {k : ℕ} {R : Type*} [CommRing R] (hk : 2 ≤ k) (x : Fin k → R) :
    LambdaLeft k R :=
  ⟨fun i =>
    if h0 : i.val = 0 then x ⟨0, by omega⟩
    else if h1 : i.val = 1 then x ⟨1, by omega⟩
    else luSign i.val * x ⟨i.val - 1, by omega⟩,
   fun _ => by simp [luSign_two]⟩

/-- Forward right map `y ↦ R` sending `D(k, R)` points to `Λ_{k, R}` right vertices. -/
def toLambdaRight {k : ℕ} {R : Type*} [CommRing R] (hk : 2 ≤ k) (y : Fin k → R) :
    LambdaRight k R :=
  ⟨fun i =>
    if h0 : i.val = 0 then y ⟨0, by omega⟩
    else if h1 : i.val = 1 then 0
    else -(luSign i.val) * y ⟨i.val - 1, by omega⟩,
   fun _ => by simp⟩

/-- Inverse left coordinate map `L ↦ x`. -/
def fromLambdaLeft {k : ℕ} {R : Type*} [CommRing R] (_hk : 2 ≤ k) (l : LambdaLeft k R) :
    Fin k → R :=
  fun m =>
    if h0 : m.val = 0 then l.1 ⟨0, by omega⟩
    else luSign (m.val + 1) * l.1 ⟨m.val + 1, by omega⟩

/-- Inverse right coordinate map `R ↦ y`. -/
def fromLambdaRight {k : ℕ} {R : Type*} [CommRing R] (_hk : 2 ≤ k) (r : LambdaRight k R) :
    Fin k → R :=
  fun m =>
    if h0 : m.val = 0 then r.1 ⟨0, by omega⟩
    else -(luSign (m.val + 1)) * r.1 ⟨m.val + 1, by omega⟩

/-- Explicit ring-universal graph isomorphism `D(k, R) ≃g Λ_{k, R}` for every `k ≥ 2` and every
commutative ring `R` (zero division, works in all characteristics including `char = 2`). -/
def lazebnikUstimenkoD_iso_lambdaGraph {k : ℕ} (hk : 2 ≤ k) (R : Type*) [CommRing R] :
    lazebnikUstimenkoD k R ≃g lambdaGraph k R where
  toFun := Sum.map (toLambdaLeft hk) (toLambdaRight hk)
  invFun := Sum.map (fromLambdaLeft hk) (fromLambdaRight hk)
  left_inv := by
    rintro (x | y)
    · simp only [Sum.map_inl]
      congr 1
      funext m
      by_cases hm0 : m.val = 0
      · simp only [fromLambdaLeft, toLambdaLeft, hm0, ↓reduceDIte]
        congr 1; exact Fin.ext hm0.symm
      · have hne0 : m.val + 1 ≠ 0 := by omega
        have hne1 : m.val + 1 ≠ 1 := by omega
        simp only [fromLambdaLeft, toLambdaLeft, hm0, hne0, hne1, ↓reduceDIte]
        rw [← mul_assoc, luSign_mul_self, one_mul]
        rfl
    · simp only [Sum.map_inr]
      congr 1
      funext m
      by_cases hm0 : m.val = 0
      · simp only [fromLambdaRight, toLambdaRight, hm0, ↓reduceDIte]
        congr 1; exact Fin.ext hm0.symm
      · have hne0 : m.val + 1 ≠ 0 := by omega
        have hne1 : m.val + 1 ≠ 1 := by omega
        simp only [fromLambdaRight, toLambdaRight, hm0, hne0, hne1, ↓reduceDIte]
        rw [← mul_assoc, neg_mul_neg, luSign_mul_self, one_mul]
        rfl
  right_inv := by
    rintro (l | r)
    · simp only [Sum.map_inl]
      congr 1
      apply Subtype.ext
      funext i
      by_cases hi0 : i.val = 0
      · have hidx : (⟨0, by omega⟩ : Fin (k + 1)) = i := Fin.ext hi0.symm
        rw [← hidx]
        simp [toLambdaLeft, fromLambdaLeft]
      by_cases hi1 : i.val = 1
      · have hidx : (⟨1, by omega⟩ : Fin (k + 1)) = i := Fin.ext hi1.symm
        rw [← hidx]
        simp [toLambdaLeft, fromLambdaLeft, luSign_two, l.2 hk]
      · have hm0 : i.val - 1 ≠ 0 := by omega
        have hadd : i.val - 1 + 1 = i.val := by omega
        simp only [toLambdaLeft, fromLambdaLeft, hi0, hi1, hm0, ↓reduceDIte]
        have hidx : (⟨i.val - 1 + 1, by omega⟩ : Fin (k + 1)) = i := Fin.ext hadd
        rw [hidx, hadd, ← mul_assoc, luSign_mul_self, one_mul]
    · simp only [Sum.map_inr]
      congr 1
      apply Subtype.ext
      funext i
      by_cases hi0 : i.val = 0
      · have hidx : (⟨0, by omega⟩ : Fin (k + 1)) = i := Fin.ext hi0.symm
        rw [← hidx]
        simp [toLambdaRight, fromLambdaRight]
      by_cases hi1 : i.val = 1
      · simp only [toLambdaRight, fromLambdaRight, hi1, ↓reduceDIte, one_ne_zero]
        have hr1 : r.1 ⟨1, by omega⟩ = 0 := r.2 (by omega)
        have hidx : (⟨1, by omega⟩ : Fin (k + 1)) = i := Fin.ext hi1.symm
        rw [← hidx, hr1]
      · have hm0 : i.val - 1 ≠ 0 := by omega
        have hadd : i.val - 1 + 1 = i.val := by omega
        simp only [toLambdaRight, fromLambdaRight, hi0, hi1, hm0, ↓reduceDIte]
        have hidx : (⟨i.val - 1 + 1, by omega⟩ : Fin (k + 1)) = i := Fin.ext hadd
        rw [hidx, hadd, ← mul_assoc, neg_mul_neg, luSign_mul_self, one_mul]
  map_rel_iff' := by
    have hadj_iff : ∀ x y : Fin k → R,
        lambdaAdj (toLambdaLeft hk x).1 (toLambdaRight hk y).1 ↔ luAdj x y := by
      intro x y
      constructor <;> intro h j hj2 hjk
      all_goals
        have hj0 : j ≠ 0 := by omega
        have hj1 : j ≠ 1 := by omega
        have hL0 : (toLambdaLeft hk x).1 ⟨0, by omega⟩ = x ⟨0, by omega⟩ := by
          simp [toLambdaLeft]
        have hR0 : (toLambdaRight hk y).1 ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by
          simp [toLambdaRight]
        have hL1 : (toLambdaLeft hk x).1 ⟨1, by omega⟩ = x ⟨1, by omega⟩ := by
          simp [toLambdaLeft]
        have hLj : (toLambdaLeft hk x).1 ⟨j, by omega⟩ =
            luSign j * x ⟨j - 1, by omega⟩ := by simp [toLambdaLeft, hj0, hj1]
        have hRj : (toLambdaRight hk y).1 ⟨j, by omega⟩ =
            -(luSign j) * y ⟨j - 1, by omega⟩ := by simp [toLambdaRight, hj0, hj1]
        have hStep := h j hj2 hjk
      · -- `lambdaAdj → luAdj`
        rw [hLj, hRj, hL0, hR0] at hStep
        by_cases hj_eq2 : j = 2
        · subst hj_eq2
          simp only [↓reduceIte, luSign_two] at hStep ⊢
          rw [hL0] at hStep
          calc x ⟨1, by omega⟩ - y ⟨1, by omega⟩
              = 1 * x ⟨1, by omega⟩ + -1 * y ⟨1, by omega⟩ := by ring
            _ = y ⟨0, by omega⟩ * x ⟨0, by omega⟩ := hStep
        by_cases hj_eq3 : j = 3
        · subst hj_eq3
          have hne32 : (3 : ℕ) ≠ 2 := by decide
          simp only [hne32, ↓reduceIte, luSign_three] at hStep ⊢
          rw [hL1] at hStep
          calc x ⟨2, by omega⟩ - y ⟨2, by omega⟩
              = 1 * x ⟨2, by omega⟩ + -1 * y ⟨2, by omega⟩ := by ring
            _ = y ⟨0, by omega⟩ * x ⟨1, by omega⟩ := hStep
        · have hj4 : 4 ≤ j := by omega
          have hm0 : j - 2 ≠ 0 := by omega
          have hm1 : j - 2 ≠ 1 := by omega
          by_cases hmod : j % 4 = 2 ∨ j % 4 = 3
          · simp only [hj_eq2, hj_eq3, hmod, ↓reduceIte] at hStep ⊢
            have hLjm2 : (toLambdaLeft hk x).1 ⟨j - 2, by omega⟩ =
                luSign (j - 2) * x ⟨j - 3, by omega⟩ := by
              simp only [toLambdaLeft, hm0, hm1, ↓reduceDIte]
              rfl
            rw [hLjm2, luSign_sub_two_mod23 hj4 hmod] at hStep
            apply (luSign_mul_cancel j).mp
            calc luSign j * (x ⟨j - 1, by omega⟩ - y ⟨j - 1, by omega⟩)
                = luSign j * x ⟨j - 1, by omega⟩ +
                    -(luSign j) * y ⟨j - 1, by omega⟩ := by ring
              _ = y ⟨0, by omega⟩ * (luSign j * x ⟨j - 3, by omega⟩) := hStep
              _ = luSign j * (y ⟨0, by omega⟩ * x ⟨j - 3, by omega⟩) := by ring
          · simp only [hj_eq2, hj_eq3, hmod, ↓reduceIte] at hStep ⊢
            have hRjm2 : (toLambdaRight hk y).1 ⟨j - 2, by omega⟩ =
                -(luSign (j - 2)) * y ⟨j - 3, by omega⟩ := by
              simp only [toLambdaRight, hm0, hm1, ↓reduceDIte]
              rfl
            rw [hRjm2, luSign_sub_two_mod01 hj4 hmod] at hStep
            apply (luSign_mul_cancel j).mp
            calc luSign j * (x ⟨j - 1, by omega⟩ - y ⟨j - 1, by omega⟩)
                = luSign j * x ⟨j - 1, by omega⟩ +
                    -(luSign j) * y ⟨j - 1, by omega⟩ := by ring
              _ = x ⟨0, by omega⟩ * (-(-luSign j) * y ⟨j - 3, by omega⟩) := hStep
              _ = luSign j * (x ⟨0, by omega⟩ * y ⟨j - 3, by omega⟩) := by ring
      · -- `luAdj → lambdaAdj`
        rw [hLj, hRj, hL0, hR0]
        by_cases hj_eq2 : j = 2
        · subst hj_eq2
          simp only [↓reduceIte, luSign_two] at hStep ⊢
          rw [hL0]
          calc (1 : R) * x ⟨1, by omega⟩ + -1 * y ⟨1, by omega⟩
              = x ⟨1, by omega⟩ - y ⟨1, by omega⟩ := by ring
            _ = y ⟨0, by omega⟩ * x ⟨0, by omega⟩ := hStep
        by_cases hj_eq3 : j = 3
        · subst hj_eq3
          have hne32 : (3 : ℕ) ≠ 2 := by decide
          simp only [hne32, ↓reduceIte, luSign_three] at hStep ⊢
          rw [hL1]
          calc (1 : R) * x ⟨2, by omega⟩ + -1 * y ⟨2, by omega⟩
              = x ⟨2, by omega⟩ - y ⟨2, by omega⟩ := by ring
            _ = y ⟨0, by omega⟩ * x ⟨1, by omega⟩ := hStep
        · have hj4 : 4 ≤ j := by omega
          have hm0 : j - 2 ≠ 0 := by omega
          have hm1 : j - 2 ≠ 1 := by omega
          by_cases hmod : j % 4 = 2 ∨ j % 4 = 3
          · simp only [hj_eq2, hj_eq3, hmod, ↓reduceIte] at hStep ⊢
            have hLjm2 : (toLambdaLeft hk x).1 ⟨j - 2, by omega⟩ =
                luSign (j - 2) * x ⟨j - 3, by omega⟩ := by
              simp only [toLambdaLeft, hm0, hm1, ↓reduceDIte]
              rfl
            rw [hLjm2, luSign_sub_two_mod23 hj4 hmod]
            calc luSign j * x ⟨j - 1, by omega⟩ + -(luSign j) * y ⟨j - 1, by omega⟩
                = luSign j * (x ⟨j - 1, by omega⟩ - y ⟨j - 1, by omega⟩) := by ring
              _ = luSign j * (y ⟨0, by omega⟩ * x ⟨j - 3, by omega⟩) := congrArg _ hStep
              _ = y ⟨0, by omega⟩ * (luSign j * x ⟨j - 3, by omega⟩) := by ring
          · simp only [hj_eq2, hj_eq3, hmod, ↓reduceIte] at hStep ⊢
            have hRjm2 : (toLambdaRight hk y).1 ⟨j - 2, by omega⟩ =
                -(luSign (j - 2)) * y ⟨j - 3, by omega⟩ := by
              simp only [toLambdaRight, hm0, hm1, ↓reduceDIte]
              rfl
            rw [hRjm2, luSign_sub_two_mod01 hj4 hmod]
            calc luSign j * x ⟨j - 1, by omega⟩ + -(luSign j) * y ⟨j - 1, by omega⟩
                = luSign j * (x ⟨j - 1, by omega⟩ - y ⟨j - 1, by omega⟩) := by ring
              _ = luSign j * (x ⟨0, by omega⟩ * y ⟨j - 3, by omega⟩) := congrArg _ hStep
              _ = x ⟨0, by omega⟩ * (-(-luSign j) * y ⟨j - 3, by omega⟩) := by ring
    intro u v
    rcases u with x | y <;> rcases v with x' | y'
    · exact Iff.rfl
    · exact hadj_iff x y'
    · exact hadj_iff x' y
    · exact Iff.rfl

/-- Girth invariance under the ring-universal isomorphism `D(k, R) ≃g Λ_{k, R}`. -/
theorem lazebnikUstimenkoD_egirth_eq_lambdaGraph_egirth {k : ℕ} (hk : 2 ≤ k)
    (R : Type*) [CommRing R] :
    (lazebnikUstimenkoD k R).egirth = (lambdaGraph k R).egirth :=
  (lazebnikUstimenkoD_iso_lambdaGraph hk R).egirth_eq

theorem lazebnikUstimenkoD_girth_eq_lambdaGraph_girth {k : ℕ} (hk : 2 ≤ k)
    (R : Type*) [CommRing R] :
    (lazebnikUstimenkoD k R).girth = (lambdaGraph k R).girth :=
  (lazebnikUstimenkoD_iso_lambdaGraph hk R).girth_eq

/-! ### 4b. Ring-Universal Isomorphisms with Lazebnik–Wang DS28 Models -/

/-- Negate all coordinates after index `0` (`p_1 = y_1`, `p_j = -y_j` for `j ≥ 2`). -/
def ds28NegTail {k : ℕ} {R : Type*} [CommRing R] (y : Fin k → R) : Fin k → R :=
  fun m => if m.val = 0 then y m else -y m

private lemma ds28NegTail_invol {k : ℕ} {R : Type*} [CommRing R] (y : Fin k → R) :
    ds28NegTail (ds28NegTail y) = y := by
  funext m
  dsimp [ds28NegTail]
  split_ifs <;> simp

/-- Explicit ring-universal graph isomorphism between the subtraction-form `D(k, R)` and the
verbatim Lazebnik–Wang DS28 addition-form graph `lazebnikUstimenkoD_DS28 k R` over every
commutative ring `R` (swapping bipartition sides and setting `p_1 = y_1`, `p_j = -y_j` for
`j ≥ 2`, `l_j = x_j`). -/
def lazebnikUstimenkoD_iso_DS28 (k : ℕ) (R : Type*) [CommRing R] :
    lazebnikUstimenkoD k R ≃g lazebnikUstimenkoD_DS28 k R where
  toFun u :=
    match u with
    | Sum.inl x => Sum.inr x
    | Sum.inr y => Sum.inl (ds28NegTail y)
  invFun u :=
    match u with
    | Sum.inl p => Sum.inr (ds28NegTail p)
    | Sum.inr l => Sum.inl l
  left_inv := by
    rintro (x | y)
    · rfl
    · exact congrArg Sum.inr (ds28NegTail_invol y)
  right_inv := by
    rintro (p | l)
    · exact congrArg Sum.inl (ds28NegTail_invol p)
    · rfl
  map_rel_iff' := by
    have hadj_iff : ∀ (x y : Fin k → R), luDS28Adj (ds28NegTail y) x ↔ luAdj x y := by
      intro x y
      refine forall₃_congr fun j hj2 hjk => ?_
      have hjm1 : j - 1 ≠ 0 := by omega
      have h0 : (ds28NegTail y) ⟨0, by omega⟩ = y ⟨0, by omega⟩ := by
        simp [ds28NegTail]
      have hjm1_eq : (ds28NegTail y) ⟨j - 1, by omega⟩ = -y ⟨j - 1, by omega⟩ := by
        simp [ds28NegTail, hjm1]
      have hLHS : -y ⟨j - 1, by omega⟩ + x ⟨j - 1, by omega⟩ =
          x ⟨j - 1, by omega⟩ - y ⟨j - 1, by omega⟩ := by ring
      rw [hjm1_eq, h0, hLHS]
      by_cases hj2' : j = 2
      · subst hj2'
        simp only [↓reduceIte]
      by_cases hj3' : j = 3
      · subst hj3'
        have h32 : (3 : ℕ) ≠ 2 := by decide
        simp only [h32, ↓reduceIte]
      · have hj4 : 4 ≤ j := by omega
        have hjm3 : j - 3 ≠ 0 := by omega
        have hjm3_eq : (ds28NegTail y) ⟨j - 3, by omega⟩ = -y ⟨j - 3, by omega⟩ := by
          simp [ds28NegTail, hjm3]
        by_cases hmod01 : j % 4 = 0 ∨ j % 4 = 1
        · have hnot23 : ¬ (j % 4 = 2 ∨ j % 4 = 3) := by omega
          have hRHS : -(-y ⟨j - 3, by omega⟩ * x ⟨0, by omega⟩) =
              x ⟨0, by omega⟩ * y ⟨j - 3, by omega⟩ := by ring
          simp only [hj2', hj3', hmod01, hnot23, ↓reduceIte, hjm3_eq, hRHS]
        · have hmod23 : j % 4 = 2 ∨ j % 4 = 3 := by omega
          simp only [hj2', hj3', hmod01, hmod23, ↓reduceIte]
    intro u v
    rcases u with x | y <;> rcases v with x' | y'
    · exact Iff.rfl
    · exact hadj_iff x y'
    · exact hadj_iff x' y
    · exact Iff.rfl

/-- Periodic coordinate sign scaling `v_j ↦ (-1)^⌊j/4⌋ v_j` realizing DS28 Proposition 38. -/
def ds28SignVec {k : ℕ} {R : Type*} [CommRing R] (v : Fin k → R) : Fin k → R :=
  fun m => luSign (m.val + 1) * v m

private lemma ds28SignVec_invol {k : ℕ} {R : Type*} [CommRing R] (v : Fin k → R) :
    ds28SignVec (ds28SignVec v) = v := by
  funext m
  simp [ds28SignVec, ← mul_assoc, luSign_mul_self]

/-- Explicit ring-universal graph isomorphism `lazebnikUstimenkoD_DS28 k R ≃g
lazebnikUstimenkoD_DS28_pos k R` (Lazebnik–Wang DS28, Section 6.1 Proposition 38, p. 37) over
every commutative ring `R`. -/
def lazebnikUstimenkoD_DS28_iso_DS28_pos (k : ℕ) (R : Type*) [CommRing R] :
    lazebnikUstimenkoD_DS28 k R ≃g lazebnikUstimenkoD_DS28_pos k R where
  toFun := Sum.map ds28SignVec ds28SignVec
  invFun := Sum.map ds28SignVec ds28SignVec
  left_inv := by
    rintro (p | l)
    · simp only [Sum.map_inl, ds28SignVec_invol]
    · simp only [Sum.map_inr, ds28SignVec_invol]
  right_inv := by
    rintro (p | l)
    · simp only [Sum.map_inl, ds28SignVec_invol]
    · simp only [Sum.map_inr, ds28SignVec_invol]
  map_rel_iff' := by
    have hadj_iff : ∀ (p l : Fin k → R),
        luDS28PosAdj (ds28SignVec p) (ds28SignVec l) ↔ luDS28Adj p l := by
      intro p l
      refine forall₃_congr fun j hj2 hjk => ?_
      have hidx1 : j - 1 + 1 = j := by omega
      have hLHS : ds28SignVec p ⟨j - 1, by omega⟩ + ds28SignVec l ⟨j - 1, by omega⟩ =
          luSign j * (p ⟨j - 1, by omega⟩ + l ⟨j - 1, by omega⟩) := by
        simp only [ds28SignVec, hidx1]
        ring
      rw [hLHS]
      by_cases hj2' : j = 2
      · subst hj2'
        simp only [↓reduceIte]
        have hRHS : ds28SignVec p ⟨0, by omega⟩ * ds28SignVec l ⟨0, by omega⟩ =
            luSign 2 * (p ⟨0, by omega⟩ * l ⟨0, by omega⟩) := by
          dsimp only [ds28SignVec]
          rw [luSign_one, luSign_two]
          ring
        rw [hRHS, luSign_mul_cancel]
      by_cases hj3' : j = 3
      · subst hj3'
        have h32 : (3 : ℕ) ≠ 2 := by decide
        simp only [h32, ↓reduceIte]
        have hRHS : ds28SignVec p ⟨0, by omega⟩ * ds28SignVec l ⟨1, by omega⟩ =
            luSign 3 * (p ⟨0, by omega⟩ * l ⟨1, by omega⟩) := by
          dsimp only [ds28SignVec]
          rw [luSign_one, luSign_two, luSign_three]
          ring
        rw [hRHS, luSign_mul_cancel]
      · have hj4 : 4 ≤ j := by omega
        have hidx3 : j - 3 + 1 = j - 2 := by omega
        by_cases hmod01 : j % 4 = 0 ∨ j % 4 = 1
        · have hnot23 : ¬ (j % 4 = 2 ∨ j % 4 = 3) := by omega
          simp only [hj2', hj3', hmod01, ↓reduceIte]
          have hRHS : ds28SignVec p ⟨j - 3, by omega⟩ * ds28SignVec l ⟨0, by omega⟩ =
              luSign j * -(p ⟨j - 3, by omega⟩ * l ⟨0, by omega⟩) := by
            dsimp only [ds28SignVec]
            rw [hidx3, luSign_one, luSign_sub_two_mod01 hj4 hnot23]
            ring
          rw [hRHS, luSign_mul_cancel]
        · have hmod23 : j % 4 = 2 ∨ j % 4 = 3 := by omega
          simp only [hj2', hj3', hmod01, ↓reduceIte]
          have hRHS : ds28SignVec p ⟨0, by omega⟩ * ds28SignVec l ⟨j - 3, by omega⟩ =
              luSign j * (p ⟨0, by omega⟩ * l ⟨j - 3, by omega⟩) := by
            dsimp only [ds28SignVec]
            rw [hidx3, luSign_one, luSign_sub_two_mod23 hj4 hmod23]
            ring
          rw [hRHS, luSign_mul_cancel]
    intro u v
    rcases u with p | l <;> rcases v with p' | l'
    · exact Iff.rfl
    · exact hadj_iff p l'
    · exact hadj_iff p' l
    · exact Iff.rfl

/-- Explicit ring-universal graph isomorphism `lazebnikUstimenkoD_DS28 k R ≃g lambdaGraph k R`
for every `k ≥ 2` and every commutative ring `R`. -/
def lazebnikUstimenkoD_DS28_iso_lambdaGraph {k : ℕ} (hk : 2 ≤ k) (R : Type*) [CommRing R] :
    lazebnikUstimenkoD_DS28 k R ≃g lambdaGraph k R :=
  (lazebnikUstimenkoD_iso_DS28 k R).symm.trans (lazebnikUstimenkoD_iso_lambdaGraph hk R)

/-- Extended girth invariance between `lazebnikUstimenkoD` and `lazebnikUstimenkoD_DS28`. -/
theorem lazebnikUstimenkoD_egirth_eq_DS28_egirth (k : ℕ) (R : Type*) [CommRing R] :
    (lazebnikUstimenkoD k R).egirth = (lazebnikUstimenkoD_DS28 k R).egirth :=
  (lazebnikUstimenkoD_iso_DS28 k R).egirth_eq

/-- Girth invariance between `lazebnikUstimenkoD` and `lazebnikUstimenkoD_DS28`. -/
theorem lazebnikUstimenkoD_girth_eq_DS28_girth (k : ℕ) (R : Type*) [CommRing R] :
    (lazebnikUstimenkoD k R).girth = (lazebnikUstimenkoD_DS28 k R).girth :=
  (lazebnikUstimenkoD_iso_DS28 k R).girth_eq

/-- Girth invariance between `lazebnikUstimenkoD_DS28` and `lazebnikUstimenkoD_DS28_pos`. -/
theorem lazebnikUstimenkoD_DS28_girth_eq_DS28_pos_girth (k : ℕ) (R : Type*) [CommRing R] :
    (lazebnikUstimenkoD_DS28 k R).girth = (lazebnikUstimenkoD_DS28_pos k R).girth :=
  (lazebnikUstimenkoD_DS28_iso_DS28_pos k R).girth_eq

/-! ### 5. Fidelity Sanity Check on Mathlib's `SimpleGraph.girth` -/

/-- A simple graph has exact extended girth `n` (and hence exact `SimpleGraph.girth = n`)
whenever every simple cycle has length `≥ n` and there exists a simple cycle of length `n`. -/
theorem girth_eq_of_bounds {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hlb : ∀ (a : V) (w : G.Walk a a), w.IsCycle → n ≤ w.length)
    (hub : ∃ (a : V) (w : G.Walk a a), w.IsCycle ∧ w.length = n) :
    G.egirth = n ∧ G.girth = n := by
  have hle : (n : ℕ∞) ≤ G.egirth :=
    SimpleGraph.le_egirth.mpr fun a w hw => Nat.cast_le.mpr (hlb a w hw)
  obtain ⟨a, w, hw, hlen⟩ := hub
  have hge : G.egirth ≤ n := hlen ▸ hw.egirth_le_length
  have heg : G.egirth = n := le_antisymm hge hle
  exact ⟨heg, by simp [SimpleGraph.girth, heg]⟩

/-- Positive `SimpleGraph.girth` is non-vacuous: `G.girth = n` with `0 < n` implies
`G.egirth = n` (in particular `G` is not acyclic). -/
theorem egirth_eq_of_girth_eq_pos {V : Type*} {G : SimpleGraph V} {n : ℕ}
    (hn : 0 < n) (hg : G.girth = n) : G.egirth = n := by
  cases h : G.egirth with
  | top =>
    simp [SimpleGraph.girth, h] at hg
    omega
  | coe m =>
    simp only [SimpleGraph.girth, h, ENat.toNat_natCast] at hg
    exact congrArg Nat.cast hg

/-! ### 6. Headline Theorem Statements (Conjecture `conmain` at `k = 12`) -/

/-- **Universal Girth Lower Bound:** For every `k ≥ 2` and every field `F`, every cycle in
`D(k, F)` has length at least `gK k` (`(gK k : ℕ∞) ≤ (lazebnikUstimenkoD k F).egirth`). -/
def LazebnikUstimenkoGirthLowerBoundStatement.{u} : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (F : Type u) [Field F],
    (gK k : ℕ∞) ≤ (lazebnikUstimenkoD k F).egirth

/-- **Verbatim Finite-Field Conjecture `conmain` at `k = 12` (`cycles-dkq-lifting.tex`, L80–82):**
For every finite field `F` of prime-power order `q = |F| ≥ 4`, the exact girth of the original
Lazebnik–Ustimenko graph `D(12, F)` equals `gK 12 = 16`. -/
def LazebnikUstimenkoD12FiniteFieldStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    4 ≤ Fintype.card F →
    (lazebnikUstimenkoD 12 F).girth = gK 12

/-- **Residue Class `q ≡ 3 (mod 4)` (`k = 12`):** For every finite field `F` with
`4 ≤ Fintype.card F` and `Fintype.card F % 4 = 3`, `(lazebnikUstimenkoD 12 F).girth = 16`.
While `q ≤ 97` was previously known (mostly by computer, Lazebnik–Wang `#DS28` Table 7) and
`q = 7^m` by `arXiv:2611.16470`, this settles all infinitely many remaining cases `q ≡ 3 (mod 4)`
with `q > 97` and `q ≠ 7^m` (e.g., `q = 103, 107, 127, 131, ...`). -/
def LazebnikUstimenkoD12OpenClassStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    4 ≤ Fintype.card F →
    Fintype.card F % 4 = 3 →
    (lazebnikUstimenkoD 12 F).girth = 16

/-- **Stronger All-Fields Statement (`k = 12` and `k = 11`):** For every field `F` (finite or
infinite) with at least 4 elements (`(4 : ℕ∞) ≤ ENat.card F`), both `D(12, F)` and `D(11, F)`
have exact girth `16` (equivalently `egirth = 16`). -/
def LazebnikUstimenkoD12AllFieldsStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F],
    (4 : ℕ∞) ≤ ENat.card F →
    (lazebnikUstimenkoD 12 F).girth = 16 ∧
    (lazebnikUstimenkoD 11 F).girth = 16

/-- **Universal Girth Lower Bound (Verbatim DS28 Model):** For every `k ≥ 2` and every field `F`,
every cycle in `lazebnikUstimenkoD_DS28 k F` has length at least `gK k`. -/
def LazebnikUstimenkoDS28GirthLowerBoundStatement.{u} : Prop :=
  ∀ (k : ℕ), 2 ≤ k → ∀ (F : Type u) [Field F],
    (gK k : ℕ∞) ≤ (lazebnikUstimenkoD_DS28 k F).egirth

/-- **All-Fields Statement (Verbatim DS28 Model, `k = 12` and `k = 11`):** For every field `F`
with `(4 : ℕ∞) ≤ ENat.card F`, both `lazebnikUstimenkoD_DS28 12 F` and
`lazebnikUstimenkoD_DS28 11 F` have exact girth `16`. -/
def LazebnikUstimenkoDS28D12AllFieldsStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F],
    (4 : ℕ∞) ≤ ENat.card F →
    (lazebnikUstimenkoD_DS28 12 F).girth = 16 ∧
    (lazebnikUstimenkoD_DS28 11 F).girth = 16

/-- **Finite-Field Conjecture `conmain` at `k = 12` (Verbatim DS28 Model):** For every finite field
`F` with `4 ≤ Fintype.card F`, `(lazebnikUstimenkoD_DS28 12 F).girth = gK 12`. -/
def LazebnikUstimenkoDS28D12FiniteFieldStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    4 ≤ Fintype.card F →
    (lazebnikUstimenkoD_DS28 12 F).girth = gK 12

/-- **Finite-Field Conjecture `conmain` at `k = 12` (DS28 Prop. 38 All-Positive Model):** For every
finite field `F` with `4 ≤ Fintype.card F`, `(lazebnikUstimenkoD_DS28_pos 12 F).girth = gK 12`. -/
def LazebnikUstimenkoDS28PosD12FiniteFieldStatement.{u} : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F],
    4 ≤ Fintype.card F →
    (lazebnikUstimenkoD_DS28_pos 12 F).girth = gK 12

end LeanForgeDkq.LazebnikUstimenko
