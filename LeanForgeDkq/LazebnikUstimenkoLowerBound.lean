/-
Copyright (c) 2026 Parker Lipscomb. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Parker Lipscomb
-/
module

public import LeanForgeDkq.LazebnikUstimenkoStatement
public import Mathlib.Algebra.Polynomial.Coeff

/-!
# Universal Girth Lower Bound for Lazebnik–Ustimenko Graphs `D(k, F)`

This file proves the universal girth lower bound:
for every integer `k ≥ 2` and every field `F`,
`(gK k : ℕ∞) ≤ (lazebnikUstimenkoD k F).egirth`.

## Proof Architecture (Affine-Invariant `SL₂(F[z])` State Matrix)

Instead of constructing edge-transitivity automorphisms `θ_e`, we attach directly to any
adjacent pair `(l, r)` in `Λ_{k, F}` the `2 × 2` polynomial state matrix
`S(l, r; z) ∈ M₂(F[z])`:
* `a = 1 + ∑_{4t+2 ≤ k} r_{4t+2} z^{2t+2}` (even, constant term `1`),
* `b = r_0 z + ∑_{4t+3 ≤ k} r_{4t+3} z^{2t+3}` (odd),
* `c = ∑_{4t ≤ k} l_{4t} z^{2t+1}` (odd),
* `d = 1 + ∑_{4t+1 ≤ k} l_{4t+1} z^{2t+2}` (even, constant term `1`).

Along any backtrackless step `[l] ~ ⟨r⟩ ~ [l']` (`u = l'_0 - l_0 ≠ 0`) and
`⟨r⟩ ~ [l'] ~ ⟨r'⟩` (`v = r'_0 - r_0 ≠ 0`), subtracting the adjacency equations `(adj_con)` yields
`S(l', r) ≡ L(u) · S(l, r)` and `S(l', r') ≡ U(v) · S(l', r)` modulo the exact entrywise degree
profile `(N00 k, N01 k, N10 k, N11 k)`.

For any simple cycle of length `2m` in `Λ_{k, F}`, multiplying around the cycle gives
`T_m · S_0 ≡ S_0` where `T_m = ∏ U(v_j) L(u_j) ∈ SL₂(F[z])`. Since `S_0(0) = I_2` and
`det T_m = 1`, this forces `T_m ≡ I_2` to the exact required power of `z` in all four residue
classes `k mod 4`. Splitting the `2m`-letter alternating word `T_m = A · B` into two halves of
length `m` then contradicts `2m < gK k`.

## Main Result

* `LeanForgeDkq.LazebnikUstimenko.lazebnikUstimenko_girth_lower_bound`:
  proves `LazebnikUstimenkoGirthLowerBoundStatement.{u}`.
-/

@[expose] public section

noncomputable section

namespace LeanForgeDkq.LazebnikUstimenko

open Polynomial

/-! ### 1. Elementary `2 × 2` Polynomial Matrix Algebra (`SL₂(F[z])`) -/

/-- A `2 × 2` matrix over `F[X]`. -/
structure PolyMat2 (F : Type*) [CommRing F] where
  a : F[X]
  b : F[X]
  c : F[X]
  d : F[X]

namespace PolyMat2

variable {F : Type*} [CommRing F]

theorem ext {M N : PolyMat2 F} (ha : M.a = N.a) (hb : M.b = N.b)
    (hc : M.c = N.c) (hd : M.d = N.d) : M = N := by
  cases M; cases N; congr

/-- Identity matrix `I₂`. -/
def one : PolyMat2 F := ⟨1, 0, 0, 1⟩

/-- Matrix multiplication. -/
def mul (M N : PolyMat2 F) : PolyMat2 F :=
  ⟨M.a * N.a + M.b * N.c, M.a * N.b + M.b * N.d,
   M.c * N.a + M.d * N.c, M.c * N.b + M.d * N.d⟩

/-- Entrywise difference `M - N`. -/
def sub (M N : PolyMat2 F) : PolyMat2 F :=
  ⟨M.a - N.a, M.b - N.b, M.c - N.c, M.d - N.d⟩

/-- Determinant `ad - bc`. -/
def det (M : PolyMat2 F) : F[X] := M.a * M.d - M.b * M.c

/-- Classical adjugate (inverse when `det M = 1`). -/
def adj (M : PolyMat2 F) : PolyMat2 F := ⟨M.d, -M.b, -M.c, M.a⟩

/-- Conjugation by `[[0, 1], [1, 0]]`, swapping `a ↔ d` and `b ↔ c`. -/
def swap (M : PolyMat2 F) : PolyMat2 F := ⟨M.d, M.c, M.b, M.a⟩

/-- Lower unipotent step `L(u) = [[1, 0], [u X, 1]]`. -/
def stepL (u : F) : PolyMat2 F := ⟨1, 0, C u * X, 1⟩

/-- Upper unipotent step `U(v) = [[1, v X], [0, 1]]`. -/
def stepU (v : F) : PolyMat2 F := ⟨1, C v * X, 0, 1⟩

private lemma mat_mul_assoc (M N K : PolyMat2 F) :
    mul (mul M N) K = mul M (mul N K) := by
  apply PolyMat2.ext <;> simp only [mul] <;> ring

private lemma mat_one_mul (M : PolyMat2 F) : mul one M = M := by
  apply PolyMat2.ext <;> simp only [mul, one] <;> ring

private lemma mat_mul_one (M : PolyMat2 F) : mul M one = M := by
  apply PolyMat2.ext <;> simp only [mul, one] <;> ring

private lemma det_one : det (one : PolyMat2 F) = 1 := by
  simp only [det, one]; ring

private lemma det_mul (M N : PolyMat2 F) : det (mul M N) = det M * det N := by
  simp only [det, mul]; ring

private lemma det_stepL (u : F) : det (stepL u) = 1 := by
  simp only [det, stepL]; ring

private lemma det_stepU (v : F) : det (stepU v) = 1 := by
  simp only [det, stepU]; ring

private lemma adj_mul_self {M : PolyMat2 F} (hdet : det M = 1) :
    mul (adj M) M = one := by
  apply PolyMat2.ext <;> simp only [mul, adj, one]
  · calc M.d * M.a + -M.b * M.c = M.a * M.d - M.b * M.c := by ring
      _ = 1 := hdet
  · ring
  · ring
  · calc -M.c * M.b + M.a * M.d = M.a * M.d - M.b * M.c := by ring
      _ = 1 := hdet

private lemma mul_adj_self {M : PolyMat2 F} (hdet : det M = 1) :
    mul M (adj M) = one := by
  apply PolyMat2.ext <;> simp only [mul, adj, one]
  · calc M.a * M.d + M.b * -M.c = M.a * M.d - M.b * M.c := by ring
      _ = 1 := hdet
  · ring
  · ring
  · calc M.c * -M.b + M.d * M.a = M.a * M.d - M.b * M.c := by ring
      _ = 1 := hdet

private lemma mat_mul_sub (M N K : PolyMat2 F) :
    mul M (sub N K) = sub (mul M N) (mul M K) := by
  apply PolyMat2.ext <;> simp only [mul, sub] <;> ring

private lemma swap_one : swap (one : PolyMat2 F) = one := by
  apply PolyMat2.ext <;> rfl

private lemma swap_swap (M : PolyMat2 F) : swap (swap M) = M := by
  apply PolyMat2.ext <;> rfl

private lemma swap_mul (M N : PolyMat2 F) :
    swap (mul M N) = mul (swap M) (swap N) := by
  apply PolyMat2.ext <;> simp only [swap, mul] <;> ring

private lemma swap_stepU (w : F) : swap (stepU w) = stepL w := by
  apply PolyMat2.ext <;> rfl

private lemma swap_stepL (w : F) : swap (stepL w) = stepU w := by
  apply PolyMat2.ext <;> rfl

private lemma det_swap (M : PolyMat2 F) : det (swap M) = det M := by
  simp only [det, swap]; ring

/-! ### 2. Alternating Unipotent Words `wordU` / `wordL` -/

/-- Alternating word starting with `U`: `U(w₁) · L(w₂) · U(w₃) · ...`. -/
def wordU : List F → PolyMat2 F
  | [] => one
  | w :: ws => mul (stepU w) (swap (wordU ws))

/-- Alternating word starting with `L`: `L(w₁) · U(w₂) · L(w₃) · ...`. -/
def wordL (ws : List F) : PolyMat2 F := swap (wordU ws)

private lemma wordU_nil : wordU ([] : List F) = one := rfl

private lemma wordL_nil : wordL ([] : List F) = one := swap_one

private lemma wordU_cons (w : F) (ws : List F) :
    wordU (w :: ws) = mul (stepU w) (wordL ws) := rfl

private lemma wordL_cons (w : F) (ws : List F) :
    wordL (w :: ws) = mul (stepL w) (wordU ws) := by
  simp only [wordL, wordU, swap_mul, swap_stepU, swap_swap]

private lemma det_wordU (ws : List F) : det (wordU ws) = 1 := by
  induction ws with
  | nil => exact det_one
  | cons w ws ih =>
    simp only [wordU, det_mul, det_stepU, det_swap, ih, mul_one]

private lemma det_wordL (ws : List F) : det (wordL ws) = 1 := by
  rw [wordL, det_swap, det_wordU]

private lemma wordU_append (xs ys : List F) :
    wordU (xs ++ ys) =
      if Even xs.length then mul (wordU xs) (wordU ys)
      else mul (wordU xs) (wordL ys) := by
  induction xs with
  | nil =>
    simp [wordU_nil, mat_one_mul]
  | cons x xs ih =>
    simp only [List.cons_append, wordU_cons, wordL, List.length_cons]
    rw [ih]
    by_cases h : Even xs.length
    · have hodd : ¬ Even (xs.length + 1) := by
        obtain ⟨k, hk⟩ := h; intro ⟨m, hm⟩; omega
      simp only [h, hodd, ↓reduceIte, swap_mul, mat_mul_assoc]
    · have hev : Even (xs.length + 1) := by
        rw [Nat.not_even_iff_odd] at h
        obtain ⟨k, hk⟩ := h
        exact ⟨k + 1, by omega⟩
      simp only [h, hev, ↓reduceIte, wordL, swap_mul, swap_swap, mat_mul_assoc]

/-- Parity invariant of `wordU ws`: diagonal entries are even in `X`, off-diagonal are odd. -/
private lemma wordU_parity (ws : List F) :
    (∀ j, (wordU ws).a.coeff (2 * j + 1) = 0) ∧
    (∀ j, (wordU ws).b.coeff (2 * j) = 0) ∧
    (∀ j, (wordU ws).c.coeff (2 * j) = 0) ∧
    (∀ j, (wordU ws).d.coeff (2 * j + 1) = 0) := by
  induction ws with
  | nil =>
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro j
    · simp [wordU, one, coeff_one]
    · simp [wordU, one]
    · simp [wordU, one]
    · simp [wordU, one, coeff_one]
  | cons w ws ih =>
    rcases ih with ⟨ha, hb, hc, hd⟩
    simp only [wordU, mul, stepU, swap, one_mul, zero_mul, zero_add]
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      rw [coeff_add, hd j, mul_assoc, coeff_C_mul, coeff_X_mul, hb j]
      ring
    · intro j
      cases j with
      | zero =>
        rw [coeff_add, hc 0, mul_assoc, coeff_C_mul, coeff_X_mul_zero]
        ring
      | succ j' =>
        have h2 : 2 * (j' + 1) = (2 * j' + 1) + 1 := by omega
        rw [h2, coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, ha j']
        have hc' := hc (j' + 1)
        rw [h2] at hc'
        rw [hc']
        ring
    · intro j; exact hb j
    · intro j; exact ha j

/-- Exact degree bounds and leading coefficients of `wordU ws` by length parity. -/
private lemma wordU_deg_lead (ws : List F) :
    (Even ws.length →
      (wordU ws).a.coeff ws.length = ws.prod ∧
      (∀ d, ws.length < d → (wordU ws).a.coeff d = 0) ∧
      (∀ d, ws.length ≤ d → (wordU ws).b.coeff d = 0) ∧
      (∀ d, ws.length ≤ d → (wordU ws).c.coeff d = 0) ∧
      (∀ d, ws.length ≤ d + 1 → (ws.length = 0 → 0 < d) → (wordU ws).d.coeff d = 0)) ∧
    (¬ Even ws.length →
      (∀ d, ws.length ≤ d → (wordU ws).a.coeff d = 0) ∧
      (wordU ws).b.coeff ws.length = ws.prod ∧
      (∀ d, ws.length < d → (wordU ws).b.coeff d = 0) ∧
      (∀ d, ws.length ≤ d + 1 → (wordU ws).c.coeff d = 0) ∧
      (∀ d, ws.length ≤ d → (wordU ws).d.coeff d = 0)) := by
  induction ws with
  | nil =>
    constructor
    · intro _
      refine ⟨by simp [wordU, one], ?_, ?_, ?_, ?_⟩
      · intro d hd; simp only [wordU, one, coeff_one, List.length_nil] at hd ⊢
        simp [Nat.ne_of_gt hd]
      · intro d _; simp [wordU, one]
      · intro d _; simp [wordU, one]
      · intro d _ hd0
        have hpos : 0 < d := hd0 rfl
        simp only [wordU, one, coeff_one]
        simp [Nat.ne_of_gt hpos]
    · intro h; exact (h ⟨0, rfl⟩).elim
  | cons w ws ih =>
    rcases ih with ⟨ihE, ihO⟩
    simp only [wordU, mul, stepU, swap, one_mul, zero_mul, zero_add,
      List.length_cons, List.prod_cons]
    constructor
    · intro hev
      have hodd : ¬ Even ws.length := by
        obtain ⟨k, hk⟩ := hev; intro ⟨m, hm⟩; omega
      obtain ⟨ha, hb_lead, hb_hi, hc, hd⟩ := ihO hodd
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, hb_lead,
          hd (ws.length + 1) (by omega), zero_add]
      · intro d hgt
        cases d with
        | zero => omega
        | succ d' =>
          rw [coeff_add, hd (d' + 1) (by omega), mul_assoc, coeff_C_mul, coeff_X_mul,
            hb_hi d' (by omega), mul_zero, add_zero]
      · intro d hge
        cases d with
        | zero => omega
        | succ d' =>
          rw [coeff_add, hc (d' + 1) (by omega), mul_assoc, coeff_C_mul, coeff_X_mul,
            ha d' (by omega), mul_zero, add_zero]
      · intro d hge
        exact hb_hi d (by omega)
      · intro d hge _
        exact ha d (by omega)
    · intro hodd
      have hev : Even ws.length := by
        rw [Nat.not_even_iff_odd] at hodd
        obtain ⟨k, hk⟩ := hodd
        exact ⟨k, by omega⟩
      obtain ⟨ha_lead, ha_hi, hb, hc, hd⟩ := ihE hev
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · intro d hge
        cases d with
        | zero => omega
        | succ d' =>
          rw [coeff_add, mul_assoc, coeff_C_mul, coeff_X_mul, hb d' (by omega), mul_zero, add_zero]
          exact hd (d' + 1) (by omega) (fun _ => by omega)
      · rw [coeff_add, hc (ws.length + 1) (by omega), zero_add, mul_assoc, coeff_C_mul,
          coeff_X_mul, ha_lead]
      · intro d hgt
        cases d with
        | zero => omega
        | succ d' =>
          rw [coeff_add, hc (d' + 1) (by omega), zero_add, mul_assoc, coeff_C_mul, coeff_X_mul,
            ha_hi d' (by omega), mul_zero]
      · intro d hge
        exact hb d (by omega)
      · intro d hge
        exact ha_hi d (by omega)

/-- Universal upper degree bound: every entry of `wordU ws` vanishes strictly above `ws.length`. -/
private lemma wordU_coeff_eq_zero_of_gt (ws : List F) {d : ℕ} (hd : ws.length < d) :
    (wordU ws).a.coeff d = 0 ∧ (wordU ws).b.coeff d = 0 ∧
    (wordU ws).c.coeff d = 0 ∧ (wordU ws).d.coeff d = 0 := by
  obtain ⟨hE, hO⟩ := wordU_deg_lead ws
  by_cases hev : Even ws.length
  · obtain ⟨_, ha, hb, hc, hd'⟩ := hE hev
    exact ⟨ha d hd, hb d (by omega), hc d (by omega), hd' d (by omega) (fun _ => by omega)⟩
  · obtain ⟨ha, _, hb, hc, hd'⟩ := hO hev
    exact ⟨ha d (by omega), hb d hd, hc d (by omega), hd' d (by omega)⟩

private lemma wordL_coeff_eq_zero_of_gt (ws : List F) {d : ℕ} (hd : ws.length < d) :
    (wordL ws).a.coeff d = 0 ∧ (wordL ws).b.coeff d = 0 ∧
    (wordL ws).c.coeff d = 0 ∧ (wordL ws).d.coeff d = 0 := by
  obtain ⟨ha, hb, hc, hd'⟩ := wordU_coeff_eq_zero_of_gt ws hd
  exact ⟨hd', hc, hb, ha⟩

/-! ### 3. Truncated Congruence `PolyModEq` and `MatModEq` -/

/-- Two polynomials agree on all coefficients of degree `< n`. -/
def PolyModEq (n : ℕ) (p q : F[X]) : Prop :=
  ∀ d < n, p.coeff d = q.coeff d

/-- Entrywise truncated congruence of `2 × 2` polynomial matrices. -/
def MatModEq (n00 n01 n10 n11 : ℕ) (M N : PolyMat2 F) : Prop :=
  PolyModEq n00 M.a N.a ∧ PolyModEq n01 M.b N.b ∧
  PolyModEq n10 M.c N.c ∧ PolyModEq n11 M.d N.d

private lemma polyModEq_refl (n : ℕ) (p : F[X]) : PolyModEq n p p :=
  fun _ _ => rfl

private lemma polyModEq_trans {n : ℕ} {p q r : F[X]}
    (h1 : PolyModEq n p q) (h2 : PolyModEq n q r) : PolyModEq n p r :=
  fun d hd => (h1 d hd).trans (h2 d hd)

private lemma polyModEq_mono {m n : ℕ} (hmn : m ≤ n) {p q : F[X]}
    (h : PolyModEq n p q) : PolyModEq m p q :=
  fun d hd => h d (lt_of_lt_of_le hd hmn)

private lemma polyModEq_zero_mul_right {n : ℕ} {p q : F[X]} (hp : PolyModEq n p 0) :
    PolyModEq n (p * q) 0 := by
  intro d hd
  rw [coeff_zero, coeff_mul]
  apply Finset.sum_eq_zero
  intro x hx
  have hx1 : x.1 ≤ d := by
    have := Finset.mem_antidiagonal.mp hx; omega
  have h0 : p.coeff x.1 = 0 := by simpa using hp x.1 (lt_of_le_of_lt hx1 hd)
  rw [h0, zero_mul]

private lemma polyModEq_zero_mul_left {n : ℕ} {p q : F[X]} (hq : PolyModEq n q 0) :
    PolyModEq n (p * q) 0 := by
  rw [mul_comm]; exact polyModEq_zero_mul_right hq

private lemma polyModEq_zero_add {n : ℕ} {p q : F[X]}
    (hp : PolyModEq n p 0) (hq : PolyModEq n q 0) :
    PolyModEq n (p + q) 0 := by
  intro d hd
  rw [coeff_add, coeff_zero]
  have hp' := hp d hd
  have hq' := hq d hd
  simp only [coeff_zero] at hp' hq'
  rw [hp', hq', add_zero]

private lemma matModEq_trans {n00 n01 n10 n11 : ℕ} {M N K : PolyMat2 F}
    (h1 : MatModEq n00 n01 n10 n11 M N) (h2 : MatModEq n00 n01 n10 n11 N K) :
    MatModEq n00 n01 n10 n11 M K :=
  ⟨polyModEq_trans h1.1 h2.1, polyModEq_trans h1.2.1 h2.2.1,
   polyModEq_trans h1.2.2.1 h2.2.2.1, polyModEq_trans h1.2.2.2 h2.2.2.2⟩

private lemma matModEq_stepL_mul {n00 n01 n10 n11 : ℕ}
    (h10 : n10 ≤ n00 + 1) (h11 : n11 ≤ n01 + 1)
    (u : F) {M N : PolyMat2 F} (h : MatModEq n00 n01 n10 n11 M N) :
    MatModEq n00 n01 n10 n11 (mul (stepL u) M) (mul (stepL u) N) := by
  rcases h with ⟨ha, hb, hc, hd⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd'; simp only [mul, stepL, one_mul, zero_mul, add_zero]; exact ha d hd'
  · intro d hd'; simp only [mul, stepL, one_mul, zero_mul, add_zero]; exact hb d hd'
  · intro d hd'
    simp only [mul, stepL, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    cases d with
    | zero =>
      simp only [coeff_X_mul_zero, mul_zero, zero_add]
      exact hc 0 hd'
    | succ d' =>
      simp only [coeff_X_mul]
      rw [ha d' (by omega), hc (d' + 1) hd']
  · intro d hd'
    simp only [mul, stepL, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    cases d with
    | zero =>
      simp only [coeff_X_mul_zero, mul_zero, zero_add]
      exact hd 0 hd'
    | succ d' =>
      simp only [coeff_X_mul]
      rw [hb d' (by omega), hd (d' + 1) hd']

private lemma matModEq_stepU_mul {n00 n01 n10 n11 : ℕ}
    (h00 : n00 ≤ n10 + 1) (h01 : n01 ≤ n11 + 1)
    (v : F) {M N : PolyMat2 F} (h : MatModEq n00 n01 n10 n11 M N) :
    MatModEq n00 n01 n10 n11 (mul (stepU v) M) (mul (stepU v) N) := by
  rcases h with ⟨ha, hb, hc, hd⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd'
    simp only [mul, stepU, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    cases d with
    | zero =>
      simp only [coeff_X_mul_zero, mul_zero, add_zero]
      exact ha 0 hd'
    | succ d' =>
      simp only [coeff_X_mul]
      rw [ha (d' + 1) hd', hc d' (by omega)]
  · intro d hd'
    simp only [mul, stepU, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    cases d with
    | zero =>
      simp only [coeff_X_mul_zero, mul_zero, add_zero]
      exact hb 0 hd'
    | succ d' =>
      simp only [coeff_X_mul]
      rw [hb (d' + 1) hd', hd d' (by omega)]
  · intro d hd'; simp only [mul, stepU, one_mul, zero_mul, zero_add]; exact hc d hd'
  · intro d hd'; simp only [mul, stepU, one_mul, zero_mul, zero_add]; exact hd d hd'

/-! ### 4. Half-Split Contradictions for `wordU ws` over a Field -/

/-- If `ws` is a nonempty list of even length `2 * m` of nonzero elements of a field `F`, then
`wordU ws` cannot be congruent to `I₂` modulo `X^N` for any `N > m`. -/
private lemma not_wordU_modEq_one {F : Type*} [Field F] {ws : List F}
    (hm : 1 ≤ ws.length / 2) (hev : Even ws.length)
    (hnz : ∀ w ∈ ws, w ≠ 0) {N : ℕ} (hN : ws.length / 2 < N)
    (hmod : MatModEq N N N N (wordU ws) one) : False := by
  set m := ws.length / 2
  have hlen : ws.length = 2 * m := by obtain ⟨k, hk⟩ := hev; omega
  have hprod_nz : ws.prod ≠ 0 := List.prod_ne_zero (fun h0 => hnz 0 h0 rfl)
  set xs := ws.take m
  set ys := ws.drop m
  have hxs_len : xs.length = m := by rw [List.length_take, hlen]; omega
  have hys_len : ys.length = m := by rw [List.length_drop, hlen]; omega
  have hsplit : ws = xs ++ ys := (List.take_append_drop m ws).symm
  set A := wordU xs
  set B := if Even m then wordU ys else wordL ys
  have hAB : wordU ws = mul A B := by
    conv_lhs => rw [hsplit]
    rw [wordU_append, hxs_len]
    dsimp only [A, B]
    split_ifs <;> rfl
  have hdetA : det A = 1 := det_wordU xs
  have hdiff_eq : sub B (adj A) = mul (adj A) (sub (wordU ws) one) := by
    rw [mat_mul_sub, mat_mul_one, hAB, ← mat_mul_assoc, adj_mul_self hdetA, mat_one_mul]
  have hE0 : PolyModEq N (sub (wordU ws) one).a 0 ∧
      PolyModEq N (sub (wordU ws) one).b 0 ∧
      PolyModEq N (sub (wordU ws) one).c 0 ∧
      PolyModEq N (sub (wordU ws) one).d 0 := by
    rcases hmod with ⟨ha, hb, hc, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hd'; simp [sub, ha d hd']
    · intro d hd'; simp [sub, hb d hd']
    · intro d hd'; simp [sub, hc d hd']
    · intro d hd'; simp [sub, hd d hd']
  have hdiff_lt : ∀ d < N,
      (sub B (adj A)).a.coeff d = 0 ∧ (sub B (adj A)).b.coeff d = 0 ∧
      (sub B (adj A)).c.coeff d = 0 ∧ (sub B (adj A)).d.coeff d = 0 := by
    intro d hd'
    rw [hdiff_eq]
    rcases hE0 with ⟨ea, eb, ec, ed⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [mul] using polyModEq_zero_add (polyModEq_zero_mul_left ea)
        (polyModEq_zero_mul_left ec) d hd'
    · simpa [mul] using polyModEq_zero_add (polyModEq_zero_mul_left eb)
        (polyModEq_zero_mul_left ed) d hd'
    · simpa [mul] using polyModEq_zero_add (polyModEq_zero_mul_left ea)
        (polyModEq_zero_mul_left ec) d hd'
    · simpa [mul] using polyModEq_zero_add (polyModEq_zero_mul_left eb)
        (polyModEq_zero_mul_left ed) d hd'
  have hdiff_gt : ∀ d, m < d →
      (sub B (adj A)).a.coeff d = 0 ∧ (sub B (adj A)).b.coeff d = 0 ∧
      (sub B (adj A)).c.coeff d = 0 ∧ (sub B (adj A)).d.coeff d = 0 := by
    intro d hd'
    have hA := wordU_coeff_eq_zero_of_gt xs (by omega : xs.length < d)
    have hB : B.a.coeff d = 0 ∧ B.b.coeff d = 0 ∧ B.c.coeff d = 0 ∧ B.d.coeff d = 0 := by
      dsimp only [B]
      split_ifs
      · exact wordU_coeff_eq_zero_of_gt ys (by omega : ys.length < d)
      · exact wordL_coeff_eq_zero_of_gt ys (by omega : ys.length < d)
    simp only [sub, adj, coeff_sub, coeff_neg]
    exact ⟨by rw [hB.1, hA.2.2.2, sub_zero],
      by rw [hB.2.1, hA.2.1, neg_zero, sub_zero],
      by rw [hB.2.2.1, hA.2.2.1, neg_zero, sub_zero],
      by rw [hB.2.2.2, hA.1, sub_zero]⟩
  have hBA : B = adj A := by
    apply PolyMat2.ext <;> apply AddMonoidAlgebra.ext <;> apply Finsupp.ext <;> intro d
    all_goals
      by_cases hdN : d < N
      · have h0 := hdiff_lt d hdN
        simp only [sub, coeff_sub, sub_eq_zero] at h0
        first | exact h0.1 | exact h0.2.1 | exact h0.2.2.1 | exact h0.2.2.2
      · have h0 := hdiff_gt d (by omega)
        simp only [sub, coeff_sub, sub_eq_zero] at h0
        first | exact h0.1 | exact h0.2.1 | exact h0.2.2.1 | exact h0.2.2.2
  have hW1 : wordU ws = one := by
    rw [hAB, hBA, mul_adj_self hdetA]
  have hlead : (wordU ws).a.coeff ws.length = ws.prod := (wordU_deg_lead ws).1 hev |>.1
  rw [hW1] at hlead
  have h10 : (one : PolyMat2 F).a.coeff ws.length = 0 := by
    simp only [one, coeff_one]
    have hne : ws.length ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
  exact hprod_nz (hlead.symm.trans h10)

/-- Sharp odd-half-length contradiction (needed for `k ≡ 3 mod 4`): if `ws` has length `2 * m`
with `m` odd and all entries nonzero, then `(wordU ws).b` and `(wordU ws).d - 1` cannot both
vanish modulo `X^{m + 1}`. -/
private lemma not_wordU_odd_half_col1_modEq {F : Type*} [Field F] {ws : List F}
    (hodd : ¬ Even (ws.length / 2)) (hev : Even ws.length)
    (hnz : ∀ w ∈ ws, w ≠ 0)
    (hb : PolyModEq (ws.length / 2 + 1) (wordU ws).b 0)
    (hd : PolyModEq (ws.length / 2 + 1) (wordU ws).d 1) : False := by
  set m := ws.length / 2
  have hlen : ws.length = 2 * m := by obtain ⟨k, hk⟩ := hev; omega
  set xs := ws.take m
  set ys := ws.drop m
  have hxs_len : xs.length = m := by rw [List.length_take, hlen]; omega
  have hys_len : ys.length = m := by rw [List.length_drop, hlen]; omega
  have hsplit : ws = xs ++ ys := (List.take_append_drop m ws).symm
  have hxs_nz : ∀ w ∈ xs, w ≠ 0 := fun w hw => hnz w (List.mem_of_mem_take hw)
  have hxs_prod_nz : xs.prod ≠ 0 := List.prod_ne_zero (fun h0 => hxs_nz 0 h0 rfl)
  set A := wordU xs
  set B := wordL ys
  have hAB : wordU ws = mul A B := by
    conv_lhs => rw [hsplit]
    rw [wordU_append, hxs_len]
    simp only [hodd, ↓reduceIte]
    rfl
  have hdetA : det A = 1 := det_wordU xs
  have hdiff_eq : sub B (adj A) = mul (adj A) (sub (wordU ws) one) := by
    rw [mat_mul_sub, mat_mul_one, hAB, ← mat_mul_assoc, adj_mul_self hdetA, mat_one_mul]
  have hcol1_zero : (sub B (adj A)).b.coeff m = 0 := by
    rw [hdiff_eq]
    have heb : PolyModEq (m + 1) (sub (wordU ws) one).b 0 := by
      intro d hd'; simp [sub, one, hb d hd']
    have hed : PolyModEq (m + 1) (sub (wordU ws) one).d 0 := by
      intro d hd'; simp [sub, one, hd d hd']
    simpa [mul] using polyModEq_zero_add (polyModEq_zero_mul_left heb)
      (polyModEq_zero_mul_left hed) m (by omega)
  have hxs_odd : ¬ Even xs.length := by rwa [hxs_len]
  have hys_odd : ¬ Even ys.length := by rwa [hys_len]
  have hA_lead : A.b.coeff m = xs.prod := by
    have h := (wordU_deg_lead xs).2 hxs_odd |>.2.1
    rwa [hxs_len] at h
  have hB_zero : B.b.coeff m = 0 := by
    have h := (wordU_deg_lead ys).2 hys_odd |>.2.2.2.1 m (by omega)
    exact h
  have hcalc : (sub B (adj A)).b.coeff m = xs.prod := by
    simp only [sub, adj, sub_neg_eq_add, coeff_add, hB_zero, zero_add, hA_lead]
  exact hxs_prod_nz (hcalc.symm.trans hcol1_zero)

end PolyMat2

/-! ### 5. Uniqueness of Colored Neighbors & State Matrix `stateMat` in `Λ_{k, F}` -/

/-- Two left neighbors of the same right vertex `r` with equal `0`-th coordinate are identical. -/
private lemma lambdaLeft_eq_of_adj_of_zero_eq {k : ℕ} (hk : 2 ≤ k) {R : Type*} [CommRing R]
    {l l' : LambdaLeft k R} {r : LambdaRight k R}
    (hl : lambdaAdj l.1 r.1) (hl' : lambdaAdj l'.1 r.1)
    (h0 : l.1 ⟨0, by omega⟩ = l'.1 ⟨0, by omega⟩) : l = l' := by
  apply Subtype.ext
  funext ⟨i, hi⟩
  have hrec : ∀ n : ℕ, ∀ hn : n ≤ k, l.1 ⟨n, by omega⟩ = l'.1 ⟨n, by omega⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst hn0; exact h0
      by_cases hn1 : n = 1
      · subst hn1
        rw [l.2 hk, l'.2 hk]
        have h2 := hl 2 (by omega) hk
        have h2' := hl' 2 (by omega) hk
        simp only [true_or, ↓reduceIte] at h2 h2'
        have heq : l.1 ⟨2, by omega⟩ + r.1 ⟨2, by omega⟩ =
            l'.1 ⟨2, by omega⟩ + r.1 ⟨2, by omega⟩ := by
          rw [h2, h2', h0]
        exact add_right_cancel heq
      · have hn2 : 2 ≤ n := by omega
        have heq1 := hl n hn2 hn
        have heq2 := hl' n hn2 hn
        have hsum : l.1 ⟨n, by omega⟩ + r.1 ⟨n, by omega⟩ =
            l'.1 ⟨n, by omega⟩ + r.1 ⟨n, by omega⟩ := by
          rw [heq1, heq2]
          split_ifs
          · rw [ih (n - 2) (by omega) (by omega)]
          · rw [h0]
        exact add_right_cancel hsum
  exact hrec i (by omega)

/-- Two right neighbors of the same left vertex `l` with equal `0`-th coordinate are identical. -/
private lemma lambdaRight_eq_of_adj_of_zero_eq {k : ℕ} (_hk : 2 ≤ k) {R : Type*} [CommRing R]
    {l : LambdaLeft k R} {r r' : LambdaRight k R}
    (hr : lambdaAdj l.1 r.1) (hr' : lambdaAdj l.1 r'.1)
    (h0 : r.1 ⟨0, by omega⟩ = r'.1 ⟨0, by omega⟩) : r = r' := by
  apply Subtype.ext
  funext ⟨i, hi⟩
  have hrec : ∀ n : ℕ, ∀ hn : n ≤ k, r.1 ⟨n, by omega⟩ = r'.1 ⟨n, by omega⟩ := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro hn
      by_cases hn0 : n = 0
      · subst hn0; exact h0
      by_cases hn1 : n = 1
      · subst hn1
        rw [r.2 (by omega), r'.2 (by omega)]
      · have hn2 : 2 ≤ n := by omega
        have heq1 := hr n hn2 hn
        have heq2 := hr' n hn2 hn
        have hsum : l.1 ⟨n, by omega⟩ + r.1 ⟨n, by omega⟩ =
            l.1 ⟨n, by omega⟩ + r'.1 ⟨n, by omega⟩ := by
          rw [heq1, heq2]
          split_ifs
          · rw [h0]
          · rw [ih (n - 2) (by omega) (by omega)]
        exact add_left_cancel hsum
  exact hrec i (by omega)

/-- Exact entrywise precision moduli of the state matrix `S(l, r; z)` in `Λ_{k, R}`. -/
private def N00 (k : ℕ) : ℕ := 2 * ((k + 2) / 4) + 2
private def N01 (k : ℕ) : ℕ := 2 * ((k + 1) / 4) + 3
private def N10 (k : ℕ) : ℕ := 2 * (k / 4) + 3
private def N11 (k : ℕ) : ℕ := 2 * ((k + 3) / 4) + 2

private lemma coeff_monomial_ite {F : Type*} [CommRing F] (m n : ℕ) (a : F) :
    (monomial m a).coeff n = if m = n then a else 0 := by
  simp [coeff_monomial, Finsupp.single_apply]

/-- Entry `(0, 0)` of `S(l, r; z)`: `1 + ∑_{4t+2 ≤ k} r_{4t+2} X^{2t+2}`. -/
private def stateS00 {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F) : F[X] :=
  1 + ∑ t ∈ Finset.range (k + 1),
    if h : 4 * t + 2 ≤ k then monomial (2 * t + 2) (r.1 ⟨4 * t + 2, by omega⟩) else 0

/-- Entry `(0, 1)` of `S(l, r; z)`: `r_0 X + ∑_{4t+3 ≤ k} r_{4t+3} X^{2t+3}`. -/
private def stateS01 {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F) : F[X] :=
  monomial 1 (r.1 ⟨0, by omega⟩) + ∑ t ∈ Finset.range (k + 1),
    if h : 4 * t + 3 ≤ k then monomial (2 * t + 3) (r.1 ⟨4 * t + 3, by omega⟩) else 0

/-- Entry `(1, 0)` of `S(l, r; z)`: `∑_{4t ≤ k} l_{4t} X^{2t+1}`. -/
private def stateS10 {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F) : F[X] :=
  ∑ t ∈ Finset.range (k + 1),
    if h : 4 * t ≤ k then monomial (2 * t + 1) (l.1 ⟨4 * t, by omega⟩) else 0

/-- Entry `(1, 1)` of `S(l, r; z)`: `1 + ∑_{4t+1 ≤ k} l_{4t+1} X^{2t+2}`. -/
private def stateS11 {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F) : F[X] :=
  1 + ∑ t ∈ Finset.range (k + 1),
    if h : 4 * t + 1 ≤ k then monomial (2 * t + 2) (l.1 ⟨4 * t + 1, by omega⟩) else 0

/-- The `2 × 2` affine-invariant polynomial state matrix `S(l, r; z)` in `Λ_{k, F}`. -/
private def stateMat {k : ℕ} {F : Type*} [CommRing F]
    (l : LambdaLeft k F) (r : LambdaRight k F) : PolyMat2 F :=
  ⟨stateS00 r, stateS01 r, stateS10 l, stateS11 l⟩

private lemma stateS00_coeff_zero {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F) :
    (stateS00 r).coeff 0 = 1 := by
  simp only [stateS00, coeff_add, coeff_one, ↓reduceIte, finsetSum_coeff]
  have h0 : ∑ t ∈ Finset.range (k + 1),
      (if h : 4 * t + 2 ≤ k then monomial (2 * t + 2) (r.1 ⟨4 * t + 2, by omega⟩) else 0).coeff 0
      = 0 := by
    apply Finset.sum_eq_zero; intro t _
    split_ifs
    · rw [coeff_monomial_ite]; simp
    · simp
  rw [h0, add_zero]

private lemma stateS00_coeff_odd {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F) (j : ℕ) :
    (stateS00 r).coeff (2 * j + 1) = 0 := by
  simp only [stateS00, coeff_add, coeff_one, finsetSum_coeff]
  have hne : 2 * j + 1 ≠ 0 := by omega
  simp only [hne, ↓reduceIte, zero_add]
  apply Finset.sum_eq_zero; intro t _
  split_ifs
  · rw [coeff_monomial_ite]; have : 2 * t + 2 ≠ 2 * j + 1 := by omega
    simp [this]
  · simp

private lemma stateS00_coeff_even {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F)
    {t : ℕ} (ht : 4 * t + 2 ≤ k) :
    (stateS00 r).coeff (2 * t + 2) = r.1 ⟨4 * t + 2, by omega⟩ := by
  simp only [stateS00, coeff_add, coeff_one, finsetSum_coeff]
  have hne : 2 * t + 2 ≠ 0 := by omega
  simp only [hne, ↓reduceIte, zero_add]
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro x _ hxt
    split_ifs
    · rw [coeff_monomial_ite]; simp [hxt]
    · simp
  · intro hmem; exfalso; exact hmem (Finset.mem_range.mpr (by omega))

private lemma stateS01_coeff_even {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F) (j : ℕ) :
    (stateS01 r).coeff (2 * j) = 0 := by
  simp only [stateS01, coeff_add, coeff_monomial_ite, finsetSum_coeff]
  have hne : (1 : ℕ) ≠ 2 * j := by omega
  simp only [hne, ↓reduceIte, zero_add]
  apply Finset.sum_eq_zero; intro t _
  split_ifs
  · rw [coeff_monomial_ite]; have : 2 * t + 3 ≠ 2 * j := by omega
    simp [this]
  · simp

private lemma stateS01_coeff_one {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F) :
    (stateS01 r).coeff 1 = r.1 ⟨0, by omega⟩ := by
  simp only [stateS01, coeff_add, coeff_monomial_ite, ↓reduceIte, finsetSum_coeff]
  have h0 : ∑ t ∈ Finset.range (k + 1),
      (if h : 4 * t + 3 ≤ k then monomial (2 * t + 3) (r.1 ⟨4 * t + 3, by omega⟩) else 0).coeff 1
      = 0 := by
    apply Finset.sum_eq_zero; intro t _
    split_ifs
    · rw [coeff_monomial_ite]; have : 2 * t + 3 ≠ 1 := by omega
      simp [this]
    · simp
  rw [h0, add_zero]

private lemma stateS01_coeff_odd {k : ℕ} {F : Type*} [CommRing F] (r : LambdaRight k F)
    {t : ℕ} (ht : 4 * t + 3 ≤ k) :
    (stateS01 r).coeff (2 * t + 3) = r.1 ⟨4 * t + 3, by omega⟩ := by
  simp only [stateS01, coeff_add, coeff_monomial_ite, finsetSum_coeff]
  have hne : (1 : ℕ) ≠ 2 * t + 3 := by omega
  simp only [hne, ↓reduceIte, zero_add]
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro x _ hxt
    split_ifs
    · rw [coeff_monomial_ite]; simp [hxt]
    · simp
  · intro hmem; exfalso; exact hmem (Finset.mem_range.mpr (by omega))

private lemma stateS10_coeff_even {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F) (j : ℕ) :
    (stateS10 l).coeff (2 * j) = 0 := by
  simp only [stateS10, finsetSum_coeff]
  apply Finset.sum_eq_zero; intro t _
  split_ifs
  · rw [coeff_monomial_ite]; have : 2 * t + 1 ≠ 2 * j := by omega
    simp [this]
  · simp

private lemma stateS10_coeff_odd {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F)
    {t : ℕ} (ht : 4 * t ≤ k) :
    (stateS10 l).coeff (2 * t + 1) = l.1 ⟨4 * t, by omega⟩ := by
  simp only [stateS10, finsetSum_coeff]
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro x _ hxt
    split_ifs
    · rw [coeff_monomial_ite]; simp [hxt]
    · simp
  · intro hmem; exfalso; exact hmem (Finset.mem_range.mpr (by omega))

private lemma stateS11_coeff_zero {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F) :
    (stateS11 l).coeff 0 = 1 := by
  simp only [stateS11, coeff_add, coeff_one, ↓reduceIte, finsetSum_coeff]
  have h0 : ∑ t ∈ Finset.range (k + 1),
      (if h : 4 * t + 1 ≤ k then monomial (2 * t + 2) (l.1 ⟨4 * t + 1, by omega⟩) else 0).coeff 0
      = 0 := by
    apply Finset.sum_eq_zero; intro t _
    split_ifs
    · rw [coeff_monomial_ite]; simp
    · simp
  rw [h0, add_zero]

private lemma stateS11_coeff_odd {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F) (j : ℕ) :
    (stateS11 l).coeff (2 * j + 1) = 0 := by
  simp only [stateS11, coeff_add, coeff_one, finsetSum_coeff]
  have hne : 2 * j + 1 ≠ 0 := by omega
  simp only [hne, ↓reduceIte, zero_add]
  apply Finset.sum_eq_zero; intro t _
  split_ifs
  · rw [coeff_monomial_ite]; have : 2 * t + 2 ≠ 2 * j + 1 := by omega
    simp [this]
  · simp

private lemma stateS11_coeff_even {k : ℕ} {F : Type*} [CommRing F] (l : LambdaLeft k F)
    {t : ℕ} (ht : 4 * t + 1 ≤ k) :
    (stateS11 l).coeff (2 * t + 2) = l.1 ⟨4 * t + 1, by omega⟩ := by
  simp only [stateS11, coeff_add, coeff_one, finsetSum_coeff]
  have hne : 2 * t + 2 ≠ 0 := by omega
  simp only [hne, ↓reduceIte, zero_add]
  rw [Finset.sum_eq_single t]
  · simp [ht]
  · intro x _ hxt
    split_ifs
    · rw [coeff_monomial_ite]; simp [hxt]
    · simp
  · intro hmem; exfalso; exact hmem (Finset.mem_range.mpr (by omega))

/-- Transition step `[l] ~ ⟨r⟩ ~ [l']` multiplies `S(l, r)` on the left by `L(l'_0 - l_0)`. -/
private lemma stateMat_stepL {k : ℕ} (hk : 2 ≤ k) {F : Type*} [CommRing F]
    {l l' : LambdaLeft k F} {r : LambdaRight k F}
    (hl : lambdaAdj l.1 r.1) (hl' : lambdaAdj l'.1 r.1) :
    PolyMat2.MatModEq (N00 k) (N01 k) (N10 k) (N11 k)
      (stateMat l' r)
      (PolyMat2.mul (PolyMat2.stepL (l'.1 ⟨0, by omega⟩ - l.1 ⟨0, by omega⟩))
        (stateMat l r)) := by
  set u := l'.1 ⟨0, by omega⟩ - l.1 ⟨0, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d _; simp [stateMat, PolyMat2.mul, PolyMat2.stepL]
  · intro d _; simp [stateMat, PolyMat2.mul, PolyMat2.stepL]
  · intro d hd
    simp only [stateMat, PolyMat2.mul, PolyMat2.stepL, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj' : d = 2 * j := by omega
      subst hj'
      cases j with
      | zero =>
        rw [stateS10_coeff_even l' 0, stateS10_coeff_even l 0]
        simp
      | succ j' =>
        have h2 : 2 * (j' + 1) = (2 * j' + 1) + 1 := by omega
        rw [h2, coeff_X_mul, stateS00_coeff_odd, mul_zero, zero_add]
        rw [← h2, stateS10_coeff_even, stateS10_coeff_even]
    · subst hj
      cases j with
      | zero =>
        have h1 : 2 * 0 + 1 = 0 + 1 := rfl
        rw [stateS10_coeff_odd l' (t := 0) (by omega), stateS10_coeff_odd l (t := 0) (by omega),
          h1, coeff_X_mul, stateS00_coeff_zero, mul_one]
        change l'.1 ⟨0, by omega⟩ = u + l.1 ⟨0, by omega⟩
        simp only [u]; ring
      | succ t =>
        have hlt : 4 * (t + 1) ≤ k := by unfold N10 at hd; omega
        have hlt2 : 4 * t + 2 ≤ k := by omega
        have h2 : 2 * (t + 1) + 1 = (2 * t + 2) + 1 := by omega
        rw [h2, coeff_X_mul, stateS00_coeff_even r hlt2, ← h2,
          stateS10_coeff_odd l' hlt, stateS10_coeff_odd l hlt]
        have heq := hl (4 * (t + 1)) (by omega) hlt
        have heq' := hl' (4 * (t + 1)) (by omega) hlt
        have hmod : ¬ ((4 * (t + 1)) % 4 = 2 ∨ (4 * (t + 1)) % 4 = 3) := by omega
        simp only [hmod, ↓reduceIte] at heq heq'
        have hsub : 4 * (t + 1) - 2 = 4 * t + 2 := by omega
        have hidx : (⟨4 * (t + 1) - 2, by omega⟩ : Fin (k + 1)) = ⟨4 * t + 2, by omega⟩ :=
          Fin.ext hsub
        rw [hidx] at heq heq'
        have hdiff : l'.1 ⟨4 * (t + 1), by omega⟩ - l.1 ⟨4 * (t + 1), by omega⟩ =
            u * r.1 ⟨4 * t + 2, by omega⟩ := by
          calc l'.1 ⟨4 * (t + 1), by omega⟩ - l.1 ⟨4 * (t + 1), by omega⟩
              = (l'.1 ⟨4 * (t + 1), by omega⟩ + r.1 ⟨4 * (t + 1), by omega⟩) -
                (l.1 ⟨4 * (t + 1), by omega⟩ + r.1 ⟨4 * (t + 1), by omega⟩) := by ring
            _ = l'.1 ⟨0, by omega⟩ * r.1 ⟨4 * t + 2, by omega⟩ -
                l.1 ⟨0, by omega⟩ * r.1 ⟨4 * t + 2, by omega⟩ := by rw [heq', heq]
            _ = u * r.1 ⟨4 * t + 2, by omega⟩ := by simp only [u]; ring
        calc l'.1 ⟨4 * (t + 1), by omega⟩
            = (l'.1 ⟨4 * (t + 1), by omega⟩ - l.1 ⟨4 * (t + 1), by omega⟩) +
                l.1 ⟨4 * (t + 1), by omega⟩ := by ring
          _ = u * r.1 ⟨4 * t + 2, by omega⟩ + l.1 ⟨4 * (t + 1), by omega⟩ := by rw [hdiff]
  · intro d hd
    simp only [stateMat, PolyMat2.mul, PolyMat2.stepL, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj' : d = 2 * j := by omega
      subst hj'
      cases j with
      | zero =>
        simp [stateS11_coeff_zero]
      | succ j' =>
        cases j' with
        | zero =>
          have h2eq : 2 * (0 + 1) = 1 + 1 := rfl
          rw [h2eq, coeff_X_mul, stateS01_coeff_one]
          have h1k : 4 * 0 + 1 ≤ k := by omega
          have h20 : (1 + 1 : ℕ) = 2 * 0 + 2 := rfl
          rw [h20, stateS11_coeff_even l' h1k, stateS11_coeff_even l h1k]
          change l'.1 ⟨1, by omega⟩ = u * r.1 ⟨0, by omega⟩ + l.1 ⟨1, by omega⟩
          rw [l'.2 hk, l.2 hk]
          have heq := hl 2 (by omega) hk
          have heq' := hl' 2 (by omega) hk
          simp only [true_or, ↓reduceIte] at heq heq'
          have hdiff : l'.1 ⟨2, by omega⟩ - l.1 ⟨2, by omega⟩ = u * r.1 ⟨0, by omega⟩ := by
            calc l'.1 ⟨2, by omega⟩ - l.1 ⟨2, by omega⟩
                = (l'.1 ⟨2, by omega⟩ + r.1 ⟨2, by omega⟩) -
                  (l.1 ⟨2, by omega⟩ + r.1 ⟨2, by omega⟩) := by ring
              _ = r.1 ⟨0, by omega⟩ * l'.1 ⟨0, by omega⟩ -
                  r.1 ⟨0, by omega⟩ * l.1 ⟨0, by omega⟩ := by rw [heq', heq]
              _ = u * r.1 ⟨0, by omega⟩ := by simp only [u]; ring
          calc l'.1 ⟨2, by omega⟩
              = (l'.1 ⟨2, by omega⟩ - l.1 ⟨2, by omega⟩) + l.1 ⟨2, by omega⟩ := by ring
            _ = u * r.1 ⟨0, by omega⟩ + l.1 ⟨2, by omega⟩ := by rw [hdiff]
        | succ t =>
          have hlt : 4 * (t + 1) + 1 ≤ k := by unfold N11 at hd; omega
          have hlt2 : 4 * t + 3 ≤ k := by omega
          have h2 : 2 * (t + 1 + 1) = (2 * t + 3) + 1 := by omega
          have h2' : 2 * (t + 1 + 1) = 2 * (t + 1) + 2 := by omega
          rw [h2, coeff_X_mul, stateS01_coeff_odd r hlt2, ← h2, h2',
            stateS11_coeff_even l' hlt, stateS11_coeff_even l hlt]
          have heq := hl (4 * (t + 1) + 1) (by omega) hlt
          have heq' := hl' (4 * (t + 1) + 1) (by omega) hlt
          have hmod : ¬ ((4 * (t + 1) + 1) % 4 = 2 ∨ (4 * (t + 1) + 1) % 4 = 3) := by omega
          simp only [hmod, ↓reduceIte] at heq heq'
          have hsub : 4 * (t + 1) + 1 - 2 = 4 * t + 3 := by omega
          have hidx : (⟨4 * (t + 1) + 1 - 2, by omega⟩ : Fin (k + 1)) =
              ⟨4 * t + 3, by omega⟩ := Fin.ext hsub
          rw [hidx] at heq heq'
          have hdiff : l'.1 ⟨4 * (t + 1) + 1, by omega⟩ - l.1 ⟨4 * (t + 1) + 1, by omega⟩ =
              u * r.1 ⟨4 * t + 3, by omega⟩ := by
            calc l'.1 ⟨4 * (t + 1) + 1, by omega⟩ - l.1 ⟨4 * (t + 1) + 1, by omega⟩
                = (l'.1 ⟨4 * (t + 1) + 1, by omega⟩ + r.1 ⟨4 * (t + 1) + 1, by omega⟩) -
                  (l.1 ⟨4 * (t + 1) + 1, by omega⟩ + r.1 ⟨4 * (t + 1) + 1, by omega⟩) := by ring
              _ = l'.1 ⟨0, by omega⟩ * r.1 ⟨4 * t + 3, by omega⟩ -
                  l.1 ⟨0, by omega⟩ * r.1 ⟨4 * t + 3, by omega⟩ := by rw [heq', heq]
              _ = u * r.1 ⟨4 * t + 3, by omega⟩ := by simp only [u]; ring
          calc l'.1 ⟨4 * (t + 1) + 1, by omega⟩
              = (l'.1 ⟨4 * (t + 1) + 1, by omega⟩ - l.1 ⟨4 * (t + 1) + 1, by omega⟩) +
                  l.1 ⟨4 * (t + 1) + 1, by omega⟩ := by ring
            _ = u * r.1 ⟨4 * t + 3, by omega⟩ + l.1 ⟨4 * (t + 1) + 1, by omega⟩ := by rw [hdiff]
    · subst hj
      rw [coeff_X_mul, stateS01_coeff_even, mul_zero, zero_add,
        stateS11_coeff_odd, stateS11_coeff_odd]

/-- Transition step `⟨r⟩ ~ [l] ~ ⟨r'⟩` multiplies `S(l, r)` on the left by `U(r'_0 - r_0)`. -/
private lemma stateMat_stepR {k : ℕ} (hk : 2 ≤ k) {F : Type*} [CommRing F]
    {l : LambdaLeft k F} {r r' : LambdaRight k F}
    (hr : lambdaAdj l.1 r.1) (hr' : lambdaAdj l.1 r'.1) :
    PolyMat2.MatModEq (N00 k) (N01 k) (N10 k) (N11 k)
      (stateMat l r')
      (PolyMat2.mul (PolyMat2.stepU (r'.1 ⟨0, by omega⟩ - r.1 ⟨0, by omega⟩))
        (stateMat l r)) := by
  set v := r'.1 ⟨0, by omega⟩ - r.1 ⟨0, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d hd
    simp only [stateMat, PolyMat2.mul, PolyMat2.stepU, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj' : d = 2 * j := by omega
      subst hj'
      cases j with
      | zero =>
        simp [stateS00_coeff_zero]
      | succ t =>
        have hlt : 4 * t + 2 ≤ k := by unfold N00 at hd; omega
        have hlt0 : 4 * t ≤ k := by omega
        have h2 : 2 * (t + 1) = (2 * t + 1) + 1 := by omega
        have h2' : 2 * (t + 1) = 2 * t + 2 := by omega
        rw [h2, coeff_X_mul, stateS10_coeff_odd l hlt0, ← h2, h2',
          stateS00_coeff_even r' hlt, stateS00_coeff_even r hlt]
        have heq := hr (4 * t + 2) (by omega) hlt
        have heq' := hr' (4 * t + 2) (by omega) hlt
        have hmod : (4 * t + 2) % 4 = 2 ∨ (4 * t + 2) % 4 = 3 := by omega
        simp only [hmod, ↓reduceIte] at heq heq'
        have hsub : 4 * t + 2 - 2 = 4 * t := by omega
        have hidx : (⟨4 * t + 2 - 2, by omega⟩ : Fin (k + 1)) = ⟨4 * t, by omega⟩ :=
          Fin.ext hsub
        rw [hidx] at heq heq'
        have hdiff : r'.1 ⟨4 * t + 2, by omega⟩ - r.1 ⟨4 * t + 2, by omega⟩ =
            v * l.1 ⟨4 * t, by omega⟩ := by
          calc r'.1 ⟨4 * t + 2, by omega⟩ - r.1 ⟨4 * t + 2, by omega⟩
              = (l.1 ⟨4 * t + 2, by omega⟩ + r'.1 ⟨4 * t + 2, by omega⟩) -
                (l.1 ⟨4 * t + 2, by omega⟩ + r.1 ⟨4 * t + 2, by omega⟩) := by ring
            _ = r'.1 ⟨0, by omega⟩ * l.1 ⟨4 * t, by omega⟩ -
                r.1 ⟨0, by omega⟩ * l.1 ⟨4 * t, by omega⟩ := by rw [heq', heq]
            _ = v * l.1 ⟨4 * t, by omega⟩ := by simp only [v]; ring
        calc r'.1 ⟨4 * t + 2, by omega⟩
            = r.1 ⟨4 * t + 2, by omega⟩ +
                (r'.1 ⟨4 * t + 2, by omega⟩ - r.1 ⟨4 * t + 2, by omega⟩) := by ring
          _ = r.1 ⟨4 * t + 2, by omega⟩ + v * l.1 ⟨4 * t, by omega⟩ := by rw [hdiff]
    · subst hj
      rw [coeff_X_mul, stateS10_coeff_even, mul_zero, add_zero,
        stateS00_coeff_odd, stateS00_coeff_odd]
  · intro d hd
    simp only [stateMat, PolyMat2.mul, PolyMat2.stepU, one_mul, coeff_add, mul_assoc, coeff_C_mul]
    rcases Nat.even_or_odd d with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hj' : d = 2 * j := by omega
      subst hj'
      cases j with
      | zero =>
        rw [stateS01_coeff_even r' 0, stateS01_coeff_even r 0]
        simp
      | succ j' =>
        have h2 : 2 * (j' + 1) = (2 * j' + 1) + 1 := by omega
        rw [h2, coeff_X_mul, stateS11_coeff_odd, mul_zero, add_zero, ← h2,
          stateS01_coeff_even, stateS01_coeff_even]
    · subst hj
      cases j with
      | zero =>
        have h1 : 2 * 0 + 1 = 0 + 1 := rfl
        rw [h1, coeff_X_mul, stateS11_coeff_zero, mul_one,
          show (0 + 1 : ℕ) = 1 from rfl, stateS01_coeff_one, stateS01_coeff_one]
        simp only [v]; ring
      | succ t =>
        have hlt : 4 * t + 3 ≤ k := by unfold N01 at hd; omega
        have hlt1 : 4 * t + 1 ≤ k := by omega
        have h2 : 2 * (t + 1) + 1 = (2 * t + 2) + 1 := by omega
        have h2' : 2 * (t + 1) + 1 = 2 * t + 3 := by omega
        rw [h2, coeff_X_mul, stateS11_coeff_even l hlt1, ← h2, h2',
          stateS01_coeff_odd r' hlt, stateS01_coeff_odd r hlt]
        have heq := hr (4 * t + 3) (by omega) hlt
        have heq' := hr' (4 * t + 3) (by omega) hlt
        have hmod : (4 * t + 3) % 4 = 2 ∨ (4 * t + 3) % 4 = 3 := by omega
        simp only [hmod, ↓reduceIte] at heq heq'
        have hsub : 4 * t + 3 - 2 = 4 * t + 1 := by omega
        have hidx : (⟨4 * t + 3 - 2, by omega⟩ : Fin (k + 1)) = ⟨4 * t + 1, by omega⟩ :=
          Fin.ext hsub
        rw [hidx] at heq heq'
        have hdiff : r'.1 ⟨4 * t + 3, by omega⟩ - r.1 ⟨4 * t + 3, by omega⟩ =
            v * l.1 ⟨4 * t + 1, by omega⟩ := by
          calc r'.1 ⟨4 * t + 3, by omega⟩ - r.1 ⟨4 * t + 3, by omega⟩
              = (l.1 ⟨4 * t + 3, by omega⟩ + r'.1 ⟨4 * t + 3, by omega⟩) -
                (l.1 ⟨4 * t + 3, by omega⟩ + r.1 ⟨4 * t + 3, by omega⟩) := by ring
            _ = r'.1 ⟨0, by omega⟩ * l.1 ⟨4 * t + 1, by omega⟩ -
                r.1 ⟨0, by omega⟩ * l.1 ⟨4 * t + 1, by omega⟩ := by rw [heq', heq]
            _ = v * l.1 ⟨4 * t + 1, by omega⟩ := by simp only [v]; ring
        calc r'.1 ⟨4 * t + 3, by omega⟩
            = r.1 ⟨4 * t + 3, by omega⟩ +
                (r'.1 ⟨4 * t + 3, by omega⟩ - r.1 ⟨4 * t + 3, by omega⟩) := by ring
          _ = r.1 ⟨4 * t + 3, by omega⟩ + v * l.1 ⟨4 * t + 1, by omega⟩ := by rw [hdiff]
  · intro d _; simp [stateMat, PolyMat2.mul, PolyMat2.stepU]
  · intro d _; simp [stateMat, PolyMat2.mul, PolyMat2.stepU]

/-! ### 6. Extracting Congruence `T_m ≡ I₂` from `T_m · S₀ ≡ S₀` -/

/-- If `E · S₀ ≡ 0` uniformly modulo `X^N` and `S₀(0) = I₂`, then `E ≡ 0 (mod X^N)`. -/
private lemma cancel_stateMat_uniform {k N : ℕ} {F : Type*} [CommRing F]
    {l : LambdaLeft k F} {r : LambdaRight k F} {E : PolyMat2 F}
    (hES : PolyMat2.MatModEq N N N N (PolyMat2.mul E (stateMat l r))
      ⟨0, 0, 0, 0⟩) :
    PolyMat2.MatModEq N N N N E ⟨0, 0, 0, 0⟩ := by
  have hS00 : (stateMat l r).a.coeff 0 = 1 := stateS00_coeff_zero r
  have hS01 : (stateMat l r).b.coeff 0 = 0 := by simpa [stateMat] using stateS01_coeff_even r 0
  have hS10 : (stateMat l r).c.coeff 0 = 0 := by simpa [stateMat] using stateS10_coeff_even l 0
  have hS11 : (stateMat l r).d.coeff 0 = 1 := stateS11_coeff_zero l
  have hmain : ∀ d < N, E.a.coeff d = 0 ∧ E.b.coeff d = 0 ∧
      E.c.coeff d = 0 ∧ E.d.coeff d = 0 := by
    intro d
    induction d using Nat.strong_induction_on with
    | ind d ih =>
      intro hd
      have hterm : ∀ (p q : F[X]), (∀ j < d, p.coeff j = 0) →
          (p * q).coeff d = p.coeff d * q.coeff 0 := by
        intro p q hp
        rw [coeff_mul, Finset.sum_eq_single (d, 0)]
        · intro x hx hne
          have hxsum := Finset.mem_antidiagonal.mp hx
          have hxlt : x.1 < d := by
            by_contra hge
            have h1 : x.1 = d := by omega
            have h2 : x.2 = 0 := by omega
            exact hne (Prod.ext h1 h2)
          rw [hp x.1 hxlt, zero_mul]
        · intro hmem; exfalso; exact hmem (Finset.mem_antidiagonal.mpr (by omega))
      have ha_lt : ∀ j < d, E.a.coeff j = 0 := fun j hj => (ih j hj (lt_trans hj hd)).1
      have hb_lt : ∀ j < d, E.b.coeff j = 0 := fun j hj => (ih j hj (lt_trans hj hd)).2.1
      have hc_lt : ∀ j < d, E.c.coeff j = 0 := fun j hj => (ih j hj (lt_trans hj hd)).2.2.1
      have hd_lt : ∀ j < d, E.d.coeff j = 0 := fun j hj => (ih j hj (lt_trans hj hd)).2.2.2
      have h00 := hES.1 d hd
      have h01 := hES.2.1 d hd
      have h10 := hES.2.2.1 d hd
      have h11 := hES.2.2.2 d hd
      simp only [PolyMat2.mul, coeff_add, coeff_zero] at h00 h01 h10 h11
      rw [hterm E.a _ ha_lt, hterm E.b _ hb_lt, hS00, hS10, mul_one, mul_zero, add_zero] at h00
      rw [hterm E.a _ ha_lt, hterm E.b _ hb_lt, hS01, hS11, mul_zero, mul_one, zero_add] at h01
      rw [hterm E.c _ hc_lt, hterm E.d _ hd_lt, hS00, hS10, mul_one, mul_zero, add_zero] at h10
      rw [hterm E.c _ hc_lt, hterm E.d _ hd_lt, hS01, hS11, mul_zero, mul_one, zero_add] at h11
      exact ⟨h00, h01, h10, h11⟩
  exact ⟨fun d hd => (hmain d hd).1, fun d hd => (hmain d hd).2.1,
    fun d hd => (hmain d hd).2.2.1, fun d hd => (hmain d hd).2.2.2⟩

/-- Combining `T · S₀ ≡ S₀` with `(N00 k, N01 k, N10 k, N11 k)` yields `gK k ≤ 2 * m` for any
closed alternating step list `ws` of length `2 * m` (`m ≥ 1`) with all nonzero entries. -/
private lemma gK_le_length_of_fixed_stateMat {k : ℕ} (hk : 2 ≤ k) {F : Type*} [Field F]
    {l : LambdaLeft k F} {r : LambdaRight k F} {ws : List F}
    (hm : 1 ≤ ws.length / 2) (hev : Even ws.length) (hnz : ∀ w ∈ ws, w ≠ 0)
    (hfix : PolyMat2.MatModEq (N00 k) (N01 k) (N10 k) (N11 k)
      (stateMat l r) (PolyMat2.mul (PolyMat2.wordU ws) (stateMat l r))) :
    gK k ≤ ws.length := by
  set m := ws.length / 2
  have hlen : ws.length = 2 * m := by obtain ⟨j, hj⟩ := hev; omega
  set T := PolyMat2.wordU ws
  set E := PolyMat2.sub T PolyMat2.one
  have hES : PolyMat2.MatModEq (N00 k) (N01 k) (N10 k) (N11 k)
      (PolyMat2.mul E (stateMat l r)) ⟨0, 0, 0, 0⟩ := by
    have hsub : PolyMat2.mul E (stateMat l r) =
        PolyMat2.sub (PolyMat2.mul T (stateMat l r)) (stateMat l r) := by
      apply PolyMat2.ext <;> simp only [E, PolyMat2.mul, PolyMat2.sub, PolyMat2.one] <;> ring
    rw [hsub]
    rcases hfix with ⟨ha, hb, hc, hd⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hd'; simp [PolyMat2.sub, (ha d hd').symm]
    · intro d hd'; simp [PolyMat2.sub, (hb d hd').symm]
    · intro d hd'; simp [PolyMat2.sub, (hc d hd').symm]
    · intro d hd'; simp [PolyMat2.sub, (hd d hd').symm]
  have hpar : (∀ j, T.a.coeff (2 * j + 1) = 0) ∧ (∀ j, T.b.coeff (2 * j) = 0) ∧
      (∀ j, T.c.coeff (2 * j) = 0) ∧ (∀ j, T.d.coeff (2 * j + 1) = 0) :=
    PolyMat2.wordU_parity ws
  have hE_par : (∀ j, E.a.coeff (2 * j + 1) = 0) ∧ (∀ j, E.b.coeff (2 * j) = 0) ∧
      (∀ j, E.c.coeff (2 * j) = 0) ∧ (∀ j, E.d.coeff (2 * j + 1) = 0) := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j; simp [E, PolyMat2.sub, PolyMat2.one, hpar.1 j, coeff_one]
    · intro j; simp [E, PolyMat2.sub, PolyMat2.one, hpar.2.1 j]
    · intro j; simp [E, PolyMat2.sub, PolyMat2.one, hpar.2.2.1 j]
    · intro j; simp [E, PolyMat2.sub, PolyMat2.one, hpar.2.2.2 j, coeff_one]
  have hT_of_E : ∀ N, PolyMat2.MatModEq N N N N E ⟨0, 0, 0, 0⟩ →
      PolyMat2.MatModEq N N N N T PolyMat2.one := by
    intro N hEN
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro d hd'; have h := hEN.1 d hd'; simp only [E, PolyMat2.sub, coeff_sub, coeff_zero] at h
      exact sub_eq_zero.mp h
    · intro d hd'; have h := hEN.2.1 d hd'; simp only [E, PolyMat2.sub, coeff_sub, coeff_zero] at h
      exact sub_eq_zero.mp h
    · intro d hd'; have h := hEN.2.2.1 d hd'
      simp only [E, PolyMat2.sub, coeff_sub, coeff_zero] at h
      exact sub_eq_zero.mp h
    · intro d hd'; have h := hEN.2.2.2 d hd'
      simp only [E, PolyMat2.sub, coeff_sub, coeff_zero] at h
      exact sub_eq_zero.mp h
  have hmod4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases hmod4 with h0 | h1 | h2 | h3
  · -- Case `k = 4s` (`gK k = 4s + 4`, uniform modulus `N = 2s + 2`).
    set N := 2 * (k / 4) + 2
    have hle : N ≤ N00 k ∧ N ≤ N01 k ∧ N ≤ N10 k ∧ N ≤ N11 k := by
      unfold N00 N01 N10 N11; omega
    have hEN := cancel_stateMat_uniform
      ⟨PolyMat2.polyModEq_mono hle.1 hES.1, PolyMat2.polyModEq_mono hle.2.1 hES.2.1,
       PolyMat2.polyModEq_mono hle.2.2.1 hES.2.2.1, PolyMat2.polyModEq_mono hle.2.2.2 hES.2.2.2⟩
    by_contra hlt
    have hmN : m < N := by
      have hevk : Even k := ⟨k / 2, by omega⟩
      unfold gK at hlt; simp only [hevk, ↓reduceIte] at hlt; omega
    exact PolyMat2.not_wordU_modEq_one hm hev hnz hmN (hT_of_E N hEN)
  · -- Case `k = 4s + 1` (`s ≥ 1`, `gK k = 4s + 6`, modulus `N0 = 2s + 2` boosted to `2s + 3`).
    set s := k / 4
    have hs1 : 1 ≤ s := by omega
    set N0 := 2 * s + 2
    have hle : N0 ≤ N00 k ∧ N0 ≤ N01 k ∧ N0 ≤ N10 k ∧ N0 + 1 ≤ N11 k := by
      unfold N00 N01 N10 N11; omega
    have hEN0 := cancel_stateMat_uniform
      ⟨PolyMat2.polyModEq_mono hle.1 hES.1, PolyMat2.polyModEq_mono hle.2.1 hES.2.1,
       PolyMat2.polyModEq_mono hle.2.2.1 hES.2.2.1,
       PolyMat2.polyModEq_mono (by omega : N0 ≤ N11 k) hES.2.2.2⟩
    have hEd_N0 : E.d.coeff N0 = 0 := by
      have h11 := hES.2.2.2 N0 (by omega)
      simp only [PolyMat2.mul, coeff_add, coeff_zero] at h11
      have hterm1 : (E.c * (stateMat l r).b).coeff N0 = 0 := by
        rw [coeff_mul]
        apply Finset.sum_eq_zero; intro x hx
        have hxsum := Finset.mem_antidiagonal.mp hx
        by_cases hlt' : x.1 < N0
        · have h0 := hEN0.2.2.1 x.1 hlt'; simp only [coeff_zero] at h0; rw [h0, zero_mul]
        · have hx2 : x.2 = 0 := by omega
          rw [hx2, show (stateMat l r).b.coeff 0 = 0 from stateS01_coeff_even r 0, mul_zero]
      have hterm2 : (E.d * (stateMat l r).d).coeff N0 = E.d.coeff N0 := by
        rw [coeff_mul, Finset.sum_eq_single (N0, 0)]
        · rw [show (stateMat l r).d.coeff 0 = 1 from stateS11_coeff_zero l, mul_one]
        · intro x hx hne
          have hxsum := Finset.mem_antidiagonal.mp hx
          have hlt' : x.1 < N0 := by
            by_contra hge
            exact hne (Prod.ext (by omega) (by omega))
          have h0 := hEN0.2.2.2 x.1 hlt'; simp only [coeff_zero] at h0; rw [h0, zero_mul]
        · intro hmem; exfalso; exact hmem (Finset.mem_antidiagonal.mpr (by omega))
      rw [hterm1, zero_add, hterm2] at h11
      exact h11
    have hEa_N0 : E.a.coeff N0 = 0 := by
      have hdet : PolyMat2.det T = 1 := PolyMat2.det_wordU ws
      have hdetE : E.a + E.d + E.a * E.d - E.b * E.c = 0 := by
        have hT : T.a = 1 + E.a ∧ T.b = E.b ∧ T.c = E.c ∧ T.d = 1 + E.d := by
          refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [E, PolyMat2.sub, PolyMat2.one] <;> ring
        have h1 : (1 + E.a) * (1 + E.d) - E.b * E.c = 1 := by
          rw [← hT.1, ← hT.2.1, ← hT.2.2.1, ← hT.2.2.2]; exact hdet
        calc E.a + E.d + E.a * E.d - E.b * E.c
            = ((1 + E.a) * (1 + E.d) - E.b * E.c) - 1 := by ring
          _ = 1 - 1 := by rw [h1]
          _ = 0 := sub_self 1
      have hcoeff := congrArg (fun p : F[X] => p.coeff N0) hdetE
      simp only [coeff_sub, coeff_add, coeff_zero] at hcoeff
      have hprod0 : ∀ p q : F[X], PolyMat2.PolyModEq N0 p 0 → PolyMat2.PolyModEq N0 q 0 →
          (p * q).coeff N0 = 0 := by
        intro p q hp hq
        rw [coeff_mul]
        apply Finset.sum_eq_zero; intro x hx
        have hxsum := Finset.mem_antidiagonal.mp hx
        by_cases hx1 : x.1 < N0
        · have h0 := hp x.1 hx1; simp only [coeff_zero] at h0; rw [h0, zero_mul]
        · have hx2 : x.2 < N0 := by omega
          have h0 := hq x.2 hx2; simp only [coeff_zero] at h0; rw [h0, mul_zero]
      rw [hEd_N0, add_zero, hprod0 E.a E.d hEN0.1 hEN0.2.2.2,
        hprod0 E.b E.c hEN0.2.1 hEN0.2.2.1, add_zero, sub_zero] at hcoeff
      exact hcoeff
    -- Together with parity (`E.b, E.c` vanish at even `N0 = 2s + 2`), `E ≡ 0 (mod N0 + 1)`.
    have hEN1 : PolyMat2.MatModEq (N0 + 1) (N0 + 1) (N0 + 1) (N0 + 1) E ⟨0, 0, 0, 0⟩ := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro d hd'
        by_cases hlt' : d < N0
        · exact hEN0.1 d hlt'
        · have : d = N0 := by omega
          subst this; simpa using hEa_N0
      · intro d hd'
        by_cases hlt' : d < N0
        · exact hEN0.2.1 d hlt'
        · have : d = 2 * (s + 1) := by omega
          subst this; simpa using hE_par.2.1 (s + 1)
      · intro d hd'
        by_cases hlt' : d < N0
        · exact hEN0.2.2.1 d hlt'
        · have : d = 2 * (s + 1) := by omega
          subst this; simpa using hE_par.2.2.1 (s + 1)
      · intro d hd'
        by_cases hlt' : d < N0
        · exact hEN0.2.2.2 d hlt'
        · have : d = N0 := by omega
          subst this; simpa using hEd_N0
    by_contra hlt
    have hmN : m < N0 + 1 := by
      have hoddk : ¬ Even k := by intro ⟨j, hj⟩; omega
      unfold gK at hlt; simp only [hoddk, ↓reduceIte] at hlt; omega
    exact PolyMat2.not_wordU_modEq_one hm hev hnz hmN (hT_of_E (N0 + 1) hEN1)
  · -- Case `k = 4s + 2` (`s ≥ 0`, `gK k = 4s + 6`, uniform modulus `N = 2s + 3`).
    set N := 2 * (k / 4) + 3
    have hle : N ≤ N00 k ∧ N ≤ N01 k ∧ N ≤ N10 k ∧ N ≤ N11 k := by
      unfold N00 N01 N10 N11; omega
    have hEN := cancel_stateMat_uniform
      ⟨PolyMat2.polyModEq_mono hle.1 hES.1, PolyMat2.polyModEq_mono hle.2.1 hES.2.1,
       PolyMat2.polyModEq_mono hle.2.2.1 hES.2.2.1, PolyMat2.polyModEq_mono hle.2.2.2 hES.2.2.2⟩
    by_contra hlt
    have hmN : m < N := by
      have hevk : Even k := ⟨k / 2, by omega⟩
      unfold gK at hlt; simp only [hevk, ↓reduceIte] at hlt; omega
    exact PolyMat2.not_wordU_modEq_one hm hev hnz hmN (hT_of_E N hEN)
  · -- Case `k = 4s + 3` (`s ≥ 0`, `gK k = 4s + 8`, uniform `N0 = 2s + 3` + sharp `m = 2s + 3`).
    set s := k / 4
    set N0 := 2 * s + 3
    have hle : N0 ≤ N00 k ∧ N0 + 1 ≤ N01 k ∧ N0 ≤ N10 k ∧ N0 ≤ N11 k := by
      unfold N00 N01 N10 N11; omega
    have hEN0 := cancel_stateMat_uniform
      ⟨PolyMat2.polyModEq_mono hle.1 hES.1,
       PolyMat2.polyModEq_mono (by omega : N0 ≤ N01 k) hES.2.1,
       PolyMat2.polyModEq_mono hle.2.2.1 hES.2.2.1,
       PolyMat2.polyModEq_mono hle.2.2.2 hES.2.2.2⟩
    by_contra hlt
    have hoddk : ¬ Even k := by intro ⟨j, hj⟩; omega
    unfold gK at hlt; simp only [hoddk, ↓reduceIte] at hlt
    by_cases hmN0 : m < N0
    · exact PolyMat2.not_wordU_modEq_one hm hev hnz hmN0 (hT_of_E N0 hEN0)
    · have hm_eq : m = N0 := by omega
      have hEa_N0 : E.a.coeff N0 = 0 := hE_par.1 (s + 1)
      have hEd_N0 : E.d.coeff N0 = 0 := hE_par.2.2.2 (s + 1)
      have hEb_N0 : E.b.coeff N0 = 0 := by
        have h01 := hES.2.1 N0 (by omega)
        simp only [PolyMat2.mul, coeff_add, coeff_zero] at h01
        have hterm1 : (E.a * (stateMat l r).b).coeff N0 = 0 := by
          rw [coeff_mul]
          apply Finset.sum_eq_zero; intro x hx
          have hxsum := Finset.mem_antidiagonal.mp hx
          by_cases hlt' : x.1 < N0
          · have h0 := hEN0.1 x.1 hlt'; simp only [coeff_zero] at h0; rw [h0, zero_mul]
          · have : x.1 = N0 := by omega
            rw [this, hEa_N0, zero_mul]
        have hterm2 : (E.b * (stateMat l r).d).coeff N0 = E.b.coeff N0 := by
          rw [coeff_mul, Finset.sum_eq_single (N0, 0)]
          · rw [show (stateMat l r).d.coeff 0 = 1 from stateS11_coeff_zero l, mul_one]
          · intro x hx hne
            have hxsum := Finset.mem_antidiagonal.mp hx
            have hlt' : x.1 < N0 := by
              by_contra hge
              exact hne (Prod.ext (by omega) (by omega))
            have h0 := hEN0.2.1 x.1 hlt'; simp only [coeff_zero] at h0; rw [h0, zero_mul]
          · intro hmem; exfalso; exact hmem (Finset.mem_antidiagonal.mpr (by omega))
        rw [hterm1, zero_add, hterm2] at h01
        exact h01
      have hTb : PolyMat2.PolyModEq (m + 1) T.b 0 := by
        intro d hd'
        rw [hm_eq] at hd'
        by_cases hlt' : d < N0
        · have h0 := hEN0.2.1 d hlt'
          simpa [E, PolyMat2.sub, PolyMat2.one] using h0
        · have : d = N0 := by omega
          subst this; simpa [E, PolyMat2.sub, PolyMat2.one] using hEb_N0
      have hTd : PolyMat2.PolyModEq (m + 1) T.d 1 := by
        intro d hd'
        rw [hm_eq] at hd'
        by_cases hlt' : d < N0
        · have h0 := hEN0.2.2.2 d hlt'
          simp only [E, PolyMat2.sub, PolyMat2.one, coeff_sub, coeff_zero] at h0
          exact sub_eq_zero.mp h0
        · have : d = N0 := by omega
          subst this
          have h0 := hEd_N0
          simp only [E, PolyMat2.sub, PolyMat2.one, coeff_sub] at h0
          exact sub_eq_zero.mp h0
      have hodd_m : ¬ Even m := by intro ⟨j, hj⟩; omega
      exact PolyMat2.not_wordU_odd_half_col1_modEq hodd_m hev hnz hTb hTd

/-! ### 7. From Any Simple Cycle in `Λ_{k, F}` to `gK k ≤ w.length` -/

/-- Vertices at distinct indices `< w.length` along a simple cycle are distinct. -/
private lemma getVert_inj_of_isCycle {V : Type*} {G : SimpleGraph V} {a : V}
    {w : G.Walk a a} (hw : w.IsCycle) {i j : ℕ}
    (hi : i < w.length) (hj : j < w.length) (heq : w.getVert i = w.getVert j) : i = j := by
  have hpath := hw.isPath_dropLast
  have hlen : w.dropLast.length = w.length - 1 := w.length_dropLast
  have hi' : i ≤ w.dropLast.length := by omega
  have hj' : j ≤ w.dropLast.length := by omega
  have heq' : w.dropLast.getVert i = w.dropLast.getVert j := by
    rw [w.getVert_dropLast hi, w.getVert_dropLast hj, heq]
  exact hpath.getVert_injOn hi' hj' heq'

/-- Every simple cycle in `lambdaGraph k F` (`k ≥ 2`, `F` a field) has length at least `gK k`. -/
theorem lambdaGraph_isCycle_length_ge {k : ℕ} (hk : 2 ≤ k) {F : Type*} [Field F]
    {a : LambdaLeft k F ⊕ LambdaRight k F} {w : (lambdaGraph k F).Walk a a}
    (hw : w.IsCycle) : gK k ≤ w.length := by
  have hL3 : 3 ≤ w.length := hw.three_le_length
  set off : ℕ := match a with | Sum.inl _ => 0 | Sum.inr _ => 1
  let V : ℕ → LambdaLeft k F ⊕ LambdaRight k F := fun t => w.getVert ((t + off) % w.length)
  have hV_adj : ∀ t, (lambdaGraph k F).Adj (V t) (V (t + 1)) := by
    intro t
    dsimp only [V]
    set r := (t + off) % w.length
    have hr : r < w.length := Nat.mod_lt _ (by omega)
    have hadj := w.adj_getVert_succ hr
    by_cases hlt : r + 1 < w.length
    · have hmod : (t + 1 + off) % w.length = r + 1 := by
        have : t + 1 + off = (t + off) + 1 := by omega
        rw [this, Nat.add_mod]
        have h1 : 1 % w.length = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1, Nat.mod_eq_of_lt hlt]
      rwa [hmod]
    · have hreq : r + 1 = w.length := by omega
      have hmod : (t + 1 + off) % w.length = 0 := by
        have : t + 1 + off = (t + off) + 1 := by omega
        rw [this, Nat.add_mod]
        have h1 : 1 % w.length = 1 := Nat.mod_eq_of_lt (by omega)
        rw [h1, hreq, Nat.mod_self]
      rw [hmod, w.getVert_zero]
      rw [hreq, w.getVert_length] at hadj
      exact hadj
  have hV_ne2 : ∀ t, V t ≠ V (t + 2) := by
    intro t heq
    have hidx := getVert_inj_of_isCycle hw
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega)) heq
    have hmod : (t + 2 + off) % w.length = ((t + off) % w.length + 2) % w.length := by
      have : t + 2 + off = (t + off) + 2 := by omega
      rw [this, Nat.add_mod, Nat.mod_eq_of_lt (by omega : 2 < w.length)]
    rw [hmod] at hidx
    set r := (t + off) % w.length
    have hr : r < w.length := Nat.mod_lt _ (by omega)
    by_cases h2 : r + 2 < w.length
    · rw [Nat.mod_eq_of_lt h2] at hidx; omega
    · have : (r + 2) % w.length = r + 2 - w.length := by
        have hsub : r + 2 = (r + 2 - w.length) + w.length := by omega
        conv_lhs => rw [hsub]
        rw [Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [this] at hidx; omega
  have hV0_left : ∃ l0, V 0 = Sum.inl l0 := by
    cases a with
    | inl l0 =>
      refine ⟨l0, ?_⟩
      simp [V, off]
    | inr r0 =>
      have h01 : (lambdaGraph k F).Adj (w.getVert 0) (w.getVert 1) :=
        w.adj_getVert_succ (by omega)
      rw [w.getVert_zero] at h01
      cases hv1 : w.getVert 1 with
      | inl l1 =>
        refine ⟨l1, ?_⟩
        simp only [V, off, zero_add, Nat.mod_eq_of_lt (by omega : 1 < w.length), hv1]
      | inr r1 =>
        rw [hv1] at h01; exact False.elim h01
  have hV_side : ∀ t, (Even t → ∃ l, V t = Sum.inl l) ∧ (¬ Even t → ∃ r, V t = Sum.inr r) := by
    intro t
    induction t with
    | zero =>
      exact ⟨fun _ => hV0_left, fun h => (h ⟨0, rfl⟩).elim⟩
    | succ t ih =>
      constructor
      · intro hev
        have hodd : ¬ Even t := by obtain ⟨j, hj⟩ := hev; intro ⟨i, hi⟩; omega
        obtain ⟨r, hr⟩ := ih.2 hodd
        have hadj := hV_adj t
        rw [hr] at hadj
        cases hv : V (t + 1) with
        | inl l => exact ⟨l, rfl⟩
        | inr r' => rw [hv] at hadj; exact False.elim hadj
      · intro hodd
        have hev : Even t := by
          rw [Nat.not_even_iff_odd] at hodd
          obtain ⟨j, hj⟩ := hodd; exact ⟨j, by omega⟩
        obtain ⟨l, hl⟩ := ih.1 hev
        have hadj := hV_adj t
        rw [hl] at hadj
        cases hv : V (t + 1) with
        | inl l' => rw [hv] at hadj; exact False.elim hadj
        | inr r => exact ⟨r, rfl⟩
  have hev_len : Even w.length := by
    by_contra hodd
    obtain ⟨r, hr⟩ := (hV_side w.length).2 hodd
    obtain ⟨l0, hl0⟩ := hV0_left
    have hper : V w.length = V 0 := by
      simp [V, Nat.add_mod_left]
    rw [hper, hl0] at hr
    cases hr
  obtain ⟨m, hm_eq⟩ := hev_len
  have hlen : w.length = 2 * m := by omega
  have hm1 : 1 ≤ m := by omega
  let Lseq : ℕ → LambdaLeft k F := fun j =>
    Classical.choose ((hV_side (2 * j)).1 ⟨j, by omega⟩)
  let Rseq : ℕ → LambdaRight k F := fun j =>
    Classical.choose ((hV_side (2 * j + 1)).2 (by intro ⟨i, hi⟩; omega))
  have hLseq : ∀ j, V (2 * j) = Sum.inl (Lseq j) := fun j =>
    Classical.choose_spec ((hV_side (2 * j)).1 ⟨j, by omega⟩)
  have hRseq : ∀ j, V (2 * j + 1) = Sum.inr (Rseq j) := fun j =>
    Classical.choose_spec ((hV_side (2 * j + 1)).2 (by intro ⟨i, hi⟩; omega))
  have hadj_LR : ∀ j, lambdaAdj (Lseq j).1 (Rseq j).1 := by
    intro j
    have h := hV_adj (2 * j)
    rw [hLseq j, hRseq j] at h
    exact h
  have hadj_RL : ∀ j, lambdaAdj (Lseq (j + 1)).1 (Rseq j).1 := by
    intro j
    have h := hV_adj (2 * j + 1)
    have h2 : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
    rw [h2, hRseq j, hLseq (j + 1)] at h
    exact h
  let uStep : ℕ → F := fun j => (Lseq (j + 1)).1 ⟨0, by omega⟩ - (Lseq j).1 ⟨0, by omega⟩
  let vStep : ℕ → F := fun j => (Rseq (j + 1)).1 ⟨0, by omega⟩ - (Rseq j).1 ⟨0, by omega⟩
  have hu_nz : ∀ j, uStep j ≠ 0 := by
    intro j h0
    have heq0 : (Lseq j).1 ⟨0, by omega⟩ = (Lseq (j + 1)).1 ⟨0, by omega⟩ :=
      (sub_eq_zero.mp h0).symm
    have hL_eq : Lseq j = Lseq (j + 1) :=
      lambdaLeft_eq_of_adj_of_zero_eq hk (hadj_LR j) (hadj_RL j) heq0
    have hVeq : V (2 * j) = V (2 * j + 2) := by
      have h2 : 2 * j + 2 = 2 * (j + 1) := by omega
      rw [h2, hLseq j, hLseq (j + 1), hL_eq]
    exact hV_ne2 (2 * j) hVeq
  have hv_nz : ∀ j, vStep j ≠ 0 := by
    intro j h0
    have heq0 : (Rseq j).1 ⟨0, by omega⟩ = (Rseq (j + 1)).1 ⟨0, by omega⟩ :=
      (sub_eq_zero.mp h0).symm
    have hR_eq : Rseq j = Rseq (j + 1) :=
      lambdaRight_eq_of_adj_of_zero_eq hk (hadj_RL j) (hadj_LR (j + 1)) heq0
    have hVeq : V (2 * j + 1) = V (2 * j + 1 + 2) := by
      have h2 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by omega
      rw [h2, hRseq j, hRseq (j + 1), hR_eq]
    exact hV_ne2 (2 * j + 1) hVeq
  let wsOf : ℕ → List F := Nat.rec [] (fun j acc => vStep j :: uStep j :: acc)
  have hws_len : ∀ n, (wsOf n).length = 2 * n := by
    intro n; induction n with
    | zero => rfl
    | succ j ih => simp [wsOf, ih]; omega
  have hws_nz : ∀ n, ∀ x ∈ wsOf n, x ≠ 0 := by
    intro n; induction n with
    | zero => intro x hx; cases hx
    | succ j ih =>
      intro x hx
      simp only [wsOf, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hv_nz j
      · exact hu_nz j
      · exact ih x hx
  have hN_bounds :
      N10 k ≤ N00 k + 1 ∧ N11 k ≤ N01 k + 1 ∧ N00 k ≤ N10 k + 1 ∧ N01 k ≤ N11 k + 1 := by
    unfold N00 N01 N10 N11; omega
  have hwalk : ∀ n, PolyMat2.MatModEq (N00 k) (N01 k) (N10 k) (N11 k)
      (stateMat (Lseq n) (Rseq n))
      (PolyMat2.mul (PolyMat2.wordU (wsOf n)) (stateMat (Lseq 0) (Rseq 0))) := by
    intro n
    induction n with
    | zero =>
      change PolyMat2.MatModEq (N00 k) (N01 k) (N10 k) (N11 k)
        (stateMat (Lseq 0) (Rseq 0))
        (PolyMat2.mul (PolyMat2.wordU []) (stateMat (Lseq 0) (Rseq 0)))
      rw [PolyMat2.wordU_nil, PolyMat2.mat_one_mul]
      exact ⟨PolyMat2.polyModEq_refl _ _, PolyMat2.polyModEq_refl _ _,
        PolyMat2.polyModEq_refl _ _, PolyMat2.polyModEq_refl _ _⟩
    | succ j ih =>
      have hstepL := stateMat_stepL hk (hadj_LR j) (hadj_RL j)
      have hstepR := stateMat_stepR hk (hadj_RL j) (hadj_LR (j + 1))
      have h1 := PolyMat2.matModEq_stepL_mul hN_bounds.1 hN_bounds.2.1 (uStep j) ih
      have h2 := PolyMat2.matModEq_trans hstepL h1
      have h3 := PolyMat2.matModEq_stepU_mul hN_bounds.2.2.1 hN_bounds.2.2.2 (vStep j) h2
      have h4 := PolyMat2.matModEq_trans hstepR h3
      have hword : PolyMat2.wordU (wsOf (j + 1)) =
          PolyMat2.mul (PolyMat2.stepU (vStep j))
            (PolyMat2.mul (PolyMat2.stepL (uStep j)) (PolyMat2.wordU (wsOf j))) := by
        simp only [wsOf, PolyMat2.wordU_cons, PolyMat2.wordL_cons]
      rw [hword, PolyMat2.mat_mul_assoc, PolyMat2.mat_mul_assoc]
      exact h4
  have hLm : Lseq m = Lseq 0 := by
    have h1 := hLseq m
    have h2 := hLseq 0
    have hper : V (2 * m) = V 0 := by simp [V, ← hlen, Nat.add_mod_left]
    rw [hper, h2] at h1
    exact Sum.inl.inj h1.symm
  have hRm : Rseq m = Rseq 0 := by
    have h1 := hRseq m
    have h2 := hRseq 0
    have hper : V (2 * m + 1) = V 1 := by
      have : 2 * m + 1 + off = w.length + (1 + off) := by omega
      simp [V, this, Nat.add_mod_left]
    rw [hper, h2] at h1
    exact Sum.inr.inj h1.symm
  have hfix := hwalk m
  rw [hLm, hRm] at hfix
  have hgk := gK_le_length_of_fixed_stateMat hk
    (by rw [hws_len]; omega)
    ⟨m, by rw [hws_len]; omega⟩
    (hws_nz m)
    hfix
  rw [hws_len, ← hlen] at hgk
  exact hgk

/-- Universal girth lower bound on `Λ_{k, F}`: `(gK k : ℕ∞) ≤ (lambdaGraph k F).egirth`. -/
theorem lambdaGraph_egirth_ge_gK {k : ℕ} (hk : 2 ≤ k) (F : Type*) [Field F] :
    (gK k : ℕ∞) ≤ (lambdaGraph k F).egirth :=
  SimpleGraph.le_egirth.mpr fun _ _ hw => Nat.cast_le.mpr (lambdaGraph_isCycle_length_ge hk hw)

/-- **Headline Theorem 1 (Universal Girth Lower Bound):**
For every integer `k ≥ 2` and every field `F`, `(gK k : ℕ∞) ≤ (lazebnikUstimenkoD k F).egirth`. -/
theorem lazebnikUstimenko_girth_lower_bound :
    LazebnikUstimenkoGirthLowerBoundStatement.{u} := by
  intro k hk F _
  rw [lazebnikUstimenkoD_egirth_eq_lambdaGraph_egirth hk F]
  exact lambdaGraph_egirth_ge_gK hk F

end LeanForgeDkq.LazebnikUstimenko

end
