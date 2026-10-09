/-
Certificate for Theorem S1 (singular-value defect inequality) of the Supplemental Material of
G. Adesso, "Optimality of Gaussian entanglement of formation" (arXiv:2608.01909v3):

    G_t(C) ≥ ∑_n (n+1) d_n²,   d_n = (t c_n − c_{n+1})₊,

for decreasing Schmidt coefficients c_n ≥ 0 and 0 < t ≤ 1, in the Schmidt-basis matrix model:
    G_t(C) = ∑_{i,j} |t c_i X_ij − c_j Y_ij|²            (Eq. S:Gmatrix),
with the index identities ∑_j |X_ij|² − ∑_j |X_ji|² = 1 (and the same for Y) for every
index with c_i > 0 (Eq. S:index).

Certified: the positive-drop lemma (S:drop), the pointwise bound (S:pointwise) in both cases
i < j and i > j, the telescoping (S:defectN), and the limit N → ∞, for decreasing spectra
indexed by ℕ (finite or infinite support). Inputs: the matrix model (S:Gmatrix), i.e.
X = U†aU, Y = V†aV in paired Schmidt bases indexed by ℕ, and the index identities (S:index),
which follow from [a, a†] = 1. Paired bases indexed by ℕ exist for every state of finite Schmidt
rank (both kernels are infinite dimensional) and for infinite rank when the two kernels have equal
dimension; the remaining states are reached by the truncation limit (`Corollaries.lean`).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Thm2Cert.MatrixLemma

open Finset

set_option autoImplicit false

noncomputable section

namespace Thm1Cert

/-- `ite_t` / `ite_f` without deprecation warnings. -/
theorem ite_t {α : Sort*} {p : Prop} [Decidable p] (h : p) {a b : α} :
    (if p then a else b) = a := by simp [h]

theorem ite_f {α : Sort*} {p : Prop} [Decidable p] (h : ¬ p) {a b : α} :
    (if p then a else b) = b := by simp [h]

/-- Positive part. -/
def pos (x : ℝ) : ℝ := max x 0

lemma pos_nonneg (x : ℝ) : 0 ≤ pos x := le_max_right _ _

lemma le_pos (x : ℝ) : x ≤ pos x := le_max_left _ _

lemma pos_mul_self (x : ℝ) : x * pos x = pos x ^ 2 := by
  unfold pos
  rcases le_total x 0 with h | h
  · rw [max_eq_right h]; ring
  · rw [max_eq_left h]; ring

variable (t : ℝ) (c : ℕ → ℝ)

/-- The positive drops `d_n = (t c_n − c_{n+1})₊`. -/
def dd (n : ℕ) : ℝ := pos (t * c n - c (n + 1))

/-! ## Positive-drop lemma (S:drop) -/

/-- `D_ij = ∑_{k=i}^{j-1} (t c_k − c_{k+1})₊ ≤ (t c_i − c_j)₊` for `i ≤ j`. -/
theorem drop_lemma {t : ℝ} {c : ℕ → ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : Antitone c)
    (hc0 : ∀ n, 0 ≤ c n) {i j : ℕ} (hij : i ≤ j) :
    ∑ k ∈ Ico i j, dd t c k ≤ pos (t * c i - c j) := by
  induction j, hij using Nat.le_induction with
  | base =>
    simp only [Ico_self, sum_empty]; exact pos_nonneg _
  | succ j hij ih =>
    rw [sum_Ico_succ_top hij]
    have hcj : c j ≤ c i := hc hij
    have hcj1 : c (j + 1) ≤ c j := hc (Nat.le_succ j)
    have hc1 := hc0 (j + 1)
    unfold dd pos at *
    -- (t c_i − c_j)₊ + (t c_j − c_{j+1})₊ ≤ (t c_i − c_{j+1})₊
    have key : max (t * c i - c j) 0 + max (t * c j - c (j + 1)) 0
        ≤ max (t * c i - c (j + 1)) 0 := by
      have h1 : t * c j ≤ t * c i := mul_le_mul_of_nonneg_left hcj ht0
      have h2 : t * c j ≤ c j := by nlinarith [hc0 j]
      simp only [max_def]
      split_ifs <;> linarith
    linarith

/-! ## Pointwise bound (S:pointwise) -/

/-- Real form of the case `i < j`: for `0 ≤ D ≤ (A − B)₊`, `A, B ≥ 0`,
`(A a − B b)² − A D a² + B D b² ≥ 0`. -/
lemma real_case_lt {A B D : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hD0 : 0 ≤ D) (hD : D ≤ pos (A - B))
    (a b : ℝ) : 0 ≤ (A * a - B * b) ^ 2 - A * D * a ^ 2 + B * D * b ^ 2 := by
  rcases hD0.eq_or_lt with h0 | hpos
  · subst h0; nlinarith [sq_nonneg (A * a - B * b)]
  · have hAB : D ≤ A - B := by
      unfold pos at hD
      rcases le_total (A - B) 0 with h | h
      · rw [max_eq_right h] at hD; linarith
      · rwa [max_eq_left h] at hD
    have e : (A * a - B * b) ^ 2 - A * D * a ^ 2 + B * D * b ^ 2
        = (A * (A - D)) * a ^ 2 - 2 * (A * B) * a * b + (B * (B + D)) * b ^ 2 := by ring
    rw [e]
    have := Thm2Cert.quad_nonneg (a := A * (A - D)) (c := B * (B + D)) (d := A * B)
      (mul_nonneg hA (by linarith)) (by nlinarith [mul_nonneg (mul_nonneg hA hB) hpos.le])
      (mul_nonneg hB (by linarith)) a b
    linarith

/-- Real form of the case `i > j`: for `0 ≤ D ≤ (t B − C)₊`, `A = t C`, `C ≤ B`, `t ≤ 1`,
`(A a − B b)² + A D a² − B D b² ≥ 0`. -/
lemma real_case_gt {t Cc B D : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hC : 0 ≤ Cc) (hCB : Cc ≤ B)
    (hD0 : 0 ≤ D) (hD : D ≤ pos (t * B - Cc)) (a b : ℝ) :
    0 ≤ (t * Cc * a - B * b) ^ 2 + t * Cc * D * a ^ 2 - B * D * b ^ 2 := by
  have hB : 0 ≤ B := hC.trans hCB
  rcases hD0.eq_or_lt with h0 | hpos
  · subst h0; nlinarith [sq_nonneg (t * Cc * a - B * b)]
  · have hDB : D ≤ t * B - Cc := by
      unfold pos at hD
      rcases le_total (t * B - Cc) 0 with h | h
      · rw [max_eq_right h] at hD; linarith
      · rwa [max_eq_left h] at hD
    have hA : 0 ≤ t * Cc := mul_nonneg ht0 hC
    have hBD : D ≤ B := by nlinarith
    have hgap : 0 ≤ B - t * Cc - D := by nlinarith
    have e : (t * Cc * a - B * b) ^ 2 + t * Cc * D * a ^ 2 - B * D * b ^ 2
        = (t * Cc * (t * Cc + D)) * a ^ 2 - 2 * (t * Cc * B) * a * b + (B * (B - D)) * b ^ 2 := by
      ring
    rw [e]
    have := Thm2Cert.quad_nonneg (a := t * Cc * (t * Cc + D)) (c := B * (B - D))
      (d := t * Cc * B) (mul_nonneg hA (by linarith))
      (by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hA hB) hpos.le) hgap])
      (mul_nonneg hB (by linarith)) a b
    linarith

lemma norm_sq_ge (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (x y : ℂ) :
    (A * ‖x‖ - B * ‖y‖) ^ 2 ≤ ‖(A : ℂ) * x - (B : ℂ) * y‖ ^ 2 := by
  have h := abs_norm_sub_norm_le ((A : ℂ) * x) ((B : ℂ) * y)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hA,
    Real.norm_of_nonneg hB] at h
  have h0 : 0 ≤ ‖(A : ℂ) * x - (B : ℂ) * y‖ := norm_nonneg _
  have := sq_le_sq' (abs_le.mp h).1 (abs_le.mp h).2
  exact this

/-! ## Dual potentials -/

/-- Truncated positive drops: `δ_k = d_k` for `k ≤ N`, `0` otherwise. -/
def dlt (N k : ℕ) : ℝ := if k ≤ N then dd t c k else 0

/-- `α_i = ∑_{k ≥ i} t c_k δ_k`. -/
def alpha (N i : ℕ) : ℝ := ∑ k ∈ Ico i (N + 1), t * c k * dlt t c N k

/-- `β_i = −∑_{k ≥ i} c_{k+1} δ_k`. -/
def beta (N i : ℕ) : ℝ := -∑ k ∈ Ico i (N + 1), c (k + 1) * dlt t c N k

lemma sum_Ico_trunc (N : ℕ) (g : ℕ → ℝ) (hg : ∀ k, N < k → g k = 0) {i j : ℕ} (hij : i ≤ j) :
    ∑ k ∈ Ico i (N + 1), g k - ∑ k ∈ Ico j (N + 1), g k = ∑ k ∈ Ico i j, g k := by
  rcases le_total j (N + 1) with hj | hj
  · rw [← sum_Ico_consecutive g hij hj]; ring
  · have e1 : ∑ k ∈ Ico j (N + 1), g k = 0 := by rw [Ico_eq_empty_of_le hj, sum_empty]
    rw [e1, sub_zero]
    rcases le_total i (N + 1) with hi | hi
    · rw [← sum_Ico_consecutive g hi hj]
      have : ∑ k ∈ Ico (N + 1) j, g k = 0 :=
        sum_eq_zero (fun k hk => hg k (by simp at hk; omega))
      rw [this, add_zero]
    · rw [Ico_eq_empty_of_le hi, sum_empty]
      exact (sum_eq_zero (fun k hk => hg k (by simp at hk; omega))).symm

variable {t c}

lemma dd_nonneg (k : ℕ) : 0 ≤ dd t c k := pos_nonneg _

lemma dlt_nonneg (N k : ℕ) : 0 ≤ dlt t c N k := by
  unfold dlt; split_ifs
  · exact dd_nonneg k
  · exact le_rfl

lemma dlt_le (N k : ℕ) : dlt t c N k ≤ dd t c k := by
  unfold dlt; split_ifs
  · exact le_rfl
  · exact dd_nonneg k

/-- **Eq. (S:pointwise)**: `|t c_i x − c_j y|² ≥ (α_i − α_j)|x|² + (β_i − β_j)|y|²`. -/
theorem pointwise (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hc : Antitone c) (hc0 : ∀ n, 0 ≤ c n)
    (N i j : ℕ) (x y : ℂ) :
    (alpha t c N i - alpha t c N j) * ‖x‖ ^ 2 + (beta t c N i - beta t c N j) * ‖y‖ ^ 2
      ≤ ‖((t * c i : ℝ) : ℂ) * x - (c j : ℂ) * y‖ ^ 2 := by
  have hn := norm_sq_ge (t * c i) (c j) (mul_nonneg ht0 (hc0 i)) (hc0 j) x y
  have hg1 : ∀ k, N < k → t * c k * dlt t c N k = 0 := by
    intro k hk; unfold dlt; simp only [show ¬ k ≤ N by omega, ↓reduceIte]; ring
  have hg2 : ∀ k, N < k → c (k + 1) * dlt t c N k = 0 := by
    intro k hk; unfold dlt; simp only [show ¬ k ≤ N by omega, ↓reduceIte]; ring
  rcases lt_trichotomy i j with hij | hij | hij
  · -- i < j
    have hA := sum_Ico_trunc N _ hg1 hij.le
    have hB := sum_Ico_trunc N _ hg2 hij.le
    set D := ∑ k ∈ Ico i j, dlt t c N k
    have hD0 : 0 ≤ D := sum_nonneg (fun k _ => dlt_nonneg N k)
    have hD : D ≤ pos (t * c i - c j) :=
      (sum_le_sum (fun k _ => dlt_le N k)).trans (drop_lemma ht0 ht1 hc hc0 hij.le)
    have hP : ∑ k ∈ Ico i j, t * c k * dlt t c N k ≤ t * c i * D := by
      rw [mul_sum]
      exact sum_le_sum (fun k hk => by
        simp only [mem_Ico] at hk
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hc hk.1) ht0) (dlt_nonneg N k))
    have hQ : c j * D ≤ ∑ k ∈ Ico i j, c (k + 1) * dlt t c N k := by
      rw [mul_sum]
      exact sum_le_sum (fun k hk => by
        simp only [mem_Ico] at hk
        exact mul_le_mul_of_nonneg_right (hc (by omega)) (dlt_nonneg N k))
    have hreal := real_case_lt (mul_nonneg ht0 (hc0 i)) (hc0 j) hD0 hD ‖x‖ ‖y‖
    unfold alpha beta
    rw [hA, show -∑ k ∈ Ico i (N + 1), c (k + 1) * dlt t c N k
        - -∑ k ∈ Ico j (N + 1), c (k + 1) * dlt t c N k
        = -(∑ k ∈ Ico i (N + 1), c (k + 1) * dlt t c N k
          - ∑ k ∈ Ico j (N + 1), c (k + 1) * dlt t c N k) by ring, hB]
    have i1 := mul_le_mul_of_nonneg_right hP (sq_nonneg ‖x‖)
    have i2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg ‖y‖)
    nlinarith
  · subst hij
    unfold alpha beta
    simp only [sub_self, zero_mul, add_zero]
    exact sq_nonneg _
  · -- i > j
    have hA := sum_Ico_trunc N _ hg1 hij.le
    have hB := sum_Ico_trunc N _ hg2 hij.le
    set D := ∑ k ∈ Ico j i, dlt t c N k
    have hD0 : 0 ≤ D := sum_nonneg (fun k _ => dlt_nonneg N k)
    have hD : D ≤ pos (t * c j - c i) :=
      (sum_le_sum (fun k _ => dlt_le N k)).trans (drop_lemma ht0 ht1 hc hc0 hij.le)
    have hP : t * c i * D ≤ ∑ k ∈ Ico j i, t * c k * dlt t c N k := by
      rw [mul_sum]
      exact sum_le_sum (fun k hk => by
        simp only [mem_Ico] at hk
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hc hk.2.le) ht0) (dlt_nonneg N k))
    have hQ : ∑ k ∈ Ico j i, c (k + 1) * dlt t c N k ≤ c j * D := by
      rw [mul_sum]
      exact sum_le_sum (fun k hk => by
        simp only [mem_Ico] at hk
        exact mul_le_mul_of_nonneg_right (hc (by omega)) (dlt_nonneg N k))
    have hreal := real_case_gt ht0 ht1 (hc0 i) (hc hij.le) hD0 hD ‖x‖ ‖y‖
    unfold alpha beta
    have eA : ∑ k ∈ Ico i (N + 1), t * c k * dlt t c N k
        - ∑ k ∈ Ico j (N + 1), t * c k * dlt t c N k
        = -∑ k ∈ Ico j i, t * c k * dlt t c N k := by linarith
    have eB : -∑ k ∈ Ico i (N + 1), c (k + 1) * dlt t c N k
        - -∑ k ∈ Ico j (N + 1), c (k + 1) * dlt t c N k
        = ∑ k ∈ Ico j i, c (k + 1) * dlt t c N k := by linarith
    rw [eA, eB]
    have i1 := mul_le_mul_of_nonneg_right hP (sq_nonneg ‖x‖)
    have i2 := mul_le_mul_of_nonneg_right hQ (sq_nonneg ‖y‖)
    nlinarith

/-! ## Telescoping (S:defectN) -/

lemma sum_alpha_beta (N : ℕ) :
    ∑ i ∈ range (N + 1), (alpha t c N i + beta t c N i)
      = ∑ k ∈ range (N + 1), ((k : ℝ) + 1) * dd t c k ^ 2 := by
  have h1 : ∀ i, alpha t c N i + beta t c N i
      = ∑ k ∈ Ico i (N + 1), (t * c k - c (k + 1)) * dlt t c N k := by
    intro i; unfold alpha beta; rw [← sub_eq_add_neg, ← sum_sub_distrib]
    exact sum_congr rfl (fun k _ => by ring)
  simp only [h1]
  rw [sum_comm' (t' := range (N + 1)) (s' := fun k => range (k + 1))
    (h := fun i k => by simp only [mem_range, mem_Ico]; omega)]
  refine sum_congr rfl (fun k hk => ?_)
  simp only [mem_range] at hk
  rw [sum_const, card_range, nsmul_eq_mul]
  unfold dlt; simp only [show k ≤ N by omega, ↓reduceIte]
  unfold dd
  rw [pos_mul_self]
  push_cast; ring

/-! ## Theorem S1 -/

/-- **Theorem S1** (singular-value defect inequality), matrix model.
`hG`: `G = ∑_{i,j} |t c_i X_ij − c_j Y_ij|²`; `hX`, `hY`: the index identities (S:index),
required only for indices with `c_i > 0`. Conclusion: `∑_{n ≤ N} (n+1) d_n² ≤ G` for every `N`,
hence `∑_n (n+1) d_n²` converges and is `≤ G`. -/
theorem defect_inequality (ht0 : 0 < t) (ht1 : t ≤ 1) (hc : Antitone c) (hc0 : ∀ n, 0 ≤ c n)
    (X Y : ℕ → ℕ → ℂ) (G : ℝ)
    (hG : HasSum (fun ij : ℕ × ℕ => ‖((t * c ij.1 : ℝ) : ℂ) * X ij.1 ij.2
      - (c ij.2 : ℂ) * Y ij.1 ij.2‖ ^ 2) G)
    (rX cX rY cY : ℕ → ℝ)
    (hrX : ∀ i, 0 < c i → HasSum (fun j => ‖X i j‖ ^ 2) (rX i))
    (hcX : ∀ i, 0 < c i → HasSum (fun j => ‖X j i‖ ^ 2) (cX i))
    (hrY : ∀ i, 0 < c i → HasSum (fun j => ‖Y i j‖ ^ 2) (rY i))
    (hcY : ∀ i, 0 < c i → HasSum (fun j => ‖Y j i‖ ^ 2) (cY i))
    (hX : ∀ i, 0 < c i → rX i - cX i = 1) (hY : ∀ i, 0 < c i → rY i - cY i = 1) (N : ℕ) :
    ∑ k ∈ range (N + 1), ((k : ℝ) + 1) * dd t c k ^ 2 ≤ G := by
  rw [← sum_alpha_beta]
  -- potentials vanish where c_i = 0
  have hα0 : ∀ i, c i = 0 → alpha t c N i = 0 := by
    intro i hi; unfold alpha
    exact sum_eq_zero (fun k hk => by
      simp only [mem_Ico] at hk
      have : c k = 0 := le_antisymm (hi ▸ hc hk.1) (hc0 k)
      rw [this]; ring)
  have hβ0 : ∀ i, c i = 0 → beta t c N i = 0 := by
    intro i hi; unfold beta
    rw [neg_eq_zero]
    exact sum_eq_zero (fun k hk => by
      simp only [mem_Ico] at hk
      have : c (k + 1) = 0 := le_antisymm (hi ▸ hc (by omega)) (hc0 _)
      rw [this]; ring)
  have hαN : ∀ i, N < i → alpha t c N i = 0 := by
    intro i hi; unfold alpha; rw [Ico_eq_empty_of_le (by omega), sum_empty]
  have hβN : ∀ i, N < i → beta t c N i = 0 := by
    intro i hi; unfold beta; rw [Ico_eq_empty_of_le (by omega), sum_empty, neg_zero]
  -- lower bound on the K × K box
  set R : ℕ → ℝ := fun K => ∑ i ∈ range (N + 1),
    (alpha t c N i * (∑ j ∈ range K, ‖X i j‖ ^ 2 - ∑ j ∈ range K, ‖X j i‖ ^ 2)
      + beta t c N i * (∑ j ∈ range K, ‖Y i j‖ ^ 2 - ∑ j ∈ range K, ‖Y j i‖ ^ 2)) with hR
  have hbox : ∀ K, N + 1 ≤ K → R K ≤ G := by
    intro K hK
    have h1 : ∑ ij ∈ range K ×ˢ range K, ‖((t * c ij.1 : ℝ) : ℂ) * X ij.1 ij.2
        - (c ij.2 : ℂ) * Y ij.1 ij.2‖ ^ 2 ≤ G :=
      sum_le_hasSum _ (fun _ _ => sq_nonneg _) hG
    have h2 : ∑ ij ∈ range K ×ˢ range K,
        ((alpha t c N ij.1 - alpha t c N ij.2) * ‖X ij.1 ij.2‖ ^ 2
          + (beta t c N ij.1 - beta t c N ij.2) * ‖Y ij.1 ij.2‖ ^ 2)
        ≤ ∑ ij ∈ range K ×ˢ range K, ‖((t * c ij.1 : ℝ) : ℂ) * X ij.1 ij.2
          - (c ij.2 : ℂ) * Y ij.1 ij.2‖ ^ 2 :=
      sum_le_sum (fun ij _ => pointwise ht0.le ht1 hc hc0 N ij.1 ij.2 _ _)
    have h3 : ∑ ij ∈ range K ×ˢ range K,
        ((alpha t c N ij.1 - alpha t c N ij.2) * ‖X ij.1 ij.2‖ ^ 2
          + (beta t c N ij.1 - beta t c N ij.2) * ‖Y ij.1 ij.2‖ ^ 2) = R K := by
      rw [sum_product]
      have hsplit : ∀ (P : ℕ → ℝ) (Z : ℕ → ℕ → ℂ), (∀ i, N < i → P i = 0) →
          ∑ i ∈ range K, ∑ j ∈ range K, (P i - P j) * ‖Z i j‖ ^ 2
            = ∑ i ∈ range (N + 1),
              P i * (∑ j ∈ range K, ‖Z i j‖ ^ 2 - ∑ j ∈ range K, ‖Z j i‖ ^ 2) := by
        intro P Z hP
        have e : ∑ i ∈ range K, ∑ j ∈ range K, (P i - P j) * ‖Z i j‖ ^ 2
            = ∑ i ∈ range K, P i * (∑ j ∈ range K, ‖Z i j‖ ^ 2 - ∑ j ∈ range K, ‖Z j i‖ ^ 2) := by
          simp only [sub_mul, sum_sub_distrib, mul_sub, mul_sum]
          rw [sum_comm (s := range K) (t := range K)
            (f := fun i j => P j * ‖Z i j‖ ^ 2)]
        rw [e, ← sum_range_add_sum_Ico _ hK]
        have : ∑ i ∈ Ico (N + 1) K,
            P i * (∑ j ∈ range K, ‖Z i j‖ ^ 2 - ∑ j ∈ range K, ‖Z j i‖ ^ 2) = 0 :=
          sum_eq_zero (fun i hi => by simp at hi; rw [hP i (by omega), zero_mul])
        rw [this, add_zero]
      have e2 : ∑ i ∈ range K, ∑ j ∈ range K,
          ((alpha t c N i - alpha t c N j) * ‖X i j‖ ^ 2
            + (beta t c N i - beta t c N j) * ‖Y i j‖ ^ 2)
          = ∑ i ∈ range K, ∑ j ∈ range K, (alpha t c N i - alpha t c N j) * ‖X i j‖ ^ 2
            + ∑ i ∈ range K, ∑ j ∈ range K, (beta t c N i - beta t c N j) * ‖Y i j‖ ^ 2 := by
        rw [← sum_add_distrib]; exact sum_congr rfl (fun i _ => sum_add_distrib)
      rw [e2, hsplit _ X hαN, hsplit _ Y hβN, hR, ← sum_add_distrib]
    linarith
  -- limit K → ∞
  have hlim : Filter.Tendsto R Filter.atTop
      (nhds (∑ i ∈ range (N + 1), (alpha t c N i + beta t c N i))) := by
    rw [hR]
    have : ∑ i ∈ range (N + 1), (alpha t c N i + beta t c N i)
        = ∑ i ∈ range (N + 1), (alpha t c N i * (rX i - cX i)
          + beta t c N i * (rY i - cY i)) := by
      refine sum_congr rfl (fun i _ => ?_)
      rcases (hc0 i).eq_or_lt with h0 | hpos
      · rw [hα0 i h0.symm, hβ0 i h0.symm]; ring
      · rw [hX i hpos, hY i hpos]; ring
    rw [this]
    refine tendsto_finsetSum _ (fun i _ => ?_)
    rcases (hc0 i).eq_or_lt with h0 | hpos
    · simp only [hα0 i h0.symm, hβ0 i h0.symm, zero_mul, add_zero]
      exact tendsto_const_nhds
    · refine Filter.Tendsto.add (Filter.Tendsto.const_mul _ ?_) (Filter.Tendsto.const_mul _ ?_)
      · exact ((hrX i hpos).tendsto_sum_nat).sub ((hcX i hpos).tendsto_sum_nat)
      · exact ((hrY i hpos).tendsto_sum_nat).sub ((hcY i hpos).tendsto_sum_nat)
  exact le_of_tendsto hlim (Filter.eventually_atTop.mpr ⟨N + 1, hbox⟩)

/-- Consequence: the defect series converges and `∑_n (n+1) d_n² ≤ G_t(C)`. -/
theorem defect_inequality_tsum (ht0 : 0 < t) (ht1 : t ≤ 1) (hc : Antitone c)
    (hc0 : ∀ n, 0 ≤ c n) (X Y : ℕ → ℕ → ℂ) (G : ℝ)
    (hG : HasSum (fun ij : ℕ × ℕ => ‖((t * c ij.1 : ℝ) : ℂ) * X ij.1 ij.2
      - (c ij.2 : ℂ) * Y ij.1 ij.2‖ ^ 2) G)
    (rX cX rY cY : ℕ → ℝ)
    (hrX : ∀ i, 0 < c i → HasSum (fun j => ‖X i j‖ ^ 2) (rX i))
    (hcX : ∀ i, 0 < c i → HasSum (fun j => ‖X j i‖ ^ 2) (cX i))
    (hrY : ∀ i, 0 < c i → HasSum (fun j => ‖Y i j‖ ^ 2) (rY i))
    (hcY : ∀ i, 0 < c i → HasSum (fun j => ‖Y j i‖ ^ 2) (cY i))
    (hX : ∀ i, 0 < c i → rX i - cX i = 1) (hY : ∀ i, 0 < c i → rY i - cY i = 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) * dd t c n ^ 2) ∧
    ∑' n : ℕ, ((n : ℝ) + 1) * dd t c n ^ 2 ≤ G := by
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * dd t c n ^ 2 := fun n => by positivity
  have hb : ∀ n, ∑ i ∈ range n, ((i : ℝ) + 1) * dd t c i ^ 2 ≤ G := by
    intro n
    rcases n with _ | n
    · simp only [range_zero, sum_empty]
      exact hG.nonneg (fun _ => sq_nonneg _)
    · exact defect_inequality ht0 ht1 hc hc0 X Y G hG rX cX rY cY hrX hcX hrY hcY hX hY n
  exact ⟨summable_of_sum_range_le hnn hb, Real.tsum_le_of_sum_range_le hnn hb⟩

end Thm1Cert
