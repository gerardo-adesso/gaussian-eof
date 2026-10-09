/-
Certificate for the exact identity Eq. (S:mainid) of the Supplemental Material:
adding the two second variations Q(O₁ψ), Q(O₂ψ) of Eq. (S:Q12), and using the sum rules
Eq. (S:wccr), gives  −∑_{l,r} c_l c_r z†_{lr} M(x_{lr}) z_{lr}.

Input (taken as hypotheses / definitions, NOT derived here): the expressions (S:Q12) for the
second variations, and the sum rules ⟨N⟩ = ∑ p_r|A_lr|², ⟨N⟩+1 = ∑ p_l|A_lr|².
Setting: a finite index set. `mainid` is Eq. (S:mainid) verbatim, for Schmidt coefficients
c_l > 0, with p_l = c_l², L_lr = (ln p_l − ln p_r)/(p_l − p_r) (= 1/p_l if p_l = p_r),
x_lr = ln(c_l/c_r). `mainid_general` / `sumQ_nonpos_general` allow c_l ≥ 0, so that kernel
directions (support-to-kernel entries, retained in the text as continuous limits) are included;
this covers every state of finite Schmidt rank. Infinite Schmidt rank (the limiting argument of
the SM) is not covered.
-/
import Thm2Cert.MatrixLemma
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Finset

set_option autoImplicit false

noncomputable section

namespace Thm2Cert

/-- The logarithmic mean kernel `L(p,p') = (ln p − ln p')/(p − p')`, `= 1/p` on the diagonal. -/
def Lker (p p' : ℝ) : ℝ := if p = p' then 1 / p else (log p - log p') / (p - p')

section scalar

variable {cl cr : ℝ}

lemma E1 (hl : 0 < cl) (hr : 0 < cr) : cl * cr * exp (log (cl / cr)) = cl ^ 2 := by
  rw [exp_log (div_pos hl hr)]; field_simp

lemma E2 (hl : 0 < cl) (hr : 0 < cr) : cl * cr * exp (-log (cl / cr)) = cr ^ 2 := by
  rw [exp_neg, exp_log (div_pos hl hr)]; field_simp

lemma E3 (hl : 0 < cl) (hr : 0 < cr) :
    cl ^ 2 * cr ^ 2 * Lker (cl ^ 2) (cr ^ 2) = cl * cr * f (log (cl / cr)) := by
  unfold Lker
  by_cases h : cl ^ 2 = cr ^ 2
  · have hlr : cl = cr := (pow_left_inj₀ hl.le hr.le two_ne_zero).mp h
    subst hlr
    simp only [↓reduceIte]
    rw [div_self hl.ne', log_one, f_zero]
    field_simp
  · simp only [h, ↓reduceIte]
    have hlr : cl ≠ cr := fun e => h (by rw [e])
    have hq : cl / cr ≠ 1 := by
      intro e; apply hlr; field_simp at e; linarith
    have hX : log (cl / cr) ≠ 0 := log_ne_zero_of_pos_of_ne_one (div_pos hl hr) hq
    unfold f
    simp only [hX, ↓reduceIte]
    rw [sinh_eq, exp_neg, exp_log (div_pos hl hr), log_pow, log_pow,
      log_div hl.ne' hr.ne']
    have h2 : cl ^ 2 - cr ^ 2 ≠ 0 := sub_ne_zero.mpr h
    have h3 : cl / cr - (cl / cr)⁻¹ ≠ 0 := by
      intro e
      apply h2
      field_simp at e
      linarith
    field_simp
    ring

lemma E3' (hl : 0 < cl) (hr : 0 < cr) :
    cl * cr * Lker (cl ^ 2) (cr ^ 2) = f (log (cl / cr)) := by
  have h := E3 hl hr
  have hc : 0 < cl * cr := mul_pos hl hr
  have : cl * cr * (cl * cr * Lker (cl ^ 2) (cr ^ 2)) = cl * cr * f (log (cl / cr)) := by
    rw [← h]; ring
  exact mul_left_cancel₀ hc.ne' this

lemma E4 (hl : 0 < cl) (hr : 0 < cr) :
    √(cl ^ 2 * cr ^ 2) * (cl ^ 2 + cr ^ 2) * Lker (cl ^ 2) (cr ^ 2)
      = 2 * cl * cr * b (log (cl / cr)) := by
  have hs : √(cl ^ 2 * cr ^ 2) = cl * cr := by
    rw [show cl ^ 2 * cr ^ 2 = (cl * cr) * (cl * cr) by ring]
    exact sqrt_mul_self (mul_pos hl hr).le
  rw [hs]
  unfold b
  rw [← E3' hl hr, cosh_eq, exp_neg, exp_log (div_pos hl hr)]
  field_simp

end scalar

variable {ι : Type*} [Fintype ι]

/-- `k = Re⟨a b⟩ = ∑ c_l c_r Re(A_lr B_lr)`. -/
def kk (c : ι → ℝ) (A B : ι → ι → ℂ) : ℝ := ∑ l, ∑ r, c l * c r * (A l r * B l r).re

/-- `𝖠 = ∑ p_l p_r L_lr |A_lr|²` (and `𝖡` with `B`). -/
def sfA (c : ι → ℝ) (A : ι → ι → ℂ) : ℝ :=
  ∑ l, ∑ r, c l ^ 2 * c r ^ 2 * Lker (c l ^ 2) (c r ^ 2) * Complex.normSq (A l r)

/-- `𝖢 = ∑ √(p_l p_r) (p_l + p_r) L_lr Re(A_lr B_lr)`. -/
def sfC (c : ι → ℝ) (A B : ι → ι → ℂ) : ℝ :=
  ∑ l, ∑ r, √(c l ^ 2 * c r ^ 2) * (c l ^ 2 + c r ^ 2) * Lker (c l ^ 2) (c r ^ 2) * (A l r * B l r).re

/-- Eq. (S:Q12), first line: `Q(O₁ψ)`. -/
def Q1 (α β κ q nA nB k sA sB sC : ℝ) : ℝ :=
  (q * κ - α) * nA + (q ^ 2 * β - q * κ) * (nB + 1) + (κ * (1 - q ^ 2) + q * (α - β)) * k
    - sA - q ^ 2 * sB + q * sC

/-- Eq. (S:Q12), second line: `Q(O₂ψ)`. -/
def Q2 (α β κ q nA nB k sA sB sC : ℝ) : ℝ :=
  (q ^ 2 * α - q * κ) * (nA + 1) + (q * κ - β) * nB + (κ * (1 - q ^ 2) - q * (α - β)) * k
    - q ^ 2 * sA - sB + q * sC

/-- **Eq. (S:mainid)** (exact bookkeeping identity), for an arbitrary real `q`. -/
theorem mainid (c : ι → ℝ) (hc : ∀ l, 0 < c l) (A B : ι → ι → ℂ) (α β κ q nA nB : ℝ)
    (hA0 : nA = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A l r))
    (hA1 : nA + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A l r))
    (hB0 : nB = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B l r))
    (hB1 : nB + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B l r)) :
    Q1 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
    = -∑ l, ∑ r, c l * c r *
        (Mdiag κ α q (log (c l / c r)) * Complex.normSq (A l r)
          + Mdiag κ β q (log (c l / c r)) * Complex.normSq (B l r)
          + 2 * Moff κ q (log (c l / c r)) * (A l r * B l r).re) := by
  have step : Q1 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      = (q * κ - α) * nA + (q ^ 2 * α - q * κ) * (nA + 1)
        + (q ^ 2 * β - q * κ) * (nB + 1) + (q * κ - β) * nB
        + 2 * κ * (1 - q ^ 2) * kk c A B - (1 + q ^ 2) * sfA c A - (1 + q ^ 2) * sfA c B
        + 2 * q * sfC c A B := by
    unfold Q1 Q2; ring
  rw [step, hA1, hB1, hA0, hB0]
  unfold kk sfA sfC
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_))
  have e1 := E1 (hc l) (hc r)
  have e2 := E2 (hc l) (hc r)
  have e3 := E3 (hc l) (hc r)
  have e4 := E4 (hc l) (hc r)
  unfold Mdiag Moff
  linear_combination
    ((α - q * κ) * Complex.normSq (A l r) + (β - q * κ) * Complex.normSq (B l r)) * e2
    + (q * (κ - q * α) * Complex.normSq (A l r) + q * (κ - q * β) * Complex.normSq (B l r)) * e1
    - (1 + q ^ 2) * (Complex.normSq (A l r) + Complex.normSq (B l r)) * e3
    + 2 * q * (A l r * B l r).re * e4

/-- **Consequence**: with `q = e^{−w}` and the hypotheses of Lemma S5,
`Q(O₁ψ) + Q(O₂ψ) ≤ 0`. -/
theorem sumQ_nonpos {κ α β w : ℝ} (h : Hyp κ α β w) (c : ι → ℝ) (hc : ∀ l, 0 < c l)
    (A B : ι → ι → ℂ) (nA nB : ℝ)
    (hA0 : nA = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A l r))
    (hA1 : nA + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A l r))
    (hB0 : nB = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B l r))
    (hB1 : nB + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B l r)) :
    Q1 α β κ (exp (-w)) nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ (exp (-w)) nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B) ≤ 0 := by
  rw [mainid c hc A B α β κ (exp (-w)) nA nB hA0 hA1 hB0 hB1, neg_nonpos]
  refine Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun r _ => ?_))
  exact mul_nonneg (mul_pos (hc l) (hc r)).le (lemmaS5_complex h _ (A l r) (B l r))

/-! ## The identity for arbitrary `c_l ≥ 0` (kernel directions included)

For a state of finite Schmidt rank, the sum rules (S:wccr) also involve pairs `(l, r)` with
one vanishing Schmidt coefficient (support-to-kernel entries of `a`, `b`). Indexing the support
together with a finite set of kernel directions (`c_l = 0`) covers this case. Here the
coefficients are written through `p_l = c_l²`, `Φ_lr = p_l p_r L_lr` and
`Ψ_lr = √(p_l p_r)(p_l + p_r) L_lr`, which equal `0` when `p_l p_r = 0`
(the "continuous limits" of the text). -/

/-- Diagonal weight `c_l c_r M₁₁(x_lr)` written in the `p`-variables. -/
def wdiag (κ a q pl pr Φ : ℝ) : ℝ := q * (κ - q * a) * pl + (a - q * κ) * pr + (1 + q ^ 2) * Φ

/-- Off-diagonal weight `c_l c_r M₁₂(x_lr)` written in the `p`-variables. -/
def woff (κ q cc Ψ : ℝ) : ℝ := -κ * (1 - q ^ 2) * cc - q * Ψ

/-- The summand of Eq. (S:mainid), for Schmidt coefficients `cl, cr ≥ 0`. -/
def term (κ α β q cl cr : ℝ) (A B : ℂ) : ℝ :=
  wdiag κ α q (cl ^ 2) (cr ^ 2) (cl ^ 2 * cr ^ 2 * Lker (cl ^ 2) (cr ^ 2)) * Complex.normSq A
  + wdiag κ β q (cl ^ 2) (cr ^ 2) (cl ^ 2 * cr ^ 2 * Lker (cl ^ 2) (cr ^ 2)) * Complex.normSq B
  + 2 * woff κ q (cl * cr) (√(cl ^ 2 * cr ^ 2) * (cl ^ 2 + cr ^ 2) * Lker (cl ^ 2) (cr ^ 2))
      * (A * B).re

/-- **Eq. (S:mainid), general form**: valid for all real `c_l` (no positivity needed). -/
theorem mainid_general (c : ι → ℝ) (A B : ι → ι → ℂ) (α β κ q nA nB : ℝ)
    (hA0 : nA = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A l r))
    (hA1 : nA + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A l r))
    (hB0 : nB = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B l r))
    (hB1 : nB + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B l r)) :
    Q1 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
    = -∑ l, ∑ r, term κ α β q (c l) (c r) (A l r) (B l r) := by
  have step : Q1 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      = (q * κ - α) * nA + (q ^ 2 * α - q * κ) * (nA + 1)
        + (q ^ 2 * β - q * κ) * (nB + 1) + (q * κ - β) * nB
        + 2 * κ * (1 - q ^ 2) * kk c A B - (1 + q ^ 2) * sfA c A - (1 + q ^ 2) * sfA c B
        + 2 * q * sfC c A B := by
    unfold Q1 Q2; ring
  rw [step, hA1, hB1, hA0, hB0]
  unfold kk sfA sfC
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun r _ => ?_))
  unfold term wdiag woff
  ring

/-- Each summand is nonnegative under the hypotheses of Lemma S5, for all `cl, cr ≥ 0`:
for `cl, cr > 0` it is `c_l c_r z† M(x_lr) z` (Lemma S5); if one coefficient vanishes it
reduces to the boundary weights, nonnegative because `qκ < α, β < κ/q`. -/
theorem term_nonneg {κ α β w : ℝ} (h : Hyp κ α β w) {cl cr : ℝ} (hl : 0 ≤ cl) (hr : 0 ≤ cr)
    (A B : ℂ) : 0 ≤ term κ α β (exp (-w)) cl cr A B := by
  have ⟨ha1, ha2⟩ := alpha_bounds h
  have ⟨hb1, hb2⟩ := alpha_bounds h.swap
  have he : 0 < exp (-w) := exp_pos _
  have nA := Complex.normSq_nonneg A
  have nB := Complex.normSq_nonneg B
  rcases hl.eq_or_lt with hl0 | hlp
  · subst hl0
    unfold term wdiag woff
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      Real.sqrt_zero, zero_add, add_zero, sub_zero]
    have : 0 ≤ (α - exp (-w) * κ) * cr ^ 2 * Complex.normSq A :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) nA
    have : 0 ≤ (β - exp (-w) * κ) * cr ^ 2 * Complex.normSq B :=
      mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) nB
    nlinarith
  rcases hr.eq_or_lt with hr0 | hrp
  · subst hr0
    unfold term wdiag woff
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      Real.sqrt_zero, add_zero, sub_zero]
    have : 0 ≤ exp (-w) * (κ - exp (-w) * α) * cl ^ 2 * Complex.normSq A :=
      mul_nonneg (mul_nonneg (mul_nonneg he.le (by linarith)) (sq_nonneg _)) nA
    have : 0 ≤ exp (-w) * (κ - exp (-w) * β) * cl ^ 2 * Complex.normSq B :=
      mul_nonneg (mul_nonneg (mul_nonneg he.le (by linarith)) (sq_nonneg _)) nB
    nlinarith
  · have e1 := E1 hlp hrp
    have e2 := E2 hlp hrp
    have e3 := E3 hlp hrp
    have e4 := E4 hlp hrp
    have key : term κ α β (exp (-w)) cl cr A B = cl * cr *
        (Mdiag κ α (exp (-w)) (log (cl / cr)) * Complex.normSq A
          + Mdiag κ β (exp (-w)) (log (cl / cr)) * Complex.normSq B
          + 2 * Moff κ (exp (-w)) (log (cl / cr)) * (A * B).re) := by
      unfold term wdiag woff Mdiag Moff
      linear_combination
        (-exp (-w) * (κ - exp (-w) * α) * Complex.normSq A
          - exp (-w) * (κ - exp (-w) * β) * Complex.normSq B) * e1
        + (-(α - exp (-w) * κ) * Complex.normSq A - (β - exp (-w) * κ) * Complex.normSq B) * e2
        + (1 + exp (-w) ^ 2) * (Complex.normSq A + Complex.normSq B) * e3
        - 2 * exp (-w) * (A * B).re * e4
    rw [key]
    exact mul_nonneg (mul_pos hlp hrp).le (lemmaS5_complex h _ A B)

/-- **Consequence, general form**: under the hypotheses of Lemma S5, `Q(O₁ψ) + Q(O₂ψ) ≤ 0`
for all Schmidt coefficients `c_l ≥ 0` (finite index set). -/
theorem sumQ_nonpos_general {κ α β w : ℝ} (h : Hyp κ α β w) (c : ι → ℝ) (hc : ∀ l, 0 ≤ c l)
    (A B : ι → ι → ℂ) (nA nB : ℝ)
    (hA0 : nA = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A l r))
    (hA1 : nA + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A l r))
    (hB0 : nB = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B l r))
    (hB1 : nB + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B l r)) :
    Q1 α β κ (exp (-w)) nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ (exp (-w)) nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B) ≤ 0 := by
  rw [mainid_general c A B α β κ (exp (-w)) nA nB hA0 hA1 hB0 hB1, neg_nonpos]
  exact Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun r _ =>
    term_nonneg h (hc l) (hc r) (A l r) (B l r)))

end Thm2Cert
