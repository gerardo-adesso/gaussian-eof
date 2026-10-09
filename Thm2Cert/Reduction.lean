/-
Certificate for the scalar steps connecting the minimum principle (Theorem S4 in the SM)
to Theorem 2 of the Letter:
  * the calibration κ cosh w − w = (α+β)/2 with (α,β,κ) = λ(t²,1,t), q = e^{−w},
    is equivalent to λ = λ_{q,t} = −2q ln q / [(t−q)(1−tq)], and λ_{q,t} > 0;
  * 𝓔(q) = g(q²/(1−q²)) = −ln(1−q²) − 2 n_q ln q;
  * the equality value on the two-mode squeezed vacuum:
      𝓔(q) + (α+β) n_q − 2κ q/(1−q²) = −ln(1−q²) − κ q   (under the calibration);
  * 𝓔(q) + λ_{q,t} d_t(q) = −ln(1−q²) − λ_{q,t} t q + λ_{q,t};
  * the m-pair inequality of Theorem 2 follows from the minimum principle.
The TMSV moments ⟨N_A⟩ = ⟨N_B⟩ = q²/(1−q²), ⟨ab⟩ = q/(1−q²), and the operator identity
λ D̂_t = T + λ, are inputs (standard), not derived here.
-/
import Thm2Cert.MatrixLemma
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Real Finset

set_option autoImplicit false

noncomputable section

namespace Thm2Cert

/-- `λ_{q,t} = −2 q ln q / [(t − q)(1 − t q)]`. -/
def lam (q t : ℝ) : ℝ := -2 * q * log q / ((t - q) * (1 - t * q))

/-- `d_t(q) = (1 − t q)² / (1 − q²)`. -/
def dt (t q : ℝ) : ℝ := (1 - t * q) ^ 2 / (1 - q ^ 2)

/-- `g(y) = (y+1) ln(y+1) − y ln y`. -/
def gfun (y : ℝ) : ℝ := (y + 1) * log (y + 1) - y * log y

/-- `𝓔(q) = g(q²/(1−q²))`, the entanglement of the TMSV. -/
def EE (q : ℝ) : ℝ := gfun (q ^ 2 / (1 - q ^ 2))

lemma calib_factor (w t : ℝ) :
    t * cosh w - (1 + t ^ 2) / 2 = (t - exp (-w)) * (1 - t * exp (-w)) / (2 * exp (-w)) := by
  rw [cosh_eq, exp_neg]
  field_simp
  ring

lemma lam_pos {q t : ℝ} (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) : 0 < lam q t := by
  unfold lam
  have hq1 : q < 1 := lt_of_lt_of_le hqt ht
  have hl : log q < 0 := log_neg hq hq1
  have h1 : 0 < t - q := by linarith
  have h2 : 0 < 1 - t * q := by nlinarith
  apply div_pos _ (mul_pos h1 h2)
  nlinarith

/-- The calibration for `(α, β, κ) = λ(t², 1, t)` holds iff `λ = λ_{q,t}`, `q = e^{−w}`. -/
theorem calib_iff {w t l : ℝ} (hw : 0 < w) (hqt : exp (-w) < t) (ht : t ≤ 1) :
    (l * t) * cosh w - w = (l * t ^ 2 + l * 1) / 2 ↔ l = lam (exp (-w)) t := by
  have hq : 0 < exp (-w) := exp_pos _
  have hq1 : exp (-w) < 1 := exp_lt_one_iff.mpr (by linarith)
  have h1 : 0 < t - exp (-w) := by linarith
  have h2 : 0 < 1 - t * exp (-w) := by nlinarith
  set D := (t - exp (-w)) * (1 - t * exp (-w)) / (2 * exp (-w)) with hDdef
  have hD : 0 < D := div_pos (mul_pos h1 h2) (by positivity)
  have key : (l * t) * cosh w - w - (l * t ^ 2 + l * 1) / 2 = l * D - w := by
    rw [hDdef, ← calib_factor w t]; ring
  have hlam : lam (exp (-w)) t = w / D := by
    unfold lam; rw [log_exp, hDdef]; field_simp
  rw [hlam, eq_div_iff hD.ne']
  constructor <;> intro h <;> linarith

lemma EE_formula {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    EE q = -log (1 - q ^ 2) - 2 * (q ^ 2 / (1 - q ^ 2)) * log q := by
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  unfold EE gfun
  have e1 : q ^ 2 / (1 - q ^ 2) + 1 = (1 - q ^ 2)⁻¹ := by field_simp; ring
  rw [e1, log_inv, log_div (pow_pos hq 2).ne' hd.ne', log_pow]
  push_cast
  field_simp
  ring

/-- Equality in the minimum principle on the two-mode squeezed vacuum (scalar part). -/
theorem tmsv_value {κ α β w : ℝ} (hcal : κ * cosh w - w = (α + β) / 2) (hw : 0 < w) :
    EE (exp (-w)) + (α + β) * (exp (-w) ^ 2 / (1 - exp (-w) ^ 2))
      - κ * (2 * exp (-w) / (1 - exp (-w) ^ 2))
      = -log (1 - exp (-w) ^ 2) - κ * exp (-w) := by
  have hq : 0 < exp (-w) := exp_pos _
  have hq1 : exp (-w) < 1 := exp_lt_one_iff.mpr (by linarith)
  have hd : 0 < 1 - exp (-w) ^ 2 := by nlinarith
  have hab : α + β = κ * (exp w + exp (-w)) - 2 * w := by rw [cosh_eq] at hcal; linarith
  have hinv : exp w = (exp (-w))⁻¹ := by rw [exp_neg, inv_inv]
  rw [EE_formula hq hq1, log_exp, hab, hinv]
  generalize exp (-w) = q at hq hq1 hd ⊢
  field_simp
  ring

/-- `𝓔(q) + λ_{q,t} d_t(q) = −ln(1−q²) − λ_{q,t} t q + λ_{q,t}`. -/
theorem energy_identity {q t : ℝ} (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) :
    EE q + lam q t * dt t q = -log (1 - q ^ 2) - lam q t * t * q + lam q t := by
  have hq1 : q < 1 := lt_of_lt_of_le hqt ht
  have hd : 0 < 1 - q ^ 2 := by nlinarith
  have h1 : 0 < t - q := by linarith
  have h2 : 0 < 1 - t * q := by nlinarith
  have h2' : 1 - q * t ≠ 0 := by rw [mul_comm]; exact h2.ne'
  rw [EE_formula hq hq1]
  unfold lam dt
  field_simp
  ring

/-- **Theorem 2 from the minimum principle.** For `m` pairs with `0 < q_j < t_j ≤ 1`,
`λ_j = λ_{q_j,t_j}`, `κ_j = λ_j t_j`, and `⟨T_j⟩ = λ_j(⟨D̂^{(j)}⟩ − 1)`, the minimum principle
`S + ∑ ⟨T_j⟩ ≥ ∑ [−ln(1−q_j²) − κ_j q_j]` implies
`S + ∑ λ_j [⟨D̂^{(j)}⟩ − d_{t_j}(q_j)] ≥ ∑ 𝓔(q_j)`. -/
theorem thm2_of_minprinciple {m : ℕ} (q t D : Fin m → ℝ) (Sent : ℝ)
    (hq : ∀ j, 0 < q j) (hqt : ∀ j, q j < t j) (ht : ∀ j, t j ≤ 1)
    (hmin : Sent + ∑ j, lam (q j) (t j) * (D j - 1)
      ≥ ∑ j, (-log (1 - q j ^ 2) - (lam (q j) (t j) * t j) * q j)) :
    Sent + ∑ j, lam (q j) (t j) * (D j - dt (t j) (q j)) ≥ ∑ j, EE (q j) := by
  have hE : ∑ j, EE (q j) = ∑ j, ((-log (1 - q j ^ 2) - (lam (q j) (t j) * t j) * q j)
      + lam (q j) (t j) - lam (q j) (t j) * dt (t j) (q j)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have := energy_identity (hq j) (hqt j) (ht j)
    linarith
  have hD : ∑ j, lam (q j) (t j) * (D j - dt (t j) (q j))
      = ∑ j, (lam (q j) (t j) * (D j - 1) + lam (q j) (t j)
        - lam (q j) (t j) * dt (t j) (q j)) := by
    refine Finset.sum_congr rfl (fun j _ => ?_); ring
  rw [hE, hD]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hmin ⊢
  linarith

/-- The parameters of Theorem 2 satisfy the hypotheses of Lemma S5: for `0 < q < t ≤ 1`,
`w = −ln q`, `λ = λ_{q,t}`, the triple `(α, β, κ) = λ(t², 1, t)` (and the swapped one
`λ(1, t², t)`) satisfies `Hyp`, with `κ² = αβ`. -/
theorem hyp_of_lam {q t : ℝ} (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) :
    Hyp (lam q t * t) (lam q t * t ^ 2) (lam q t * 1) (-log q) ∧
    Hyp (lam q t * t) (lam q t * 1) (lam q t * t ^ 2) (-log q) := by
  have hq1 : q < 1 := lt_of_lt_of_le hqt ht
  have hl := lam_pos hq hqt ht
  have ht0 : 0 < t := hq.trans hqt
  have hw : 0 < -log q := neg_pos.mpr (log_neg hq hq1)
  have hexp : exp (-(-log q)) = q := by rw [neg_neg, exp_log hq]
  have hcal := (calib_iff (w := -log q) (t := t) (l := lam q t) hw (by rw [hexp]; exact hqt) ht).mpr
    (by rw [hexp])
  refine ⟨⟨by positivity, by positivity, by positivity, hw, by nlinarith, by linarith⟩,
    ⟨by positivity, by positivity, by positivity, hw, by nlinarith, by linarith⟩⟩

end Thm2Cert
