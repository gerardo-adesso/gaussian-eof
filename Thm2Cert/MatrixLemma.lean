/-
Copyright (c) 2026. Machine-checked certificate for
G. Adesso, "Optimality of Gaussian entanglement of formation", Supplemental Material,
Lemma S5 (the matrix inequality behind Theorem 2).

Statement certified here (all real numbers):
  Let κ, α, β, w > 0 with κ² ≤ αβ and the calibration κ cosh w − w = (α+β)/2,
  and q = e^{−w}.  With f(x) = x / sinh x (f(0) = 1) and b(x) = x coth x = f(x) cosh x, put
    M₁₁(x) = q(κ − qα)eˣ + (α − qκ)e⁻ˣ + (1+q²) f(x)
    M₂₂(x) = q(κ − qβ)eˣ + (β − qκ)e⁻ˣ + (1+q²) f(x)
    M₁₂(x) = −κ(1 − q²) − 2q b(x).
  Then M(x) is positive semidefinite for every real x, positive definite for x ≠ w,
  and the kernel of M(w) is spanned by (1,1).
The comparison M ≥ γK of Lemma S5 (with explicit γ) is certified in `Comparison.lean`.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.Norm

open Real

set_option autoImplicit false

noncomputable section

namespace Thm2Cert

/-! ## The auxiliary functions `f x = x / sinh x` and `b x = x coth x` -/

/-- `f x = x / sinh x`, extended continuously by `f 0 = 1`. -/
def f (x : ℝ) : ℝ := if x = 0 then 1 else x / sinh x

/-- `b x = x coth x`, written as `f x * cosh x` (so that `b 0 = 1`). -/
def b (x : ℝ) : ℝ := f x * cosh x

@[simp] lemma f_zero : f 0 = 1 := by simp [f]

lemma f_mul_sinh (x : ℝ) : f x * sinh x = x := by
  unfold f
  split_ifs with h
  · simp [h]
  · have : sinh x ≠ 0 := sinh_ne_zero.mpr h
    field_simp

lemma f_pos (x : ℝ) : 0 < f x := by
  unfold f
  split_ifs with h
  · exact one_pos
  · rcases lt_or_gt_of_ne h with hx | hx
    · exact div_pos_of_neg_of_neg hx (sinh_neg_iff.mpr hx)
    · exact div_pos hx (sinh_pos_iff.mpr hx)

lemma f_neg (x : ℝ) : f (-x) = f x := by
  unfold f
  by_cases h : x = 0
  · simp [h]
  · have h' : -x ≠ 0 := neg_ne_zero.mpr h
    simp only [h, h', ite_false, sinh_neg, neg_div_neg_eq]

lemma b_eq {x : ℝ} (hx : x ≠ 0) : b x = x * cosh x / sinh x := by
  unfold b f; simp only [hx, ite_false]; ring

/-! ## Two monotonicity facts -/

lemma sinh_strictConvexOn : StrictConvexOn ℝ (Set.Ici (0:ℝ)) sinh := by
  apply StrictMonoOn.strictConvexOn_of_deriv (convex_Ici 0) continuous_sinh.continuousOn
  rw [interior_Ici, Real.deriv_sinh]
  exact cosh_strictMonoOn.mono Set.Ioi_subset_Ici_self

/-- (L1) `sinh t / t` is strictly increasing on `(0, ∞)`, in cross-multiplied form. -/
lemma L1 {a c : ℝ} (ha : 0 < a) (hac : a < c) : c * sinh a < a * sinh c := by
  have hc : 0 < c := ha.trans hac
  have h1 : (0:ℝ) < 1 - a / c := by rw [sub_pos, div_lt_one hc]; exact hac
  have h2 : (0:ℝ) < a / c := div_pos ha hc
  have h := sinh_strictConvexOn.2 (Set.self_mem_Ici) (Set.mem_Ici.mpr hc.le) hc.ne h1 h2
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, sinh_zero] at h
  rw [div_mul_cancel₀ a hc.ne'] at h
  calc c * sinh a < c * (a / c * sinh c) := mul_lt_mul_of_pos_left h hc
    _ = a * sinh c := by field_simp

/-- (L2) the identity behind the monotonicity of `sinh a / sinh (a + c)`. -/
lemma L2 (a a' c : ℝ) :
    sinh a' * sinh (a + c) - sinh a * sinh (a' + c) = sinh (a' - a) * sinh c := by
  simp only [sinh_add, sinh_sub]; ring

/-! ## Sign of `g(x) = w sinh x − sinh² w · f x` -/

lemma g_pos {w x : ℝ} (hw : 0 < w) (hx : w < x) : 0 < w * sinh x - sinh w ^ 2 * f x := by
  have hx0 : 0 < x := hw.trans hx
  have hs : 0 < sinh w := sinh_pos_iff.mpr hw
  have hsx : sinh w < sinh x := sinh_lt_sinh.mpr hx
  have hsxp : 0 < sinh x := hs.trans hsx
  have hL := L1 hw hx
  have key : (w * sinh x - sinh w ^ 2 * f x) * sinh x
      = w * sinh x * sinh x - x * sinh w * sinh w := by
    linear_combination (-(sinh w) ^ 2) * f_mul_sinh x
  have h1 := mul_lt_mul_of_pos_right hL hsxp
  have h2 := mul_lt_mul_of_pos_left hsx (mul_pos hx0 hs)
  have h3 : 0 < (w * sinh x - sinh w ^ 2 * f x) * sinh x := by rw [key]; linarith
  nlinarith

lemma g_neg {w x : ℝ} (hw : 0 < w) (hx : x < w) : w * sinh x - sinh w ^ 2 * f x < 0 := by
  have hs : 0 < sinh w := sinh_pos_iff.mpr hw
  have hfs : 0 < sinh w ^ 2 * f x := mul_pos (pow_pos hs 2) (f_pos x)
  rcases le_or_gt x 0 with hx0 | hx0
  · have : sinh x ≤ 0 := sinh_nonpos_iff.mpr hx0
    nlinarith
  · have hsx : sinh x < sinh w := sinh_lt_sinh.mpr hx
    have hsxp : 0 < sinh x := sinh_pos_iff.mpr hx0
    have hL := L1 hx0 hx
    have key : (w * sinh x - sinh w ^ 2 * f x) * sinh x
        = w * sinh x * sinh x - x * sinh w * sinh w := by
      linear_combination (-(sinh w) ^ 2) * f_mul_sinh x
    have h1 := mul_lt_mul_of_pos_right hL hsxp
    have h2 := mul_lt_mul_of_pos_left hsx (mul_pos hx0 hs)
    have h3 : (w * sinh x - sinh w ^ 2 * f x) * sinh x < 0 := by rw [key]; linarith
    nlinarith

/-! ## Sign of `J(x) = w sinh(x/2) − sinh(w/2) f(x) sinh((x+w)/2)` (that is, `w · I(x)`) -/

/-- `J w x = w * I(x)` with `I` as in the proof of Lemma S5. -/
def J (w x : ℝ) : ℝ := w * sinh (x / 2) - sinh (w / 2) * f x * sinh ((x + w) / 2)

lemma J_key (w x : ℝ) : J w x * sinh x * sinh w
    = (w * sinh x) * (sinh (x / 2) * sinh w)
      - (x * sinh w) * (sinh (w / 2) * sinh ((x + w) / 2)) := by
  unfold J
  linear_combination (-(sinh (w / 2)) * sinh ((x + w) / 2) * sinh w) * f_mul_sinh x

lemma J_pos {w x : ℝ} (hw : 0 < w) (hx : w < x) : 0 < J w x := by
  have hx0 : 0 < x := hw.trans hx
  have hS : 0 < sinh w := sinh_pos_iff.mpr hw
  have hs : 0 < sinh (w / 2) := sinh_pos_iff.mpr (by linarith)
  have hsx : 0 < sinh x := sinh_pos_iff.mpr hx0
  have hL := L1 hw hx
  have h2 := L2 (w / 2) (x / 2) (w / 2)
  rw [show w / 2 + w / 2 = w by ring, show x / 2 + w / 2 = (x + w) / 2 by ring] at h2
  have h2' : sinh (w / 2) * sinh ((x + w) / 2) < sinh (x / 2) * sinh w := by
    have : 0 < sinh (x / 2 - w / 2) * sinh (w / 2) :=
      mul_pos (sinh_pos_iff.mpr (by linarith)) hs
    linarith
  have hpos : 0 < sinh (w / 2) * sinh ((x + w) / 2) :=
    mul_pos hs (sinh_pos_iff.mpr (by linarith))
  have hprod := mul_lt_mul'' hL h2' (mul_pos hx0 hS).le hpos.le
  have : 0 < J w x * sinh x * sinh w := by rw [J_key]; linarith
  have hm : 0 < sinh x * sinh w := mul_pos hsx hS
  nlinarith

lemma J_neg {w x : ℝ} (hw : 0 < w) (hx : x < w) : J w x < 0 := by
  have hS : 0 < sinh w := sinh_pos_iff.mpr hw
  have hs : 0 < sinh (w / 2) := sinh_pos_iff.mpr (by linarith)
  rcases lt_trichotomy x 0 with hx0 | hx0 | hx0
  · rcases le_or_gt (-w) x with hxw | hxw
    · -- −w ≤ x < 0
      have h1 : sinh (x / 2) < 0 := sinh_neg_iff.mpr (by linarith)
      have h2 : 0 ≤ sinh ((x + w) / 2) := sinh_nonneg_iff.mpr (by linarith)
      have h3 : 0 < sinh (w / 2) * f x := mul_pos hs (f_pos x)
      unfold J
      nlinarith
    · -- x < −w : write x = −z with z > w
      obtain ⟨z, rfl⟩ : ∃ z, x = -z := ⟨-x, by ring⟩
      have hzw : w < z := by linarith
      have hz0 : 0 < z := hw.trans hzw
      have hsz : 0 < sinh z := sinh_pos_iff.mpr hz0
      have hL := L1 hw hzw
      have e : f z * sinh w * sinh z = z * sinh w := by
        linear_combination sinh w * f_mul_sinh z
      have hfz : f z * sinh w < w := by nlinarith
      have hsS : sinh (w / 2) < sinh w := sinh_lt_sinh.mpr (by linarith)
      have hsf : sinh (w / 2) * f z < w := by
        have := mul_lt_mul_of_pos_right hsS (f_pos z)
        nlinarith
      have hA : sinh ((-z + w) / 2) = -sinh ((z - w) / 2) := by
        rw [← sinh_neg]; congr 1; ring
      have hB : sinh (-z / 2) = -sinh (z / 2) := by
        rw [← sinh_neg]; congr 1; ring
      have hC0 : 0 < sinh ((z - w) / 2) := sinh_pos_iff.mpr (by linarith)
      have hC1 : sinh ((z - w) / 2) < sinh (z / 2) := sinh_lt_sinh.mpr (by linarith)
      have i1 := mul_lt_mul_of_pos_right hsf hC0
      have i2 := mul_lt_mul_of_pos_left hC1 hw
      unfold J
      rw [hA, hB, f_neg]
      nlinarith
  · subst hx0
    unfold J
    rw [f_zero]
    simp only [zero_div, sinh_zero, mul_zero, zero_add, mul_one]
    nlinarith
  · have hsx : 0 < sinh x := sinh_pos_iff.mpr hx0
    have hL := L1 hx0 hx
    have h2 := L2 (x / 2) (w / 2) (w / 2)
    rw [show w / 2 + w / 2 = w by ring, show x / 2 + w / 2 = (x + w) / 2 by ring] at h2
    have h2' : sinh (x / 2) * sinh w < sinh (w / 2) * sinh ((x + w) / 2) := by
      have : 0 < sinh (w / 2 - x / 2) * sinh (w / 2) :=
        mul_pos (sinh_pos_iff.mpr (by linarith)) hs
      linarith
    have hpos : 0 < sinh (x / 2) * sinh w := mul_pos (sinh_pos_iff.mpr (by linarith)) hS
    have hprod := mul_lt_mul'' hL h2' (mul_pos hw hsx).le hpos.le
    have : J w x * sinh x * sinh w < 0 := by rw [J_key]; linarith
    have hm : 0 < sinh x * sinh w := mul_pos hsx hS
    nlinarith

/-! ## Pure algebraic identities (certified by `linear_combination`) -/

/-- Eq. (S:detid): decomposition of the determinant of `M/(2q)`. Here
`P = κ cosh w − α`, `Q = κ cosh w − β` (so `P + Q = 2w` is the calibration). -/
lemma det_identity (κ κ0 w P Q S C sy cy sx cx F : ℝ)
    (hQ : Q = 2 * w - P) (hC : C ^ 2 - S ^ 2 = 1) (hy : cy ^ 2 - sy ^ 2 = 1)
    (hsx : sx = sy * C + cy * S) (hcx : cx = cy * C + sy * S) (h3 : κ0 * (C - 1) = w) :
    (κ * S * cy + P * sy + C * F) * (κ * S * cy + Q * sy + C * F) - (κ * S + F * cx) ^ 2
      = ((κ0 * S * cy + w * sy + C * F) ^ 2 - (κ0 * S + F * cx) ^ 2)
        + 2 * (κ - κ0) * sy * (w * sx - S ^ 2 * F)
        + ((κ * C - P) * (κ * C - Q) - κ ^ 2) * sy ^ 2 := by
  subst hQ hsx hcx
  linear_combination (sy ^ 2 * (κ0 - κ) * (κ + κ0)) * hC
    + (-S ^ 2 * (κ0 - κ) * (κ + κ0)) * hy + (-sy ^ 2 * (κ0 * (C + 1) - w)) * h3

/-- Half-angle form of the eigenvalue of `M/(2q)` along `(1,1)` at `κ = κ₀`, `δ = 0`. -/
lemma half_minus (κ0 w S C sy cy sxh cxh cx sxw sp cp sr cr F : ℝ)
    (hp : cp ^ 2 - sp ^ 2 = 1) (hr : cr ^ 2 - sr ^ 2 = 1)
    (hw : w = κ0 * (C - 1)) (hC : C = cr ^ 2 + sr ^ 2) (hS : S = 2 * sr * cr)
    (hsy : sy = 2 * sp * cp) (hcy : cy = cp ^ 2 + sp ^ 2)
    (hsxh : sxh = sp * cr + cp * sr) (hcxh : cxh = cp * cr + sp * sr)
    (hcx : cx = cxh ^ 2 + sxh ^ 2) (hsxw : sxw = sp * C + cp * S) :
    sr * ((κ0 * S * cy + w * sy + C * F) - (κ0 * S + F * cx))
      = 2 * sp * (w * sxh - sr * F * sxw) := by
  subst hw; subst hcx; subst hsxw; subst hC hS hsy hcy hsxh hcxh
  linear_combination (-sr * (F * cr ^ 2 + F * sr ^ 2 - 2 * cr * sr * κ0)) * hp
    + (-2 * cr * sp ^ 2 * κ0) * hr

/-- Half-angle form of the eigenvalue of `M/(2q)` along `(1,−1)` at `κ = κ₀`, `δ = 0`. -/
lemma half_plus (κ0 w S C sy cy sxh cxh cx sxw sp cp sr cr F : ℝ)
    (hp : cp ^ 2 - sp ^ 2 = 1) (hr : cr ^ 2 - sr ^ 2 = 1)
    (hw : w = κ0 * (C - 1)) (hC : C = cr ^ 2 + sr ^ 2) (hS : S = 2 * sr * cr)
    (hsy : sy = 2 * sp * cp) (hcy : cy = cp ^ 2 + sp ^ 2)
    (hsxh : sxh = sp * cr + cp * sr) (hcxh : cxh = cp * cr + sp * sr)
    (hcx : cx = cxh ^ 2 + sxh ^ 2) (_hsxw : sxw = sp * C + cp * S) :
    sr * ((κ0 * S * cy + w * sy + C * F) + (κ0 * S + F * cx))
      = 2 * w * cp * cxh + sr * F * (C + cx) := by
  subst hw; subst hcx; subst hC hS hsy hcy hsxh hcxh
  linear_combination (-2 * cr * κ0 * (cr - 1) * (cr + 1)) * hp
    + (-2 * cr * κ0 * (sp ^ 2 + 1)) * hr

/-! ## The matrix `M(x)` and its normalized form `M(x)/(2q)` -/

/-- Diagonal entry of `M(x)` for a general `q` (`a = α` or `a = β`). -/
def Mdiag (κ a q x : ℝ) : ℝ := q * (κ - q * a) * exp x + (a - q * κ) * exp (-x) + (1 + q ^ 2) * f x

/-- Off-diagonal entry of `M(x)` for a general `q`. -/
def Moff (κ q x : ℝ) : ℝ := -κ * (1 - q ^ 2) - 2 * q * b x

/-- Diagonal entry of `M(x)/(2q)`, `q = e^{−w}`: `m = κ S cosh(x−w) + (κC − a) sinh(x−w) + C f`. -/
def mdiag (κ a w x : ℝ) : ℝ :=
  κ * sinh w * cosh (x - w) + (κ * cosh w - a) * sinh (x - w) + cosh w * f x

/-- Minus the off-diagonal entry of `M(x)/(2q)`. -/
def moff (κ w x : ℝ) : ℝ := κ * sinh w + b x

lemma Mdiag_eq (κ a w x : ℝ) : Mdiag κ a (exp (-w)) x = 2 * exp (-w) * mdiag κ a w x := by
  unfold Mdiag mdiag
  simp only [cosh_eq, sinh_eq, Real.exp_neg, Real.exp_sub, neg_sub]
  field_simp
  ring

lemma Moff_eq (κ w x : ℝ) : Moff κ (exp (-w)) x = -(2 * exp (-w) * moff κ w x) := by
  unfold Moff moff
  simp only [sinh_eq, Real.exp_neg]
  field_simp
  ring

/-! ## Hypotheses of Lemma S5 -/

/-- Hypotheses of Lemma S5: `α, β, κ > 0`, `αβ ≥ κ²`, and `w > 0` solves the calibration
`κ cosh w − w = (α+β)/2` (then `q = e^{−w}`). -/
structure Hyp (κ α β w : ℝ) : Prop where
  hκ : 0 < κ
  hα : 0 < α
  hβ : 0 < β
  hw : 0 < w
  hκαβ : κ ^ 2 ≤ α * β
  hcal : κ * cosh w - w = (α + β) / 2

/-- Sanity check: the hypotheses are satisfiable (`w = 1`, `κ = 2/(cosh 1 − 1)`,
`α = β = κ cosh 1 − 1`). -/
theorem hyp_nonvacuous : ∃ κ α β w : ℝ, Hyp κ α β w := by
  have hC1 : 0 < cosh 1 - 1 := by have := one_lt_cosh.mpr (one_ne_zero (α := ℝ)); linarith
  set κ := 2 / (cosh 1 - 1) with hκ
  have hκpos : 0 < κ := div_pos two_pos hC1
  have hk : κ * (cosh 1 - 1) = 2 := div_mul_cancel₀ 2 hC1.ne'
  refine ⟨κ, κ * cosh 1 - 1, κ * cosh 1 - 1, 1, hκpos, by nlinarith, by nlinarith, one_pos,
    by nlinarith, by ring⟩

variable {κ α β w : ℝ}

lemma kappa0_le (h : Hyp κ α β w) : w / (cosh w - 1) ≤ κ := by
  have hC1 : 0 < cosh w - 1 := by have := one_lt_cosh.mpr h.hw.ne'; linarith
  have h1 : (2 * κ) ^ 2 ≤ (α + β) ^ 2 := by nlinarith [sq_nonneg (α - β), h.hκαβ]
  have hab : 2 * κ ≤ α + β := by nlinarith [h.hκ, h.hα, h.hβ]
  rw [div_le_iff₀ hC1]
  linarith [h.hcal]

/-- `κ sinh w > w`. -/
lemma kS_gt (h : Hyp κ α β w) : w < κ * sinh w := by
  have hC1 : 0 < cosh w - 1 := by have := one_lt_cosh.mpr h.hw.ne'; linarith
  have hS : 0 < sinh w := sinh_pos_iff.mpr h.hw
  have hSC : cosh w - 1 < sinh w := by
    have h1 := cosh_sub_sinh w
    have h2 : exp (-w) < 1 := Real.exp_lt_one_iff.mpr (by linarith [h.hw])
    have h3 : 0 < exp (-w) := exp_pos _
    linarith
  have hk := kappa0_le h
  rw [div_le_iff₀ hC1] at hk
  nlinarith [h.hκ]

/-- The trace of `M(x)/(2q)` is positive. -/
lemma trace_pos (h : Hyp κ α β w) (x : ℝ) : 0 < mdiag κ α w x + mdiag κ β w x := by
  have hk := kS_gt h
  have hcy : 0 < cosh (x - w) := cosh_pos _
  have he : 0 < cosh (x - w) + sinh (x - w) := by rw [cosh_add_sinh]; exact exp_pos _
  have hCf : 0 < cosh w * f x := mul_pos (cosh_pos _) (f_pos x)
  have hsum : mdiag κ α w x + mdiag κ β w x
      = 2 * (κ * sinh w - w) * cosh (x - w) + 2 * w * (cosh (x - w) + sinh (x - w))
        + 2 * (cosh w * f x) := by
    unfold mdiag; linear_combination (2 * sinh (x - w)) * h.hcal
  rw [hsum]
  have : 0 < (κ * sinh w - w) * cosh (x - w) := mul_pos (by linarith) hcy
  nlinarith [h.hw]

/-- At `x = w` all four entries of `M(w)/(2q)` agree (up to the sign of the off-diagonal). -/
lemma at_w_alpha (κ a w : ℝ) : mdiag κ a w w = moff κ w w := by
  unfold mdiag moff b
  simp only [sub_self, cosh_zero, sinh_zero]
  ring

set_option maxHeartbeats 1000000 in
/-- Main step: `det(M(x)/(2q)) > 0` for `x ≠ w`. -/
theorem det_pos (h : Hyp κ α β w) {x : ℝ} (hx : x ≠ w) :
    0 < mdiag κ α w x * mdiag κ β w x - moff κ w x ^ 2 := by
  have hC1 : 0 < cosh w - 1 := by have := one_lt_cosh.mpr h.hw.ne'; linarith
  set κ0 := w / (cosh w - 1) with hκ0def
  have h3 : κ0 * (cosh w - 1) = w := div_mul_cancel₀ w hC1.ne'
  have hk : κ0 ≤ κ := kappa0_le h
  have hdet := det_identity κ κ0 w (κ * cosh w - α) (κ * cosh w - β) (sinh w) (cosh w)
    (sinh (x - w)) (cosh (x - w)) (sinh x) (cosh x) (f x)
    (by linarith [h.hcal]) (by rw [cosh_sq]; ring) (by rw [cosh_sq]; ring)
    (by rw [← sinh_add, sub_add_cancel]) (by rw [← cosh_add, sub_add_cancel]) h3
  -- half-angle data
  have hp : cosh ((x - w) / 2) ^ 2 - sinh ((x - w) / 2) ^ 2 = 1 := by rw [cosh_sq]; ring
  have hr : cosh (w / 2) ^ 2 - sinh (w / 2) ^ 2 = 1 := by rw [cosh_sq]; ring
  have hCr : cosh w = cosh (w / 2) ^ 2 + sinh (w / 2) ^ 2 := by
    rw [← cosh_two_mul]; congr 1; ring
  have hSr : sinh w = 2 * sinh (w / 2) * cosh (w / 2) := by
    rw [← sinh_two_mul]; congr 1; ring
  have hsy : sinh (x - w) = 2 * sinh ((x - w) / 2) * cosh ((x - w) / 2) := by
    rw [← sinh_two_mul]; congr 1; ring
  have hcy : cosh (x - w) = cosh ((x - w) / 2) ^ 2 + sinh ((x - w) / 2) ^ 2 := by
    rw [← cosh_two_mul]; congr 1; ring
  have hsxh : sinh (x / 2) = sinh ((x - w) / 2) * cosh (w / 2) + cosh ((x - w) / 2) * sinh (w / 2) := by
    rw [← sinh_add]; congr 1; ring
  have hcxh : cosh (x / 2) = cosh ((x - w) / 2) * cosh (w / 2) + sinh ((x - w) / 2) * sinh (w / 2) := by
    rw [← cosh_add]; congr 1; ring
  have hcx : cosh x = cosh (x / 2) ^ 2 + sinh (x / 2) ^ 2 := by
    rw [← cosh_two_mul]; congr 1; ring
  have hsxw : sinh ((x + w) / 2) = sinh ((x - w) / 2) * cosh w + cosh ((x - w) / 2) * sinh w := by
    rw [← sinh_add]; congr 1; ring
  have hm := half_minus κ0 w (sinh w) (cosh w) (sinh (x - w)) (cosh (x - w)) (sinh (x / 2))
    (cosh (x / 2)) (cosh x) (sinh ((x + w) / 2)) (sinh ((x - w) / 2)) (cosh ((x - w) / 2))
    (sinh (w / 2)) (cosh (w / 2)) (f x) hp hr h3.symm hCr hSr hsy hcy hsxh hcxh hcx hsxw
  have hpl := half_plus κ0 w (sinh w) (cosh w) (sinh (x - w)) (cosh (x - w)) (sinh (x / 2))
    (cosh (x / 2)) (cosh x) (sinh ((x + w) / 2)) (sinh ((x - w) / 2)) (cosh ((x - w) / 2))
    (sinh (w / 2)) (cosh (w / 2)) (f x) hp hr h3.symm hCr hSr hsy hcy hsxh hcxh hcx hsxw
  have hsr : 0 < sinh (w / 2) := sinh_pos_iff.mpr (by linarith [h.hw])
  -- sign facts on either side of x = w
  have hsJ : 0 < sinh ((x - w) / 2) * J w x := by
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact mul_pos_of_neg_of_neg (sinh_neg_iff.mpr (by linarith)) (J_neg h.hw hlt)
    · exact mul_pos (sinh_pos_iff.mpr (by linarith)) (J_pos h.hw hgt)
  have hsg : 0 ≤ sinh (x - w) * (w * sinh x - sinh w ^ 2 * f x) := by
    rcases lt_or_gt_of_ne hx with hlt | hgt
    · exact (mul_pos_of_neg_of_neg (sinh_neg_iff.mpr (by linarith)) (g_neg h.hw hlt)).le
    · exact (mul_pos (sinh_pos_iff.mpr (by linarith)) (g_pos h.hw hgt)).le
  -- the two eigenvalues at κ = κ₀, δ = 0
  have hAm : 0 < (κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
      - (κ0 * sinh w + f x * cosh x) := by
    have e1 : 0 < sinh (w / 2) * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
      - (κ0 * sinh w + f x * cosh x)) := by
      rw [hm]; unfold J at hsJ; linarith
    exact (mul_pos_iff_of_pos_left hsr).mp e1
  have hAp : 0 < (κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
      + (κ0 * sinh w + f x * cosh x) := by
    have q1 : 0 < 2 * w * cosh ((x - w) / 2) * cosh (x / 2) :=
      mul_pos (mul_pos (by linarith [h.hw]) (cosh_pos _)) (cosh_pos _)
    have q2 : 0 < sinh (w / 2) * f x * (cosh w + cosh x) :=
      mul_pos (mul_pos hsr (f_pos x)) (by linarith [cosh_pos w, cosh_pos x])
    have e1 : 0 < sinh (w / 2) * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
      + (κ0 * sinh w + f x * cosh x)) := by rw [hpl]; linarith
    exact (mul_pos_iff_of_pos_left hsr).mp e1
  have hΔ0 : 0 < (κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x) ^ 2
      - (κ0 * sinh w + f x * cosh x) ^ 2 := by
    have e : (κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x) ^ 2
        - (κ0 * sinh w + f x * cosh x) ^ 2
        = ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
          - (κ0 * sinh w + f x * cosh x))
          * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
          + (κ0 * sinh w + f x * cosh x)) := by ring
    rw [e]; exact mul_pos hAm hAp
  have hT2 : 0 ≤ 2 * (κ - κ0) * sinh (x - w) * (w * sinh x - sinh w ^ 2 * f x) := by
    have : 0 ≤ 2 * (κ - κ0) := by linarith
    have := mul_nonneg this hsg
    linarith
  have hT3 : 0 ≤ ((κ * cosh w - (κ * cosh w - α)) * (κ * cosh w - (κ * cosh w - β)) - κ ^ 2)
      * sinh (x - w) ^ 2 := by
    have : (κ * cosh w - (κ * cosh w - α)) * (κ * cosh w - (κ * cosh w - β)) - κ ^ 2
        = α * β - κ ^ 2 := by ring
    rw [this]
    exact mul_nonneg (by linarith [h.hκαβ]) (sq_nonneg _)
  unfold mdiag moff b
  linarith [hdet, hΔ0, hT2, hT3]

/-- `det(M(x)/(2q)) ≥ 0` for every real `x`. -/
theorem det_nonneg (h : Hyp κ α β w) (x : ℝ) :
    0 ≤ mdiag κ α w x * mdiag κ β w x - moff κ w x ^ 2 := by
  by_cases hx : x = w
  · rw [hx, at_w_alpha, at_w_alpha]; nlinarith [sq_nonneg (moff κ w w)]
  · exact (det_pos h hx).le

lemma diag_nonneg (h : Hyp κ α β w) (x : ℝ) :
    0 ≤ mdiag κ α w x ∧ 0 ≤ mdiag κ β w x := by
  have hd := det_nonneg h x
  have ht := trace_pos h x
  constructor <;> nlinarith [sq_nonneg (moff κ w x), sq_nonneg (mdiag κ α w x), sq_nonneg (mdiag κ β w x)]

/-! ## Quadratic forms of 2×2 symmetric matrices -/

lemma quad_nonneg {a c d : ℝ} (ha : 0 ≤ a) (hdet : d ^ 2 ≤ a * c) (hc : 0 ≤ c) (u v : ℝ) :
    0 ≤ a * u ^ 2 - 2 * d * u * v + c * v ^ 2 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0
    have hd : d = 0 := by
      have : d ^ 2 ≤ 0 := by linarith
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm this (sq_nonneg d))
    subst hd
    nlinarith [sq_nonneg v]
  · nlinarith [sq_nonneg (a * u - d * v), mul_nonneg (sub_nonneg.2 hdet) (sq_nonneg v)]

lemma quad_pos {a c d : ℝ} (ha : 0 < a) (hdet : d ^ 2 < a * c) {u v : ℝ}
    (huv : u ≠ 0 ∨ v ≠ 0) : 0 < a * u ^ 2 - 2 * d * u * v + c * v ^ 2 := by
  by_cases hv : v = 0
  · subst hv
    have hu : u ≠ 0 := by tauto
    have : 0 < u ^ 2 := by positivity
    nlinarith
  · have : 0 < v ^ 2 := by positivity
    nlinarith [sq_nonneg (a * u - d * v), mul_pos (sub_pos.2 hdet) this]

/-! ## Lemma S5 (positivity and kernel of `M(x)`) -/

/-- The quadratic form of `M(x)`, `q = e^{−w}`. -/
def QM (κ α β w x u v : ℝ) : ℝ :=
  Mdiag κ α (exp (-w)) x * u ^ 2 + 2 * Moff κ (exp (-w)) x * u * v + Mdiag κ β (exp (-w)) x * v ^ 2

lemma QM_eq (κ α β w x u v : ℝ) : QM κ α β w x u v
    = 2 * exp (-w) * (mdiag κ α w x * u ^ 2 - 2 * moff κ w x * u * v + mdiag κ β w x * v ^ 2) := by
  unfold QM; rw [Mdiag_eq, Mdiag_eq, Moff_eq]; ring

/-- **Lemma S5 (i)**: `M(x) ≥ 0` for every real `x`. -/
theorem lemmaS5_psd (h : Hyp κ α β w) (x u v : ℝ) : 0 ≤ QM κ α β w x u v := by
  rw [QM_eq]
  have ⟨h1, h2⟩ := diag_nonneg h x
  have hd := det_nonneg h x
  exact mul_nonneg (by positivity) (quad_nonneg h1 (by linarith) h2 u v)

/-- **Lemma S5 (ii)**: `M(x)` is positive definite for `x ≠ w`, i.e. `ker M(x) = {0}`. -/
theorem lemmaS5_pd (h : Hyp κ α β w) {x : ℝ} (hx : x ≠ w) {u v : ℝ} (huv : u ≠ 0 ∨ v ≠ 0) :
    0 < QM κ α β w x u v := by
  rw [QM_eq]
  have hd := det_pos h hx
  have ⟨h1, h2⟩ := diag_nonneg h x
  have ha : 0 < mdiag κ α w x := by
    rcases h1.eq_or_lt with h0 | h0
    · rw [← h0] at hd; nlinarith [sq_nonneg (moff κ w x)]
    · exact h0
  exact mul_pos (by positivity) (quad_pos ha (by linarith) huv)

/-- **Lemma S5 (iii)**: at `x = w`, the quadratic form vanishes exactly on `span{(1,1)}`,
i.e. `ker M(w) = span{(1,1)}`. -/
theorem lemmaS5_kernel (h : Hyp κ α β w) (u v : ℝ) : QM κ α β w w u v = 0 ↔ u = v := by
  rw [QM_eq, at_w_alpha, at_w_alpha]
  have ht := trace_pos h w
  rw [at_w_alpha, at_w_alpha] at ht
  have hq : 0 < 2 * exp (-w) := by positivity
  have hc : 0 < moff κ w w := by linarith
  have e : moff κ w w * u ^ 2 - 2 * moff κ w w * u * v + moff κ w w * v ^ 2
      = moff κ w w * (u - v) ^ 2 := by ring
  rw [e]
  constructor
  · intro h0
    have : moff κ w w * (u - v) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h0 with h1 | h1
      · linarith
      · exact h1
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h1
      linarith
  · intro huv; subst huv; ring

/-- `M(w) (1,1)ᵀ = 0`, entrywise. -/
theorem lemmaS5_null :
    Mdiag κ α (exp (-w)) w + Moff κ (exp (-w)) w = 0 ∧
    Moff κ (exp (-w)) w + Mdiag κ β (exp (-w)) w = 0 := by
  rw [Mdiag_eq, Mdiag_eq, Moff_eq, at_w_alpha, at_w_alpha]
  constructor <;> ring

/-- Complex form used in Eq. (S:mainid): for `z = (A, conj B)`,
`z† M(x) z = M₁₁|A|² + M₂₂|B|² + 2 M₁₂ Re(AB) ≥ 0`. -/
theorem lemmaS5_complex (h : Hyp κ α β w) (x : ℝ) (A B : ℂ) :
    0 ≤ Mdiag κ α (exp (-w)) x * Complex.normSq A + Mdiag κ β (exp (-w)) x * Complex.normSq B
      + 2 * Moff κ (exp (-w)) x * (A * B).re := by
  have hpsd := lemmaS5_psd h x ‖A‖ ‖B‖
  unfold QM at hpsd
  have hoff : Moff κ (exp (-w)) x ≤ 0 := by
    rw [Moff_eq]
    have : 0 < moff κ w x := by
      unfold moff b
      have := kS_gt h
      have : 0 < f x * cosh x := mul_pos (f_pos x) (cosh_pos x)
      nlinarith [h.hw]
    have : 0 < exp (-w) := exp_pos _
    nlinarith
  have hre : (A * B).re ≤ ‖A‖ * ‖B‖ := by
    rw [← Complex.norm_mul]; exact Complex.re_le_norm _
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonpos_left hre hoff]

/-- The off-diagonal entry is negative: `M₁₂(x) < 0`. -/
lemma Moff_neg (h : Hyp κ α β w) (x : ℝ) : Moff κ (exp (-w)) x < 0 := by
  rw [Moff_eq]
  have : 0 < moff κ w x := by
    unfold moff b
    have := kS_gt h
    have : 0 < f x * cosh x := mul_pos (f_pos x) (cosh_pos x)
    nlinarith [h.hw]
  have : 0 < exp (-w) := exp_pos _
  nlinarith

/-- Complex strict form: for `x ≠ w` and `z = (A, conj B) ≠ 0`, `z† M(x) z > 0`. -/
theorem lemmaS5_complex_pd (h : Hyp κ α β w) {x : ℝ} (hx : x ≠ w) {A B : ℂ}
    (hAB : A ≠ 0 ∨ B ≠ 0) :
    0 < Mdiag κ α (exp (-w)) x * Complex.normSq A + Mdiag κ β (exp (-w)) x * Complex.normSq B
      + 2 * Moff κ (exp (-w)) x * (A * B).re := by
  have huv : ‖A‖ ≠ 0 ∨ ‖B‖ ≠ 0 := by
    rcases hAB with hA | hB
    · exact Or.inl (norm_ne_zero_iff.mpr hA)
    · exact Or.inr (norm_ne_zero_iff.mpr hB)
  have hpd := lemmaS5_pd h hx huv
  unfold QM at hpd
  have hoff := (Moff_neg h x).le
  have hre : (A * B).re ≤ ‖A‖ * ‖B‖ := by
    rw [← Complex.norm_mul]; exact Complex.re_le_norm _
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  nlinarith [mul_le_mul_of_nonpos_left hre hoff]

/-- At `x = w`: `z† M(w) z = 2q (κ sinh w + b(w)) |A − conj B|²`. -/
theorem lemmaS5_complex_at_w (A B : ℂ) :
    Mdiag κ α (exp (-w)) w * Complex.normSq A + Mdiag κ β (exp (-w)) w * Complex.normSq B
      + 2 * Moff κ (exp (-w)) w * (A * B).re
      = 2 * exp (-w) * moff κ w w * Complex.normSq (A - (starRingEnd ℂ) B) := by
  rw [Mdiag_eq, Mdiag_eq, Moff_eq, at_w_alpha, at_w_alpha]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.conj_re,
    Complex.conj_im, Complex.mul_re]
  ring

/-- Complex kernel at `x = w`: `z† M(w) z = 0` iff `z = (A, conj B)` lies in `span{(1,1)}`. -/
theorem lemmaS5_complex_kernel (h : Hyp κ α β w) (A B : ℂ) :
    Mdiag κ α (exp (-w)) w * Complex.normSq A + Mdiag κ β (exp (-w)) w * Complex.normSq B
      + 2 * Moff κ (exp (-w)) w * (A * B).re = 0 ↔ A = (starRingEnd ℂ) B := by
  rw [lemmaS5_complex_at_w]
  have ht := trace_pos h w
  rw [at_w_alpha, at_w_alpha] at ht
  have hc : 0 < 2 * exp (-w) * moff κ w w := mul_pos (by positivity) (by linarith)
  rw [mul_eq_zero, Complex.normSq_eq_zero, sub_eq_zero]
  constructor
  · rintro (h0 | h0)
    · linarith
    · exact h0
  · intro h0; exact Or.inr h0

lemma Hyp.swap (h : Hyp κ α β w) : Hyp κ β α w :=
  ⟨h.hκ, h.hβ, h.hα, h.hw, by linarith [h.hκαβ, mul_comm α β], by linarith [h.hcal]⟩

/-- `q κ < α < κ / q` (written as `q α < κ`), with `q = e^{−w}`. -/
lemma alpha_bounds (h : Hyp κ α β w) : exp (-w) * κ < α ∧ exp (-w) * α < κ := by
  have hE : exp w * exp (-w) = 1 := by rw [← exp_add]; simp
  have hEe : exp (-w) < exp w := exp_lt_exp.mpr (by linarith [h.hw])
  have he : 0 < exp (-w) := exp_pos _
  have hβ : β = κ * (exp w + exp (-w)) - 2 * w - α := by
    have := h.hcal; rw [cosh_eq] at this; linarith
  have hk := h.hκαβ
  rw [hβ] at hk
  have hwα : 0 < w * α := mul_pos h.hw h.hα
  have hE2 : κ ^ 2 * (exp w * exp (-w)) = κ ^ 2 := by rw [hE, mul_one]
  constructor
  · by_contra hc
    replace hc := not_lt.mp hc
    have h1 : 0 ≤ (exp (-w) * κ - α) * (exp w * κ - α) :=
      mul_nonneg (by linarith) (by nlinarith [h.hκ])
    nlinarith
  · by_contra hc
    replace hc := not_lt.mp hc
    have hα' : exp w * κ ≤ α := by
      have h1 := mul_le_mul_of_nonneg_left hc (exp_pos w).le
      have h2 : exp w * (exp (-w) * α) = α := by rw [← mul_assoc, hE, one_mul]
      linarith
    have h1 : 0 ≤ (α - exp w * κ) * (α - exp (-w) * κ) :=
      mul_nonneg (by linarith) (by nlinarith [h.hκ])
    nlinarith

end Thm2Cert
