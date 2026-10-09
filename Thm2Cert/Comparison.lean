/-
Certificate for the comparison `M(x) ≥ γ K(x)` of Lemma S5, with the EXPLICIT constant
    γ = κ sinh w − w coth w − |α − β| / 2  > 0,
and for the rigidity inequality of the Supplemental Material:
    Q(O₁ψ) + Q(O₂ψ) ≤ −γ ∑_{l,r} c_l c_r z†_{lr} K(x_{lr}) z_{lr}   (= −γ (‖O₁ψ‖² + ‖O₂ψ‖²)),
for every finite Schmidt spectrum (kernel directions included), and its many-pair version.
Here Q(O_iψ) are the expressions (S:Q12); their derivation from the Euler equation, and the
identity ∑ c_l c_r z† K z = ‖O₁ψ‖² + ‖O₂ψ‖² (S:defects), are certified in `Derivation.lean`.
-/
import Thm2Cert.Identity

open Real Finset

set_option autoImplicit false

noncomputable section

namespace Thm2Cert

/-! ## `f` is even and nonincreasing in `|x|` -/

lemma f_anti {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) : f c ≤ f a := by
  rcases hac.eq_or_lt with h | h
  · subst h; exact le_rfl
  rcases ha.eq_or_lt with h0 | h0
  · subst h0
    rw [f_zero]
    have h1 := f_mul_sinh c
    have h2 : c < sinh c := self_lt_sinh_iff.mpr h
    have h3 : 0 < sinh c := sinh_pos_iff.mpr h
    nlinarith [f_pos c]
  · have hc : 0 < c := h0.trans h
    have hL := L1 h0 h
    have e1 := f_mul_sinh a
    have e2 := f_mul_sinh c
    have hsa : 0 < sinh a := sinh_pos_iff.mpr h0
    have hsc : 0 < sinh c := sinh_pos_iff.mpr hc
    have key : (f c - f a) * (sinh a * sinh c) = c * sinh a - a * sinh c := by
      linear_combination sinh a * e2 - sinh c * e1
    have : (f c - f a) * (sinh a * sinh c) < 0 := by rw [key]; linarith
    nlinarith [mul_pos hsa hsc]

lemma f_abs (x : ℝ) : f |x| = f x := by
  rcases abs_choice x with h | h
  · rw [h]
  · rw [h, f_neg]

/-! ## Two more half-angle identities -/

lemma minus_identity (κ0 w S C sy cy sxh cxh cx sxw sp cp sr cr F : ℝ)
    (hp : cp ^ 2 - sp ^ 2 = 1) (hr : cr ^ 2 - sr ^ 2 = 1)
    (hw : w = κ0 * (C - 1)) (hC : C = cr ^ 2 + sr ^ 2) (hS : S = 2 * sr * cr)
    (hsy : sy = 2 * sp * cp) (hcy : cy = cp ^ 2 + sp ^ 2)
    (hsxh : sxh = sp * cr + cp * sr) (hcxh : cxh = cp * cr + sp * sr)
    (hcx : cx = cxh ^ 2 + sxh ^ 2) (hsxw : sxw = sp * C + cp * S) :
    S * ((κ0 * S * cy + w * sy + C * F) - (κ0 * S + F * cx))
      = 2 * w * sp ^ 2 + 2 * sp * (sxw * (w - S * F)) := by
  subst hw; subst hcx; subst hsxw; subst hS; subst hC hsy hcy hsxh hcxh
  linear_combination (-2 * cr * sr * (F * cr ^ 2 + F * sr ^ 2 - 2 * cr * sr * κ0)) * hp
    + (-2 * sp ^ 2 * κ0 * (cr ^ 2 - sr ^ 2 + 1)) * hr

lemma plus_identity (κ0 w S C sy cy sxh cxh cx cxw sp cp sr cr F : ℝ)
    (hp : cp ^ 2 - sp ^ 2 = 1) (hr : cr ^ 2 - sr ^ 2 = 1)
    (hw : w = κ0 * (C - 1)) (hC : C = cr ^ 2 + sr ^ 2) (hS : S = 2 * sr * cr)
    (hsy : sy = 2 * sp * cp) (hcy : cy = cp ^ 2 + sp ^ 2)
    (hsxh : sxh = sp * cr + cp * sr) (hcxh : cxh = cp * cr + sp * sr)
    (hcx : cx = cxh ^ 2 + sxh ^ 2) (hcxw : cxw = cp * C + sp * S) :
    S * ((κ0 * S * cy + w * sy + C * F) + (κ0 * S + F * cx))
      = 2 * w * cp ^ 2 + 2 * w * cp * cxw + S * F * (C + cx) := by
  subst hw; subst hcx; subst hcxw; subst hS; subst hC hsy hcy hsxh hcxh
  linear_combination (-2 * κ0 * (cr ^ 4 + sr ^ 4 - 1)) * hp
    + (-2 * κ0 * (sp ^ 2 + 1) * (cr ^ 2 - sr ^ 2 + 1)) * hr

/-! ## Eigenvalue bounds at `κ = κ₀`, `δ = 0`: `N₀ ≥ (w / sinh w) K̃` -/

/-- Both eigenvalues of `M/(2q)` at `κ = κ₀`, `δ = 0` dominate `w / sinh w` times those of
`K/(2q) = [[cosh(x−w), −1], [−1, cosh(x−w)]]`. -/
lemma eig_bounds {w : ℝ} (hw : 0 < w) (κ0 : ℝ) (h3 : κ0 * (cosh w - 1) = w) (x : ℝ) :
    w * (cosh (x - w) - 1) ≤ sinh w * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w)
        + cosh w * f x) - (κ0 * sinh w + f x * cosh x)) ∧
    w * (cosh (x - w) + 1) ≤ sinh w * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w)
        + cosh w * f x) + (κ0 * sinh w + f x * cosh x)) := by
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
  have hsxh : sinh (x / 2) = sinh ((x - w) / 2) * cosh (w / 2)
      + cosh ((x - w) / 2) * sinh (w / 2) := by
    rw [← sinh_add]; congr 1; ring
  have hcxh : cosh (x / 2) = cosh ((x - w) / 2) * cosh (w / 2)
      + sinh ((x - w) / 2) * sinh (w / 2) := by
    rw [← cosh_add]; congr 1; ring
  have hcx : cosh x = cosh (x / 2) ^ 2 + sinh (x / 2) ^ 2 := by
    rw [← cosh_two_mul]; congr 1; ring
  have hsxw : sinh ((x + w) / 2) = sinh ((x - w) / 2) * cosh w
      + cosh ((x - w) / 2) * sinh w := by
    rw [← sinh_add]; congr 1; ring
  have hcxw : cosh ((x + w) / 2) = cosh ((x - w) / 2) * cosh w
      + sinh ((x - w) / 2) * sinh w := by
    rw [← cosh_add]; congr 1; ring
  have hm := minus_identity κ0 w (sinh w) (cosh w) (sinh (x - w)) (cosh (x - w)) (sinh (x / 2))
    (cosh (x / 2)) (cosh x) (sinh ((x + w) / 2)) (sinh ((x - w) / 2)) (cosh ((x - w) / 2))
    (sinh (w / 2)) (cosh (w / 2)) (f x) hp hr h3.symm hCr hSr hsy hcy hsxh hcxh hcx hsxw
  have hpl := plus_identity κ0 w (sinh w) (cosh w) (sinh (x - w)) (cosh (x - w)) (sinh (x / 2))
    (cosh (x / 2)) (cosh x) (cosh ((x + w) / 2)) (sinh ((x - w) / 2)) (cosh ((x - w) / 2))
    (sinh (w / 2)) (cosh (w / 2)) (f x) hp hr h3.symm hCr hSr hsy hcy hsxh hcxh hcx hcxw
  have hS : 0 < sinh w := sinh_pos_iff.mpr hw
  have hfw : f w * sinh w = w := f_mul_sinh w
  -- sign: sinh((x−w)/2) · sinh((x+w)/2) · (w − sinh w · f x) ≥ 0
  have hsign : 0 ≤ sinh ((x - w) / 2) * (sinh ((x + w) / 2) * (w - sinh w * f x)) := by
    rcases le_total w x with hxw | hxw
    · -- x ≥ w
      have h1 : 0 ≤ sinh ((x - w) / 2) := sinh_nonneg_iff.mpr (by linarith)
      have h2 : 0 ≤ sinh ((x + w) / 2) := sinh_nonneg_iff.mpr (by linarith)
      have h3' : f x ≤ f w := by
        rw [← f_abs x]; exact f_anti hw.le (le_trans hxw (le_abs_self x))
      have h4 : 0 ≤ w - sinh w * f x := by nlinarith
      exact mul_nonneg h1 (mul_nonneg h2 h4)
    · have h1 : sinh ((x - w) / 2) ≤ 0 := sinh_nonpos_iff.mpr (by linarith)
      rcases le_total (-w) x with hxw' | hxw'
      · -- −w ≤ x ≤ w
        have h2 : 0 ≤ sinh ((x + w) / 2) := sinh_nonneg_iff.mpr (by linarith)
        have h3' : f w ≤ f x := by
          rw [← f_abs x]; exact f_anti (abs_nonneg x) (abs_le.mpr ⟨hxw', hxw⟩)
        have h4 : w - sinh w * f x ≤ 0 := by nlinarith
        have : sinh ((x + w) / 2) * (w - sinh w * f x) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h2 h4
        exact mul_nonneg_of_nonpos_of_nonpos h1 this
      · -- x ≤ −w
        have h2 : sinh ((x + w) / 2) ≤ 0 := sinh_nonpos_iff.mpr (by linarith)
        have h3' : f x ≤ f w := by
          rw [← f_abs x]; exact f_anti hw.le (by rw [abs_of_nonpos (by linarith)]; linarith)
        have h4 : 0 ≤ w - sinh w * f x := by nlinarith
        have : sinh ((x + w) / 2) * (w - sinh w * f x) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg h2 h4
        exact mul_nonneg_of_nonpos_of_nonpos h1 this
  have hcxw_pos : 0 < cosh ((x + w) / 2) := cosh_pos _
  have hcp : 0 < cosh ((x - w) / 2) := cosh_pos _
  have hCx : 0 < cosh w + cosh x := by linarith [cosh_pos w, cosh_pos x]
  have hw2 : w * (cosh ((x - w) / 2) ^ 2 - sinh ((x - w) / 2) ^ 2) = w := by rw [hp, mul_one]
  constructor
  · rw [hm, hcy]; linarith
  · rw [hpl, hcy]
    have : 0 ≤ sinh w * f x * (cosh w + cosh x) :=
      (mul_pos (mul_pos hS (f_pos x)) hCx).le
    have : 0 ≤ 2 * w * cosh ((x - w) / 2) * cosh ((x + w) / 2) :=
      (mul_pos (mul_pos (by linarith) hcp) hcxw_pos).le
    linarith

/-! ## The explicit constant `γ` -/

/-- `γ = κ sinh w − w coth w − |α − β|/2`. -/
def gam (κ α β w : ℝ) : ℝ := κ * sinh w - w * cosh w / sinh w - |α - β| / 2

variable {κ α β w : ℝ}

lemma gam_mul_sinh (hw : 0 < w) :
    gam κ α β w * sinh w = κ * sinh w ^ 2 - w * cosh w - |α - β| / 2 * sinh w := by
  have hS : sinh w ≠ 0 := (sinh_pos_iff.mpr hw).ne'
  unfold gam
  rw [sub_mul, sub_mul, div_mul_cancel₀ _ hS]; ring

theorem gam_pos (h : Hyp κ α β w) : 0 < gam κ α β w := by
  have hw := h.hw
  have hS : 0 < sinh w := sinh_pos_iff.mpr hw
  have hC1 : 0 < cosh w - 1 := by have := one_lt_cosh.mpr hw.ne'; linarith
  have hSC : sinh w ^ 2 = cosh w ^ 2 - 1 := by rw [cosh_sq]; ring
  have hk := kappa0_le h
  rw [div_le_iff₀ hC1] at hk
  -- R := κ S² − w C > 0
  have hR : 0 < κ * sinh w ^ 2 - w * cosh w := by
    have : κ * sinh w ^ 2 = κ * (cosh w - 1) * (cosh w + 1) := by rw [hSC]; ring
    nlinarith [cosh_pos w]
  -- (|δ| S / 2)² < R²
  have hδ : (α - β) ^ 2 ≤ 4 * ((κ * cosh w - w) ^ 2 - κ ^ 2) := by
    have hs : α + β = 2 * (κ * cosh w - w) := by linarith [h.hcal]
    have e : (α - β) ^ 2 = (α + β) ^ 2 - 4 * (α * β) := by ring
    rw [e, hs]; nlinarith [h.hκαβ]
  have hsq : (|α - β| / 2 * sinh w) ^ 2 < (κ * sinh w ^ 2 - w * cosh w) ^ 2 := by
    have e : (κ * sinh w ^ 2 - w * cosh w) ^ 2
        = ((κ * cosh w - w) ^ 2 - κ ^ 2) * sinh w ^ 2 + w ^ 2 := by
      rw [hSC]; ring
    rw [e, mul_pow, div_pow, sq_abs]
    have : 0 < w ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hδ (sq_nonneg (sinh w))
    nlinarith
  have hlt := abs_lt_of_sq_lt_sq hsq hR.le
  have hlt' : |α - β| / 2 * sinh w < κ * sinh w ^ 2 - w * cosh w := lt_of_abs_lt hlt
  have hpos : 0 < gam κ α β w * sinh w := by rw [gam_mul_sinh hw]; linarith
  exact (mul_pos_iff_of_pos_right hS).mp hpos

/-- `γ ≤ α − qκ` and `q γ ≤ κ − q α` (the boundary weights dominate `γ`). -/
lemma gam_le (h : Hyp κ α β w) :
    gam κ α β w ≤ α - exp (-w) * κ ∧ exp (-w) * gam κ α β w ≤ κ - exp (-w) * α := by
  have hw := h.hw
  have hS : 0 < sinh w := sinh_pos_iff.mpr hw
  have hq : cosh w - sinh w = exp (-w) := cosh_sub_sinh w
  have hE : exp (-w) * (cosh w + sinh w) = 1 := by
    rw [cosh_add_sinh, ← exp_add]; simp
  have hwC : w ≤ w * cosh w / sinh w := by
    rw [le_div_iff₀ hS]; nlinarith [sinh_lt_cosh w]
  have hwC0 : 0 ≤ w * cosh w / sinh w := by linarith
  have hab := h.hcal
  have hd1 : -(α - β) ≤ |α - β| := neg_le_abs _
  have hd2 : α - β ≤ |α - β| := le_abs_self _
  have hqk : κ * cosh w - κ * sinh w = exp (-w) * κ := by rw [← mul_sub, hq, mul_comm]
  unfold gam
  constructor
  · linarith
  · have e : κ - exp (-w) * α - exp (-w) * (κ * sinh w - w * cosh w / sinh w - |α - β| / 2)
        = exp (-w) * (κ * (cosh w + sinh w) - α
          - (κ * sinh w - w * cosh w / sinh w - |α - β| / 2)) := by
      linear_combination (-κ) * hE
    have : 0 ≤ κ * (cosh w + sinh w) - α - (κ * sinh w - w * cosh w / sinh w - |α - β| / 2) := by
      linarith
    nlinarith [exp_pos (-w)]

lemma gam_swap : gam κ α β w = gam κ β α w := by unfold gam; rw [abs_sub_comm]

/-! ## `M(x)/(2q) ≥ γ K(x)/(2q)` -/

lemma amgm_cross (δ sy cy s d : ℝ) (hy : cy ^ 2 - sy ^ 2 = 1) (hc : 1 ≤ cy) :
    2 * δ * sy * s * d ≤ |δ| * ((cy - 1) * s ^ 2 + (cy + 1) * d ^ 2) := by
  have hX : 0 ≤ (cy - 1) * s ^ 2 + (cy + 1) * d ^ 2 := by
    have := sq_nonneg s; have := sq_nonneg d; nlinarith
  have hsq : (2 * sy * s * d) ^ 2 ≤ ((cy - 1) * s ^ 2 + (cy + 1) * d ^ 2) ^ 2 := by
    have : ((cy - 1) * s ^ 2 + (cy + 1) * d ^ 2) ^ 2 - (2 * sy * s * d) ^ 2
        = ((cy - 1) * s ^ 2 - (cy + 1) * d ^ 2) ^ 2 + 4 * s ^ 2 * d ^ 2 * (cy ^ 2 - sy ^ 2 - 1) := by
      ring
    rw [hy, sub_self, mul_zero, add_zero] at this
    nlinarith [sq_nonneg ((cy - 1) * s ^ 2 - (cy + 1) * d ^ 2)]
  have habs := abs_le_of_sq_le_sq hsq hX
  calc 2 * δ * sy * s * d = δ * (2 * sy * s * d) := by ring
    _ ≤ |δ * (2 * sy * s * d)| := le_abs_self _
    _ = |δ| * |2 * sy * s * d| := abs_mul _ _
    _ ≤ |δ| * ((cy - 1) * s ^ 2 + (cy + 1) * d ^ 2) :=
        mul_le_mul_of_nonneg_left habs (abs_nonneg _)

theorem N_comparison (h : Hyp κ α β w) (x u v : ℝ) :
    gam κ α β w * (cosh (x - w) * u ^ 2 - 2 * u * v + cosh (x - w) * v ^ 2)
      ≤ mdiag κ α w x * u ^ 2 - 2 * moff κ w x * u * v + mdiag κ β w x * v ^ 2 := by
  have hw := h.hw
  have hS : 0 < sinh w := sinh_pos_iff.mpr hw
  have hC1 : 0 < cosh w - 1 := by have := one_lt_cosh.mpr hw.ne'; linarith
  set κ0 := w / (cosh w - 1) with hκ0def
  have h3 : κ0 * (cosh w - 1) = w := div_mul_cancel₀ w hC1.ne'
  have hSC : sinh w ^ 2 = cosh w ^ 2 - 1 := by rw [cosh_sq]; ring
  obtain ⟨hAm, hAp⟩ := eig_bounds hw κ0 h3 x
  have hg := gam_mul_sinh (κ := κ) (α := α) (β := β) hw
  -- Γ S = γ S + |δ| S / 2, with Γ = w/S + (κ − κ₀) S
  have hΓ : w + (κ - κ0) * sinh w ^ 2 = gam κ α β w * sinh w + |α - β| / 2 * sinh w := by
    rw [hg, hSC]; linear_combination (-(cosh w + 1)) * h3
  have hy : cosh (x - w) ^ 2 - sinh (x - w) ^ 2 = 1 := by rw [cosh_sq]; ring
  have hcy1 : 1 ≤ cosh (x - w) := one_le_cosh _
  -- P₁ = A − c − γ (cosh y − 1) ≥ |δ|/2 (cosh y − 1), P₂ likewise
  set A := κ * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x with hA
  set c := κ * sinh w + f x * cosh x with hc
  have hP1 : sinh w * (|α - β| / 2 * (cosh (x - w) - 1))
      ≤ sinh w * (A - c - gam κ α β w * (cosh (x - w) - 1)) := by
    have e : sinh w * (A - c - gam κ α β w * (cosh (x - w) - 1))
        = sinh w * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
          - (κ0 * sinh w + f x * cosh x)) - w * (cosh (x - w) - 1)
          + (cosh (x - w) - 1) * (w + (κ - κ0) * sinh w ^ 2 - gam κ α β w * sinh w) := by
      rw [hA, hc]; ring
    rw [e, hΓ]; nlinarith
  have hP2 : sinh w * (|α - β| / 2 * (cosh (x - w) + 1))
      ≤ sinh w * (A + c - gam κ α β w * (cosh (x - w) + 1)) := by
    have e : sinh w * (A + c - gam κ α β w * (cosh (x - w) + 1))
        = sinh w * ((κ0 * sinh w * cosh (x - w) + w * sinh (x - w) + cosh w * f x)
          + (κ0 * sinh w + f x * cosh x)) - w * (cosh (x - w) + 1)
          + (cosh (x - w) + 1) * (w + (κ - κ0) * sinh w ^ 2 - gam κ α β w * sinh w) := by
      rw [hA, hc]; ring
    rw [e, hΓ]; nlinarith
  have hP1' := le_of_mul_le_mul_left hP1 hS
  have hP2' := le_of_mul_le_mul_left hP2 hS
  -- diagonal entries through A, using the calibration
  have hmα : mdiag κ α w x = A - (α - β) / 2 * sinh (x - w) := by
    unfold mdiag; rw [hA]; linear_combination sinh (x - w) * h.hcal
  have hmβ : mdiag κ β w x = A + (α - β) / 2 * sinh (x - w) := by
    unfold mdiag; rw [hA]; linear_combination sinh (x - w) * h.hcal
  have hmo : moff κ w x = c := by unfold moff b; rw [hc]
  rw [hmα, hmβ, hmo]
  -- change of variables s = (u+v)/2, d = (u−v)/2
  have e : (A - (α - β) / 2 * sinh (x - w)) * u ^ 2 - 2 * c * u * v
      + (A + (α - β) / 2 * sinh (x - w)) * v ^ 2
      - gam κ α β w * (cosh (x - w) * u ^ 2 - 2 * u * v + cosh (x - w) * v ^ 2)
      = 2 * (A - c - gam κ α β w * (cosh (x - w) - 1)) * ((u + v) / 2) ^ 2
        - 2 * (α - β) * sinh (x - w) * ((u + v) / 2) * ((u - v) / 2)
        + 2 * (A + c - gam κ α β w * (cosh (x - w) + 1)) * ((u - v) / 2) ^ 2 := by ring
  have hcross := amgm_cross (α - β) (sinh (x - w)) (cosh (x - w)) ((u + v) / 2) ((u - v) / 2)
    hy hcy1
  have i1 := mul_le_mul_of_nonneg_right hP1' (sq_nonneg ((u + v) / 2))
  have i2 := mul_le_mul_of_nonneg_right hP2' (sq_nonneg ((u - v) / 2))
  have : 0 ≤ (A - (α - β) / 2 * sinh (x - w)) * u ^ 2 - 2 * c * u * v
      + (A + (α - β) / 2 * sinh (x - w)) * v ^ 2
      - gam κ α β w * (cosh (x - w) * u ^ 2 - 2 * u * v + cosh (x - w) * v ^ 2) := by
    rw [e]; linarith
  linarith

/-! ## Lemma S5, comparison part: `M(x) ≥ γ K(x)` -/

/-- Diagonal entry of `K(x)`: `e^{−x} + q² eˣ` (the off-diagonal entry is `−2q`). -/
def Kdiag (q x : ℝ) : ℝ := exp (-x) + q ^ 2 * exp x

lemma Kdiag_eq (w x : ℝ) : Kdiag (exp (-w)) x = 2 * exp (-w) * cosh (x - w) := by
  unfold Kdiag
  simp only [cosh_eq, Real.exp_neg, Real.exp_sub, neg_sub]
  field_simp
  ring

/-- The quadratic form of `K(x)`. -/
def QK (w x u v : ℝ) : ℝ :=
  Kdiag (exp (-w)) x * u ^ 2 + 2 * (-2 * exp (-w)) * u * v + Kdiag (exp (-w)) x * v ^ 2

/-- **Lemma S5 (iv)**: `M(x) ≥ γ K(x)` for every real `x`, with the explicit
`γ = κ sinh w − w coth w − |α−β|/2 > 0` (`gam_pos`). -/
theorem lemmaS5_gamma (h : Hyp κ α β w) (x u v : ℝ) :
    gam κ α β w * QK w x u v ≤ QM κ α β w x u v := by
  rw [QM_eq]
  unfold QK
  rw [Kdiag_eq]
  have := N_comparison h x u v
  have hq : 0 < 2 * exp (-w) := by positivity
  have := mul_le_mul_of_nonneg_left this hq.le
  linarith

/-- A real symmetric 2×2 form that is nonnegative on `ℝ²` is nonnegative on `z = (A, conj B)`. -/
lemma psd_complex {p11 p12 p22 : ℝ}
    (hP : ∀ u v : ℝ, 0 ≤ p11 * u ^ 2 + 2 * p12 * u * v + p22 * v ^ 2) (A B : ℂ) :
    0 ≤ p11 * Complex.normSq A + p22 * Complex.normSq B + 2 * p12 * (A * B).re := by
  have hre1 : (A * B).re ≤ ‖A‖ * ‖B‖ := by
    rw [← Complex.norm_mul]; exact Complex.re_le_norm _
  have hre2 : -(‖A‖ * ‖B‖) ≤ (A * B).re := by
    have := Complex.re_le_norm (-(A * B))
    rw [norm_neg, Complex.norm_mul, Complex.neg_re] at this
    linarith
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  rcases le_total 0 p12 with hp | hp
  · have := hP ‖A‖ (-‖B‖)
    nlinarith [mul_le_mul_of_nonneg_left hre2 hp]
  · have := hP ‖A‖ ‖B‖
    nlinarith [mul_le_mul_of_nonpos_left hre1 hp]

/-- Complex form of `M(x) ≥ γ K(x)`, for `z = (A, conj B)`. -/
theorem lemmaS5_gamma_complex (h : Hyp κ α β w) (x : ℝ) (A B : ℂ) :
    gam κ α β w * (Kdiag (exp (-w)) x * (Complex.normSq A + Complex.normSq B)
        + 2 * (-2 * exp (-w)) * (A * B).re)
      ≤ Mdiag κ α (exp (-w)) x * Complex.normSq A + Mdiag κ β (exp (-w)) x * Complex.normSq B
        + 2 * Moff κ (exp (-w)) x * (A * B).re := by
  have hP : ∀ u v : ℝ, 0 ≤ (Mdiag κ α (exp (-w)) x - gam κ α β w * Kdiag (exp (-w)) x) * u ^ 2
      + 2 * (Moff κ (exp (-w)) x - gam κ α β w * (-2 * exp (-w))) * u * v
      + (Mdiag κ β (exp (-w)) x - gam κ α β w * Kdiag (exp (-w)) x) * v ^ 2 := by
    intro u v
    have := lemmaS5_gamma h x u v
    unfold QM QK at this
    linarith
  have := psd_complex hP A B
  linarith

/-! ## Rigidity: `Q(O₁ψ) + Q(O₂ψ) ≤ −γ (‖O₁ψ‖² + ‖O₂ψ‖²)` -/

/-- Summand of `‖O₁ψ‖² + ‖O₂ψ‖² = ∑ c_l c_r z† K(x_lr) z` (Eq. S:defects) in the
`p`-variables: `c_l c_r K₁₁ = p_r + q² p_l`, `c_l c_r K₁₂ = −2q c_l c_r`. -/
def kterm (q cl cr : ℝ) (A B : ℂ) : ℝ :=
  (cr ^ 2 + q ^ 2 * cl ^ 2) * (Complex.normSq A + Complex.normSq B)
    - 4 * q * (cl * cr) * (A * B).re

lemma kterm_nonneg {q cl cr : ℝ} (hq : 0 ≤ q) (hl : 0 ≤ cl) (hr : 0 ≤ cr) (A B : ℂ) :
    0 ≤ kterm q cl cr A B := by
  unfold kterm
  have hre : (A * B).re ≤ ‖A‖ * ‖B‖ := by
    rw [← Complex.norm_mul]; exact Complex.re_le_norm _
  have hm : 0 ≤ q * (cl * cr) := mul_nonneg hq (mul_nonneg hl hr)
  have hP : 2 * (q * (cl * cr)) ≤ cr ^ 2 + q ^ 2 * cl ^ 2 := by nlinarith [sq_nonneg (cr - q * cl)]
  have hN : 2 * (‖A‖ * ‖B‖) ≤ ‖A‖ ^ 2 + ‖B‖ ^ 2 := by nlinarith [sq_nonneg (‖A‖ - ‖B‖)]
  have hab : 0 ≤ ‖A‖ * ‖B‖ := by positivity
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have i1 := mul_le_mul_of_nonneg_left hre hm
  have i2 := mul_le_mul_of_nonneg_right hP hab
  have i3 := mul_le_mul_of_nonneg_left hN (by positivity : (0:ℝ) ≤ cr ^ 2 + q ^ 2 * cl ^ 2)
  nlinarith

/-- Termwise comparison, for all Schmidt coefficients `cl, cr ≥ 0`. -/
theorem term_ge (h : Hyp κ α β w) {cl cr : ℝ} (hl : 0 ≤ cl) (hr : 0 ≤ cr) (A B : ℂ) :
    gam κ α β w * kterm (exp (-w)) cl cr A B ≤ term κ α β (exp (-w)) cl cr A B := by
  obtain ⟨ga1, ga2⟩ := gam_le h
  obtain ⟨gb1, gb2⟩ := gam_le h.swap
  rw [← gam_swap] at gb1 gb2
  have he : 0 < exp (-w) := exp_pos _
  have nA := Complex.normSq_nonneg A
  have nB := Complex.normSq_nonneg B
  rcases hl.eq_or_lt with hl0 | hlp
  · subst hl0
    unfold term wdiag woff kterm
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      Real.sqrt_zero, add_zero, sub_zero]
    have i1 := mul_le_mul_of_nonneg_right ga1 (mul_nonneg (sq_nonneg cr) nA)
    have i2 := mul_le_mul_of_nonneg_right gb1 (mul_nonneg (sq_nonneg cr) nB)
    nlinarith
  rcases hr.eq_or_lt with hr0 | hrp
  · subst hr0
    unfold term wdiag woff kterm
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
      Real.sqrt_zero, add_zero, sub_zero, zero_add]
    have i1 := mul_le_mul_of_nonneg_right ga2 (mul_nonneg (mul_nonneg he.le (sq_nonneg cl)) nA)
    have i2 := mul_le_mul_of_nonneg_right gb2 (mul_nonneg (mul_nonneg he.le (sq_nonneg cl)) nB)
    nlinarith
  · have e1 := E1 hlp hrp
    have e2 := E2 hlp hrp
    have e3 := E3 hlp hrp
    have e4 := E4 hlp hrp
    have keyM : term κ α β (exp (-w)) cl cr A B = cl * cr *
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
    have keyK : kterm (exp (-w)) cl cr A B = cl * cr *
        (Kdiag (exp (-w)) (log (cl / cr)) * (Complex.normSq A + Complex.normSq B)
          + 2 * (-2 * exp (-w)) * (A * B).re) := by
      unfold kterm Kdiag
      linear_combination
        (-(Complex.normSq A + Complex.normSq B)) * e2
        + (-exp (-w) ^ 2 * (Complex.normSq A + Complex.normSq B)) * e1
    rw [keyM, keyK]
    have := mul_le_mul_of_nonneg_left (lemmaS5_gamma_complex h (log (cl / cr)) A B)
      (mul_pos hlp hrp).le
    linarith

variable {ι : Type*} [Fintype ι]

/-- **Rigidity inequality** for one pair: `Q(O₁ψ) + Q(O₂ψ) ≤ −γ ∑ c_l c_r z† K z`. -/
theorem rigidity (h : Hyp κ α β w) (c : ι → ℝ) (hc : ∀ l, 0 ≤ c l)
    (A B : ι → ι → ℂ) (nA nB : ℝ)
    (hA0 : nA = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A l r))
    (hA1 : nA + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A l r))
    (hB0 : nB = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B l r))
    (hB1 : nB + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B l r)) :
    Q1 α β κ (exp (-w)) nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      + Q2 α β κ (exp (-w)) nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B)
      ≤ -(gam κ α β w * ∑ l, ∑ r, kterm (exp (-w)) (c l) (c r) (A l r) (B l r)) := by
  rw [mainid_general c A B α β κ (exp (-w)) nA nB hA0 hA1 hB0 hB1, neg_le_neg_iff,
    Finset.mul_sum]
  refine Finset.sum_le_sum (fun l _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun r _ => term_ge h (hc l) (hc r) (A l r) (B l r))

/-- **Rigidity, many pairs.** For `m` pairs `j` (all sharing the Schmidt coefficients `c`)
with hypotheses `Hyp κ_j α_j β_j w_j`, and any `0 < γ₀ ≤ min_j γ_j`:
`∑_j [Q(O₁,ⱼψ) + Q(O₂,ⱼψ)] ≤ −γ₀ ∑_j ∑ c_l c_r z†_j K_j z_j`. In particular, if the left side
is `≥ 0` (second-order stability with `⟨O_{i,j}⟩ = 0`), every defect sum vanishes. -/
theorem rigidity_multi {m : ℕ} (κ α β w : Fin m → ℝ) (h : ∀ j, Hyp (κ j) (α j) (β j) (w j))
    (γ0 : ℝ) (hγ0 : 0 < γ0) (hγ : ∀ j, γ0 ≤ gam (κ j) (α j) (β j) (w j))
    (c : ι → ℝ) (hc : ∀ l, 0 ≤ c l) (A B : Fin m → ι → ι → ℂ) (nA nB : Fin m → ℝ)
    (hA0 : ∀ j, nA j = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A j l r))
    (hA1 : ∀ j, nA j + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A j l r))
    (hB0 : ∀ j, nB j = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B j l r))
    (hB1 : ∀ j, nB j + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B j l r)) :
    (∑ j, (Q1 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
        (sfA c (B j)) (sfC c (A j) (B j))
      + Q2 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
        (sfA c (B j)) (sfC c (A j) (B j))))
      ≤ -(γ0 * ∑ j, ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r)) ∧
    (0 ≤ ∑ j, (Q1 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
        (sfA c (B j)) (sfC c (A j) (B j))
      + Q2 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
        (sfA c (B j)) (sfC c (A j) (B j))) →
      ∀ j, ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r) = 0) := by
  have hK : ∀ j, 0 ≤ ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r) := fun j =>
    Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun r _ =>
      kterm_nonneg (exp_pos _).le (hc l) (hc r) _ _))
  have hj : ∀ j, (Q1 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j))
        (sfA c (A j)) (sfA c (B j)) (sfC c (A j) (B j))
      + Q2 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
        (sfA c (B j)) (sfC c (A j) (B j)))
      ≤ -(γ0 * ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r)) := by
    intro j
    have := rigidity (h j) c hc (A j) (B j) (nA j) (nB j) (hA0 j) (hA1 j) (hB0 j) (hB1 j)
    have := mul_le_mul_of_nonneg_right (hγ j) (hK j)
    linarith
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
  rw [Finset.sum_neg_distrib, ← Finset.mul_sum] at hsum
  refine ⟨hsum, fun h0 j => ?_⟩
  have htot : γ0 * ∑ j, ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r) ≤ 0 := by
    linarith
  have hnn : 0 ≤ ∑ j, ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r) :=
    Finset.sum_nonneg (fun j _ => hK j)
  have hle : ∑ j, ∑ l, ∑ r, kterm (exp (-w j)) (c l) (c r) (A j l r) (B j l r) ≤ 0 := by
    by_contra hcon
    have := mul_pos hγ0 (not_le.mp hcon)
    linarith
  have hzero := le_antisymm hle hnn
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hK j)).mp hzero j (Finset.mem_univ j)

end Thm2Cert
