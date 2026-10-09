/-
Certificate for the thermal log-Sobolev closure of the Supplemental Material of
G. Adesso, "Optimality of Gaussian entanglement of formation" (arXiv:2608.01909v3):

  * Eq. (S:thermalF): for z^{(s)}_n = √(1−s²) sⁿ,
        H((z^{(s)})²) = 𝓔(s),     𝓕_t(z^{(s)}) = (t−s)²/(1−s²);
  * Eq. (S:support): for 0 < q < t ≤ 1 and λ = λ_{q,t}, the function
        φ(s) = 𝓔(s) + λ (t−s)²/(1−s²)
    attains its minimum over 0 ≤ s < 1 at s = q (monotonicity of Λ_t, Eq. S:LambdaMon).

The meta log-Sobolev theorem of Beigi and Rahimi-Keshari is NOT formalized; it enters
`Assembly.lean` as an explicit hypothesis (`BRK`).
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Thm1Cert.Compression
import Thm2Cert.Reduction

open Finset Real

set_option autoImplicit false

noncomputable section

namespace Thm1Cert

open Thm2Cert (EE gfun lam dt EE_formula lam_pos)

/-- Entropy `H(z²) = ∑ −z_n² ln z_n²` of a square-root sequence. -/
def Hs (z : ℕ → ℝ) : ℝ := ∑' n, negMulLog (z n ^ 2)

/-- `𝓕_t(z) = ∑ (n+1)(t z_n − z_{n+1})²` (Eq. S:Fdef). -/
def Ft (t : ℝ) (z : ℕ → ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) * (t * z n - z (n + 1)) ^ 2

/-- Thermal square-root sequence `z^{(s)}_n = √(1−s²) sⁿ` (Eq. S:thermalz). -/
def zs (s : ℝ) (n : ℕ) : ℝ := √(1 - s ^ 2) * s ^ n

lemma zs_sq {s : ℝ} (hs1 : s < 1) (hs0 : 0 ≤ s) (n : ℕ) :
    zs s n ^ 2 = (1 - s ^ 2) * (s ^ 2) ^ n := by
  unfold zs
  rw [mul_pow, Real.sq_sqrt (by nlinarith), ← pow_mul, ← pow_mul, mul_comm 2 n]

lemma EE_zero : EE 0 = 0 := by
  unfold EE gfun; simp

/-- **Eq. (S:thermalF), entropy part**: `H((z^{(s)})²) = 𝓔(s)`. -/
theorem H_thermal {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : Hs (zs s) = EE s := by
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    rw [EE_zero]
    unfold Hs
    have : ∀ n, negMulLog (zs 0 n ^ 2) = 0 := by
      intro n
      rw [zs_sq (by norm_num) le_rfl]
      rcases n with _ | n
      · simp
      · simp
    simp only [this, tsum_zero]
  · have hx0 : 0 ≤ s ^ 2 := sq_nonneg s
    have hx1 : s ^ 2 < 1 := by nlinarith
    have ha : 0 < 1 - s ^ 2 := by linarith
    have hg := hasSum_geometric_of_lt_one hx0 hx1
    have hn := hasSum_coe_mul_geometric_of_norm_lt_one
      (show ‖s ^ 2‖ < 1 by rw [Real.norm_of_nonneg hx0]; exact hx1)
    have hsum := (hg.mul_left (-(1 - s ^ 2) * log (1 - s ^ 2))).add
      (hn.mul_left (-(1 - s ^ 2) * log (s ^ 2)))
    unfold Hs
    have hterm : ∀ n : ℕ, negMulLog (zs s n ^ 2)
        = -(1 - s ^ 2) * log (1 - s ^ 2) * (s ^ 2) ^ n
          + -(1 - s ^ 2) * log (s ^ 2) * ((n : ℝ) * (s ^ 2) ^ n) := by
      intro n
      rw [zs_sq hs1 hs0 n]
      unfold negMulLog
      rw [Real.log_mul ha.ne' (pow_ne_zero _ (by positivity)), Real.log_pow]
      ring
    simp only [hterm]
    rw [hsum.tsum_eq, EE_formula hpos hs1, Real.log_pow]
    field_simp
    push_cast
    ring

/-- **Eq. (S:thermalF), energy part**: `𝓕_t(z^{(s)}) = (t−s)²/(1−s²)`. -/
theorem F_thermal (t : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Ft t (zs s) = (t - s) ^ 2 / (1 - s ^ 2) := by
  have hx0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hx1 : s ^ 2 < 1 := by nlinarith
  have ha : 0 < 1 - s ^ 2 := by linarith
  have hg := hasSum_geometric_of_lt_one hx0 hx1
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖s ^ 2‖ < 1 by rw [Real.norm_of_nonneg hx0]; exact hx1)
  have hsum := (hn.add hg).mul_left ((1 - s ^ 2) * (t - s) ^ 2)
  unfold Ft
  have hterm : ∀ n : ℕ, ((n : ℝ) + 1) * (t * zs s n - zs s (n + 1)) ^ 2
      = (1 - s ^ 2) * (t - s) ^ 2 * ((n : ℝ) * (s ^ 2) ^ n + (s ^ 2) ^ n) := by
    intro n
    have e : t * zs s n - zs s (n + 1) = (t - s) * zs s n := by unfold zs; ring
    rw [e, mul_pow, zs_sq hs1 hs0 n]; ring
  simp only [hterm]
  rw [hsum.tsum_eq]
  field_simp
  ring

/-! ## The supporting-line inequality (S:support) -/

/-- `φ(s) = 𝓔(s) + λ (t−s)²/(1−s²)`. -/
def phi (L t s : ℝ) : ℝ := EE s + L * ((t - s) ^ 2 / (1 - s ^ 2))

/-- A continuous closed form of `φ` on `[0,1)`. -/
def psi (L t s : ℝ) : ℝ :=
  -log (1 - s ^ 2) - 2 * s * (s * log s) / (1 - s ^ 2) + L * ((t - s) ^ 2 / (1 - s ^ 2))

lemma phi_eq_psi (L t : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) : phi L t s = psi L t s := by
  unfold phi psi
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0; rw [EE_zero]; simp
  · rw [EE_formula hpos hs1]; ring

lemma psi_continuousAt (L t : ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ContinuousAt (psi L t) s := by
  have hd : 1 - s ^ 2 ≠ 0 := by nlinarith
  unfold psi
  have c1 : ContinuousAt (fun s : ℝ => 1 - s ^ 2) s := by fun_prop
  have c2 : ContinuousAt (fun s : ℝ => s * log s) s := continuous_mul_log.continuousAt
  refine ((ContinuousAt.neg (c1.log hd)).sub ?_).add (continuousAt_const.mul ?_)
  · exact ((continuousAt_const.mul continuousAt_id).mul c2).div c1 hd
  · exact (((continuousAt_const.sub continuousAt_id).pow 2)).div c1 hd

/-- `g(s) = −2 s ln s − λ (t−s)(1−ts)`; `φ'(s) = 2 g(s)/(1−s²)²`. -/
def gsign (L t s : ℝ) : ℝ := -2 * s * log s - L * (t - s) * (1 - t * s)

lemma psi_hasDerivAt (L t : ℝ) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    HasDerivAt (psi L t) (2 * gsign L t s / (1 - s ^ 2) ^ 2) s := by
  have hd : 1 - s ^ 2 ≠ 0 := by nlinarith
  have d1 : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-(2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_sub 1
  have d2 : HasDerivAt (fun s : ℝ => s * log s) (log s + 1) s := hasDerivAt_mul_log hs0.ne'
  have d3 := ((hasDerivAt_id' s).const_mul (2:ℝ)).mul d2
  have d4 := ((hasDerivAt_id' s).const_sub t).pow 2
  have h := ((d1.log hd).neg.sub (d3.div d1 hd)).add ((d4.div d1 hd).const_mul L)
  unfold psi
  convert h using 1
  unfold gsign
  simp only [Pi.mul_apply, Pi.pow_apply]
  field_simp
  ring

/-- `k(s) = −s ln s/(1−s)` is strictly increasing on `(0,1)`. -/
lemma k_strictMono : StrictMonoOn (fun s : ℝ => -(s * log s) / (1 - s)) (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro s hs
    have : 1 - s ≠ 0 := by linarith [hs.2]
    exact (continuous_mul_log.continuousAt.neg.div (continuousAt_const.sub continuousAt_id)
      this).continuousWithinAt
  · intro s hs
    rw [interior_Ioo] at hs
    have h1 : 1 - s ≠ 0 := by linarith [hs.2]
    have hd := ((hasDerivAt_mul_log hs.1.ne').neg).div ((hasDerivAt_id' s).const_sub 1) h1
    rw [show deriv (fun s : ℝ => -(s * log s) / (1 - s)) s
        = (-(log s + 1) * (1 - s) - (-(s * log s)) * -1) / (1 - s) ^ 2 from hd.deriv]
    have hl := Real.log_lt_sub_one_of_pos hs.1 (by linarith [hs.2] : s ≠ 1)
    have : 0 < (1 - s) ^ 2 := by positivity
    apply div_pos _ this
    nlinarith

/-- `Λ_t(s) = −2 s ln s/((t−s)(1−ts))` is strictly increasing on `(0,t)` (Eq. S:LambdaMon). -/
lemma Lambda_strictMono {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    StrictMonoOn (fun s : ℝ => -2 * s * log s / ((t - s) * (1 - t * s))) (Set.Ioo 0 t) := by
  intro s1 hs1 s2 hs2 h12
  have hs1' : s1 ∈ Set.Ioo (0:ℝ) 1 := ⟨hs1.1, by linarith [hs1.2]⟩
  have hs2' : s2 ∈ Set.Ioo (0:ℝ) 1 := ⟨hs2.1, by linarith [hs2.2]⟩
  have hk := k_strictMono hs1' hs2' h12
  simp only at hk
  have hk1 : 0 < -(s1 * log s1) / (1 - s1) := by
    apply div_pos _ (by linarith [hs1'.2])
    have := Real.log_neg hs1'.1 hs1'.2
    nlinarith [hs1'.1]
  -- m(s) = (1−s)/((t−s)(1−ts)) is positive and nondecreasing
  have hm1 : 0 < (1 - s1) / ((t - s1) * (1 - t * s1)) := by
    apply div_pos (by linarith [hs1'.2]) (mul_pos (by linarith [hs1.2]) (by nlinarith [hs1'.2]))
  have hm : (1 - s1) / ((t - s1) * (1 - t * s1)) ≤ (1 - s2) / ((t - s2) * (1 - t * s2)) := by
    have a1 : 0 < t - s1 := by linarith [hs1.2]
    have a2 : 0 < t - s2 := by linarith [hs2.2]
    have b1 : 0 < 1 - t * s1 := by nlinarith [hs1'.2]
    have b2 : 0 < 1 - t * s2 := by nlinarith [hs2'.2]
    rw [div_le_div_iff₀ (mul_pos a1 b1) (mul_pos a2 b2)]
    have e1 : (1 - s1) * (t - s2) ≤ (1 - s2) * (t - s1) := by nlinarith
    have e2 : 1 - t * s2 ≤ 1 - t * s1 := by nlinarith
    have := mul_le_mul e1 e2 b2.le (by nlinarith [hs2'.2])
    nlinarith
  have f1 : -2 * s1 * log s1 / ((t - s1) * (1 - t * s1))
      = 2 * (-(s1 * log s1) / (1 - s1)) * ((1 - s1) / ((t - s1) * (1 - t * s1))) := by
    have : 1 - s1 ≠ 0 := by linarith [hs1'.2]
    field_simp
  have f2 : -2 * s2 * log s2 / ((t - s2) * (1 - t * s2))
      = 2 * (-(s2 * log s2) / (1 - s2)) * ((1 - s2) / ((t - s2) * (1 - t * s2))) := by
    have : 1 - s2 ≠ 0 := by linarith [hs2'.2]
    field_simp
  simp only
  rw [f1, f2]
  have := mul_lt_mul hk hm hm1 (by linarith)
  nlinarith

/-- Sign of `g`: negative on `(0,q)`, positive on `(q,1)`. -/
lemma gsign_cases {q t : ℝ} (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) {s : ℝ} (hs0 : 0 < s)
    (hs1 : s < 1) :
    (s < q → gsign (lam q t) t s < 0) ∧ (q < s → 0 < gsign (lam q t) t s) := by
  have hL := lam_pos hq hqt ht
  have hΛq : -2 * q * log q / ((t - q) * (1 - t * q)) = lam q t := by
    unfold lam; ring_nf
  have hfac : ∀ s, 0 < s → s < t →
      gsign (lam q t) t s = (t - s) * (1 - t * s)
        * (-2 * s * log s / ((t - s) * (1 - t * s)) - lam q t) := by
    intro s h0 h1
    have e1 : t - s ≠ 0 := by linarith
    have e2 : 1 - t * s ≠ 0 := by nlinarith
    have e3 : 1 - s * t ≠ 0 := by rw [mul_comm]; exact e2
    unfold gsign; field_simp
  have ht0 : 0 < t := hq.trans hqt
  constructor
  · intro hsq
    have hst : s < t := hsq.trans hqt
    rw [hfac s hs0 hst]
    have := Lambda_strictMono ht0 ht ⟨hs0, hst⟩ ⟨hq, hqt⟩ hsq
    simp only at this
    rw [hΛq] at this
    exact mul_neg_of_pos_of_neg (mul_pos (by linarith) (by nlinarith)) (by linarith)
  · intro hqs
    rcases lt_or_ge s t with hst | hst
    · rw [hfac s hs0 hst]
      have := Lambda_strictMono ht0 ht ⟨hq, hqt⟩ ⟨hs0, hst⟩ hqs
      simp only at this
      rw [hΛq] at this
      exact mul_pos (mul_pos (by linarith) (by nlinarith)) (by linarith)
    · unfold gsign
      have hl : log s < 0 := Real.log_neg hs0 hs1
      have : 0 ≤ (s - t) * (1 - t * s) := mul_nonneg (by linarith) (by nlinarith)
      nlinarith [mul_pos hs0 (neg_pos.mpr hl)]

/-- **Eq. (S:support)**: for `0 < q < t ≤ 1` and `λ = λ_{q,t}`,
`𝓔(s) + λ(t−s)²/(1−s²) ≥ 𝓔(q) + λ(t−q)²/(1−q²)` for all `0 ≤ s < 1`. -/
theorem support {q t : ℝ} (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s < 1) : phi (lam q t) t q ≤ phi (lam q t) t s := by
  have hq1 : q < 1 := lt_of_lt_of_le hqt ht
  rw [phi_eq_psi _ _ hq.le hq1, phi_eq_psi _ _ hs0 hs1]
  have hderiv : ∀ x, 0 < x → x < 1 →
      deriv (psi (lam q t) t) x = 2 * gsign (lam q t) t x / (1 - x ^ 2) ^ 2 :=
    fun x h0 h1 => (psi_hasDerivAt _ _ h0 h1).deriv
  have hdiff : ∀ x, 0 < x → x < 1 → DifferentiableAt ℝ (psi (lam q t) t) x :=
    fun x h0 h1 => (psi_hasDerivAt _ _ h0 h1).differentiableAt
  rcases le_total s q with hsq | hsq
  · -- antitone on [0, q]
    have hanti : AntitoneOn (psi (lam q t) t) (Set.Icc 0 q) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 q)
      · intro x hx
        exact (psi_continuousAt _ _ hx.1 (lt_of_le_of_lt hx.2 hq1)).continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hdiff x hx.1 (hx.2.trans hq1)).differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        rw [hderiv x hx.1 (hx.2.trans hq1)]
        have := (gsign_cases hq hqt ht hx.1 (hx.2.trans hq1)).1 hx.2
        have : 0 < (1 - x ^ 2) ^ 2 := by
          have : 0 < 1 - x ^ 2 := by nlinarith [hx.2.trans hq1, hx.1]
          positivity
        apply div_nonpos_of_nonpos_of_nonneg (by linarith) this.le
    exact hanti ⟨hs0, hsq⟩ ⟨hq.le, le_rfl⟩ hsq
  · -- monotone on [q, 1)
    have hmono : MonotoneOn (psi (lam q t) t) (Set.Ico q 1) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ico q 1)
      · intro x hx
        exact (psi_continuousAt _ _ (hq.le.trans hx.1) hx.2).continuousWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        exact (hdiff x (hq.trans hx.1) hx.2).differentiableWithinAt
      · intro x hx
        rw [interior_Ico] at hx
        rw [hderiv x (hq.trans hx.1) hx.2]
        have := (gsign_cases hq hqt ht (hq.trans hx.1) hx.2).2 hx.1
        apply div_nonneg (by linarith) (by positivity)
    exact hmono ⟨le_rfl, hq1⟩ ⟨hsq, hs1⟩ hsq

end Thm1Cert
