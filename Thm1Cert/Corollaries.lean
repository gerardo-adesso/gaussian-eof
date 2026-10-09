/-
Corollaries and the general-state limit for Theorem 1 of G. Adesso, "Optimality of Gaussian
entanglement of formation" (arXiv:2608.01909v3).

  * `theorem1_limit`: the affine bound passes to limits E_L → E, D_L → D. With the normalized
    Schmidt truncations C^{(L)} (finite rank, covered by `theorem1_upsilon` in the paired-basis
    matrix model), this gives Theorem 1 for every finite-energy state, the convergence
    G_t(C^{(L)}) → G_t(C), E(ψ_{C^{(L)}}) → E(ψ_C) being the Fock-space input of the SM
    (proof of Theorem S1, last paragraph);
  * `entropy_truncation`: E(ψ_{C^{(L)}}) → E(ψ_C) for the normalized truncations, at the level of
    Schmidt spectra (finite entropy);
  * `fixed_entanglement_endpoint` (q = t) and `separability_criterion` (q = 0, i.e. E(ψ) = 0
    implies D_t(ψ) ≥ 1), completing Eq. (S:fixedE) for 0 ≤ q ≤ t.
-/
import Thm1Cert.Upsilon

open Finset Real Filter Topology

set_option autoImplicit false

noncomputable section

namespace Thm1Cert

open Thm2Cert (EE gfun lam dt EE_formula lam_pos)

/-- **Limit step.** If the affine bound holds along a sequence of states with `E_L → E` and
`D_L → D`, it holds in the limit. -/
theorem theorem1_limit {q t : ℝ} (E D : ℝ) (EL DL : ℕ → ℝ)
    (h : ∀ L, EE q ≤ EL L + lam q t * (DL L - dt t q))
    (hE : Tendsto EL atTop (𝓝 E)) (hD : Tendsto DL atTop (𝓝 D)) :
    EE q ≤ E + lam q t * (D - dt t q) := by
  have hlim := hE.add ((hD.sub (tendsto_const_nhds (x := dt t q))).const_mul (lam q t))
  exact ge_of_tendsto hlim (Eventually.of_forall h)

/-- Entropy of the normalized Schmidt truncations converges: with `P_M = ∑_{n ≤ M} c_n²`,
`H((c^{(M)})²) = S_M/P_M + ln P_M → H(c²)`. -/
theorem entropy_truncation (c : ℕ → ℝ) (hnorm : HasSum (fun n => c n ^ 2) 1)
    (hH : Summable (fun n => negMulLog (c n ^ 2))) :
    Tendsto (fun M : ℕ => (∑ n ∈ range (M + 1), negMulLog (c n ^ 2)) / (∑ n ∈ range (M + 1), c n ^ 2)
      + log (∑ n ∈ range (M + 1), c n ^ 2)) atTop (𝓝 (∑' n, negMulLog (c n ^ 2))) := by
  have hP : Tendsto (fun M : ℕ => ∑ n ∈ range (M + 1), c n ^ 2) atTop (𝓝 1) :=
    (hnorm.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hS : Tendsto (fun M : ℕ => ∑ n ∈ range (M + 1), negMulLog (c n ^ 2)) atTop
      (𝓝 (∑' n, negMulLog (c n ^ 2))) :=
    (hH.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
  have hlog : Tendsto (fun M : ℕ => log (∑ n ∈ range (M + 1), c n ^ 2)) atTop (𝓝 0) := by
    rw [← Real.log_one]
    exact (Real.continuousAt_log one_ne_zero).tendsto.comp hP
  have := (hS.div hP one_ne_zero).add hlog
  simpa using this

/-- **Eq. (S:fixedE) at `q = t`**: `D_t(ψ) = G + 1 − t² ≥ 1 − t² = d_t(t)` since `G ≥ 0`. -/
theorem fixed_entanglement_endpoint {t G : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (hG : 0 ≤ G) :
    dt t t ≤ G + 1 - t ^ 2 := by
  have : 1 - t ^ 2 ≠ 0 := by nlinarith
  have hd : dt t t = 1 - t ^ 2 := by unfold dt; field_simp
  rw [hd]; linarith

lemma EE_nonneg {q : ℝ} (hq : 0 < q) (hq1 : q < 1) : 0 ≤ EE q := by
  unfold EE gfun
  set y := q ^ 2 / (1 - q ^ 2) with hy
  have hy0 : 0 < y := div_pos (by positivity) (by nlinarith)
  have h1 : log y ≤ log (y + 1) := Real.log_le_log hy0 (by linarith)
  have h2 : 0 ≤ log (y + 1) := Real.log_nonneg (by linarith)
  nlinarith

/-- **Separability criterion (`q = 0` in Eq. S:fixedE)**: if the affine bound holds for all
`0 < q < t` and `E(ψ) ≤ 0` (a product state), then `D_t(ψ) ≥ 1 = d_t(0)`. -/
theorem separability_criterion {t E D : ℝ} (ht0 : 0 < t) (ht : t ≤ 1)
    (h : ∀ q, 0 < q → q < t → EE q ≤ E + lam q t * (D - dt t q)) (hE : E ≤ 0) : 1 ≤ D := by
  have hle : ∀ q, 0 < q → q < t → dt t q ≤ D := by
    intro q hq hqt
    have hL := lam_pos hq hqt ht
    have h0 := EE_nonneg hq (lt_of_lt_of_le hqt ht)
    have := h q hq hqt
    by_contra hc
    rw [not_le] at hc
    have : lam q t * (D - dt t q) < 0 := mul_neg_of_pos_of_neg hL (by linarith)
    linarith
  have hcont : ContinuousAt (fun q => dt t q) 0 := by
    unfold dt
    exact ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).pow 2).div
      (continuousAt_const.sub (continuousAt_id.pow 2)) (by norm_num)
  have hc := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioo 0 t))
  have hev : ∀ᶠ q in 𝓝[Set.Ioo 0 t] (0 : ℝ), dt t q ≤ D :=
    eventually_nhdsWithin_of_forall (fun q hq => hle q hq.1 hq.2)
  have : (𝓝[Set.Ioo 0 t] (0 : ℝ)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo ht0.ne]
    exact ⟨le_rfl, ht0.le⟩
  have h1 := le_of_tendsto hc hev
  have hd0 : dt t 0 = 1 := by unfold dt; simp
  rwa [hd0] at h1

end Thm1Cert
