/-
Assembly of Theorem 1 of G. Adesso, "Optimality of Gaussian entanglement of formation"
(arXiv:2608.01909v3), Supplemental Material Sec. "Completion of the proof":

  * `thm1_spectrum`: for every decreasing Schmidt spectrum c with ∑ c_n² = 1 and finite entropy,
        𝓔(q) + λ_{q,t}(t−q)²/(1−q²) ≤ H(c²) + λ_{q,t} ∑ (n+1) d_n²
    (compression on normalized truncations, the closure, and the limit M → ∞);
  * `theorem1`: with the defect inequality (Theorem S1),
        E(ψ) + λ_{q,t} [D_t(ψ) − d_t(q)] ≥ 𝓔(q),     D_t = G_t + 1 − t²   (Eq. S:Gdef),
    in the Schmidt-basis matrix model of `Defect.lean`; the identifications E(ψ) = H(c²)
    (Eq. S:entropy), D_t = G_t + 1 − t² and the matrix model itself are inputs;
  * `theorem1_endpoint`: the case q = t < 1 (Eq. S:endpoint);
  * `fixed_entanglement`: E(ψ) ≤ 𝓔(q) ⇒ D_t(ψ) ≥ d_t(q) (Eq. S:fixedE).

Input: `BRK t λ` — the Beigi–Rahimi-Keshari meta log-Sobolev theorem, restricted to diagonal
states of finite rank: H(z²) + λ 𝓕_t(z) ≥ inf_{0≤s<1} [H((z^{(s)})²) + λ 𝓕_t(z^{(s)})].
-/
import Mathlib.Algebra.BigOperators.Field
import Thm1Cert.Closure

open Finset Real Filter Topology

set_option autoImplicit false

noncomputable section

namespace Thm1Cert

open Thm2Cert (EE gfun lam dt EE_formula lam_pos)

/-- **Input (Beigi–Rahimi-Keshari, diagonal states of finite rank).** For every finitely
supported `z ≥ 0` with `∑ z_n² = 1`, `H(z²) + λ 𝓕_t(z)` is at least the infimum over thermal
states. (Υ(ρ_z) = H(z²) + λ𝓕_t(z) + const for the parameters (S:parameters).) -/
def BRK (t L : ℝ) : Prop :=
  ∀ z : ℕ → ℝ, (∀ n, 0 ≤ z n) → (∃ M, ∀ n, M < n → z n = 0) → HasSum (fun n => z n ^ 2) 1 →
    ∀ c0 : ℝ, (∀ s, 0 ≤ s → s < 1 → c0 ≤ Hs (zs s) + L * Ft t (zs s)) → c0 ≤ Hs z + L * Ft t z

variable {q t : ℝ}

/-- Closure for a compressed, finitely supported sequence. -/
lemma closure_finite (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) (hB : BRK t (lam q t))
    (M : ℕ) (z : ℕ → ℝ) (hz0 : ∀ n, 0 ≤ z n) (hzs : ∀ n, M < n → z n = 0)
    (hzn : ∑ n ∈ range (M + 1), z n ^ 2 = 1) :
    phi (lam q t) t q ≤ ∑ n ∈ range (M + 1), negMulLog (z n ^ 2)
      + lam q t * ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * (t * z n - z (n + 1)) ^ 2 := by
  have hout : ∀ n, n ∉ range (M + 1) → M < n := fun n hn => by simp at hn; omega
  have hH : Hs z = ∑ n ∈ range (M + 1), negMulLog (z n ^ 2) := by
    unfold Hs
    exact tsum_eq_sum (fun n hn => by rw [hzs n (hout n hn)]; simp)
  have hF : Ft t z = ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * (t * z n - z (n + 1)) ^ 2 := by
    unfold Ft
    exact tsum_eq_sum (fun n hn => by
      rw [hzs n (hout n hn), hzs (n + 1) (by have := hout n hn; omega)]; ring)
  have hsum : HasSum (fun n => z n ^ 2) 1 := by
    rw [← hzn]
    exact hasSum_sum_of_ne_finset_zero (fun n hn => by rw [hzs n (hout n hn)]; ring)
  have := hB z hz0 ⟨M, hzs⟩ hsum (phi (lam q t) t q) (fun s hs0 hs1 => by
    rw [H_thermal hs0 hs1, F_thermal t hs0 hs1]
    exact support hq hqt ht hs0 hs1)
  rwa [hH, hF] at this

lemma negMulLog_div {x P : ℝ} (hx : 0 < x) (hP : 0 < P) :
    negMulLog (x / P) = negMulLog x / P + x / P * log P := by
  unfold negMulLog
  rw [Real.log_div hx.ne' hP.ne']
  field_simp
  ring

/-- **Truncation bound.** For `c_M > 0` and `P = ∑_{n ≤ M} c_n²`, the normalized truncation gives
`φ(q) ≤ S_M/P + ln P + λ (∑_{n<M}(n+1)d_n² + (M+1)t² c_M²)/P`. -/
lemma trunc_bound (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) (hB : BRK t (lam q t))
    (c : ℕ → ℝ) (hc : Antitone c) (_hc0 : ∀ n, 0 ≤ c n) (M : ℕ) (hcM : 0 < c M) :
    phi (lam q t) t q
      ≤ (∑ n ∈ range (M + 1), negMulLog (c n ^ 2)) / (∑ n ∈ range (M + 1), c n ^ 2)
        + log (∑ n ∈ range (M + 1), c n ^ 2)
        + lam q t * ((∑ n ∈ range M, ((n : ℝ) + 1) * dd t c n ^ 2
            + ((M : ℝ) + 1) * (t * c M) ^ 2) / (∑ n ∈ range (M + 1), c n ^ 2)) := by
  classical
  have ht0 : 0 < t := hq.trans hqt
  have hpos : ∀ n, n ≤ M → 0 < c n := fun n hn => lt_of_lt_of_le hcM (hc hn)
  set P := ∑ n ∈ range (M + 1), c n ^ 2 with hP
  have hP0 : 0 < P := sum_pos (fun n hn => pow_pos (hpos n (by simp at hn; omega)) 2)
    ⟨0, by simp⟩
  have hsP : 0 < √P := Real.sqrt_pos.mpr hP0
  set cM : ℕ → ℝ := fun n => if n ≤ M then c n / √P else 0 with hcM_def
  have hcMpos : ∀ n, n ≤ M → 0 < cM n := fun n hn => by
    simp only [hcM_def, ite_t hn]; exact div_pos (hpos n hn) hsP
  have hcManti : ∀ n, n < M → cM (n + 1) ≤ cM n := fun n hn => by
    simp only [hcM_def, ite_t (by omega : n + 1 ≤ M), ite_t hn.le]
    exact div_le_div_of_nonneg_right (hc (Nat.le_succ n)) hsP.le
  have hcMsupp : ∀ n, M < n → cM n = 0 := fun n hn => by
    simp only [hcM_def, show ¬ n ≤ M by omega, ↓reduceIte]
  have hsq : ∀ n, n ≤ M → cM n ^ 2 = c n ^ 2 / P := fun n hn => by
    simp only [hcM_def, ite_t hn]; rw [div_pow, Real.sq_sqrt hP0.le]
  have hcMnorm : ∑ n ∈ range (M + 1), cM n ^ 2 = 1 := by
    rw [sum_congr rfl (fun n hn => hsq n (by simp at hn; omega)), ← sum_div, div_self hP0.ne']
  obtain ⟨z, hz0, hzs, hzn, -, hzH, hzE⟩ :=
    compression ht0 cM hcMpos hcManti hcMsupp hcMnorm
  have hcl := closure_finite hq hqt ht hB M z hz0 hzs hzn
  have hL := (lam_pos hq hqt ht).le
  -- entropy of the truncation
  have hent : ∑ n ∈ range (M + 1), negMulLog (cM n ^ 2)
      = (∑ n ∈ range (M + 1), negMulLog (c n ^ 2)) / P + log P := by
    rw [sum_congr rfl (fun n hn => by
      rw [hsq n (by simp at hn; omega), negMulLog_div (pow_pos (hpos n (by simp at hn; omega)) 2) hP0])]
    rw [sum_add_distrib, ← sum_div, ← sum_mul, ← sum_div, ← hP, div_self hP0.ne', one_mul]
  -- energy of the truncation
  have hen : ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * pos (t * cM n - cM (n + 1)) ^ 2
      = (∑ n ∈ range M, ((n : ℝ) + 1) * dd t c n ^ 2 + ((M : ℝ) + 1) * (t * c M) ^ 2) / P := by
    rw [sum_range_succ, add_div, sum_div]
    congr 1
    · refine sum_congr rfl (fun n hn => ?_)
      simp only [mem_range] at hn
      simp only [hcM_def, ite_t hn.le, ite_t (by omega : n + 1 ≤ M)]
      rw [show t * (c n / √P) - c (n + 1) / √P = (1 / √P) * (t * c n - c (n + 1)) by
        field_simp]
      rw [pos_mul_left (by positivity), mul_pow, div_pow, one_pow, Real.sq_sqrt hP0.le]
      unfold dd; field_simp
    · simp only [hcM_def, ite_t le_rfl, show ¬ M + 1 ≤ M by omega, ↓reduceIte, sub_zero]
      have h0 : 0 ≤ t * (c M / √P) := by positivity
      rw [show pos (t * (c M / √P)) = t * (c M / √P) from max_eq_left h0, mul_pow, div_pow,
        Real.sq_sqrt hP0.le]
      field_simp
  calc phi (lam q t) t q ≤ _ := hcl
    _ ≤ ∑ n ∈ range (M + 1), negMulLog (cM n ^ 2)
        + lam q t * ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * pos (t * cM n - cM (n + 1)) ^ 2 :=
      add_le_add hzH (mul_le_mul_of_nonneg_left hzE hL)
    _ = _ := by rw [hent, hen]

/-- For decreasing summable `p ≥ 0`, `(M+1) p_M → 0`. -/
lemma tendsto_mul_antitone (p : ℕ → ℝ) (hp0 : ∀ n, 0 ≤ p n) (hanti : Antitone p) {A : ℝ}
    (hs : HasSum p A) : Tendsto (fun M : ℕ => ((M : ℝ) + 1) * p M) atTop (𝓝 0) := by
  set tail : ℕ → ℝ := fun k => A - ∑ n ∈ range k, p n with htail
  have htl : Tendsto tail atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := A)).sub hs.tendsto_sum_nat
    simpa [htail] using this
  have hdiv : Tendsto (fun M : ℕ => M / 2) atTop atTop :=
    tendsto_atTop_atTop.mpr (fun b => ⟨2 * b, fun a ha => by omega⟩)
  have hup : Tendsto (fun M : ℕ => 2 * tail (M / 2)) atTop (𝓝 0) := by
    simpa using (htl.comp hdiv).const_mul 2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun M => mul_nonneg (by positivity) (hp0 M)) (fun M => ?_)
  simp only
  set k := M / 2
  have hk : k ≤ M + 1 := by omega
  have h1 : ((M : ℝ) + 1 - k) * p M ≤ ∑ n ∈ Ico k (M + 1), p n := by
    have : ∑ n ∈ Ico k (M + 1), p M ≤ ∑ n ∈ Ico k (M + 1), p n :=
      sum_le_sum (fun n hn => hanti (by simp at hn; omega))
    rw [sum_const, Nat.card_Ico, nsmul_eq_mul] at this
    rw [Nat.cast_sub hk] at this
    push_cast at this
    linarith
  have h2 : ∑ n ∈ range (M + 1), p n ≤ A := sum_le_hasSum _ (fun n _ => hp0 n) hs
  have h3 := sum_range_add_sum_Ico p hk
  have h4 : ((M : ℝ) + 1) ≤ 2 * ((M : ℝ) + 1 - k) := by
    have : 2 * k ≤ M := Nat.mul_div_le M 2
    have : (2 : ℝ) * k ≤ M := by exact_mod_cast this
    linarith
  have h5 := mul_le_mul_of_nonneg_right h4 (hp0 M)
  simp only [htail]
  nlinarith

/-- **Theorem 1, spectral form.** -/
theorem thm1_spectrum (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) (hB : BRK t (lam q t))
    (c : ℕ → ℝ) (hc : Antitone c) (hc0 : ∀ n, 0 ≤ c n) (hnorm : HasSum (fun n => c n ^ 2) 1)
    (hH : Summable (fun n => negMulLog (c n ^ 2)))
    (hD : Summable (fun n : ℕ => ((n : ℝ) + 1) * dd t c n ^ 2)) :
    phi (lam q t) t q
      ≤ ∑' n, negMulLog (c n ^ 2) + lam q t * ∑' n : ℕ, ((n : ℝ) + 1) * dd t c n ^ 2 := by
  classical
  have hL := (lam_pos hq hqt ht).le
  by_cases hfin : ∃ R, c (R + 1) = 0
  · -- finite Schmidt rank
    set R := Nat.find hfin with hR
    have hR1 : c (R + 1) = 0 := Nat.find_spec hfin
    have hzero : ∀ n, R < n → c n = 0 := fun n hn =>
      le_antisymm (hR1 ▸ hc (by omega)) (hc0 n)
    have hcR : 0 < c R := by
      rcases (hc0 R).eq_or_lt with h | h
      · exfalso
        rcases Nat.eq_zero_or_pos R with h0 | h0
        · -- c 0 = 0 forces c ≡ 0, contradicting normalization
          have hall : ∀ n, c n = 0 := fun n =>
            le_antisymm ((hc (Nat.zero_le n)).trans (by rw [← h0]; exact h.symm.le)) (hc0 n)
          have : HasSum (fun n => c n ^ 2) 0 := by simp [hall]
          exact one_ne_zero (hnorm.unique this)
        · exact Nat.find_min hfin (show R - 1 < R by omega)
            (by rw [show R - 1 + 1 = R by omega]; exact h.symm)
      · exact h
    have hb := trunc_bound hq hqt ht hB c hc hc0 R hcR
    have hout : ∀ n, n ∉ range (R + 1) → R < n := fun n hn => by simp at hn; omega
    have hP : ∑ n ∈ range (R + 1), c n ^ 2 = 1 := by
      rw [← hnorm.tsum_eq]
      exact (tsum_eq_sum (fun n hn => by rw [hzero n (hout n hn)]; ring)).symm
    have hS : ∑' n, negMulLog (c n ^ 2) = ∑ n ∈ range (R + 1), negMulLog (c n ^ 2) :=
      tsum_eq_sum (fun n hn => by rw [hzero n (hout n hn)]; simp)
    have hDs : ∑' n : ℕ, ((n : ℝ) + 1) * dd t c n ^ 2
        = ∑ n ∈ range R, ((n : ℝ) + 1) * dd t c n ^ 2 + ((R : ℝ) + 1) * (t * c R) ^ 2 := by
      rw [tsum_eq_sum (s := range (R + 1)) (fun n hn => by
        unfold dd; rw [hzero n (hout n hn), hzero (n + 1) (by have := hout n hn; omega)]
        simp [pos]), sum_range_succ]
      unfold dd; rw [hR1, sub_zero, show pos (t * c R) = t * c R from
        max_eq_left (mul_nonneg (hq.trans hqt).le (hc0 R))]
    rw [hP, Real.log_one, div_one, div_one, add_zero] at hb
    rw [hS, hDs]; exact hb
  · -- infinite Schmidt rank: pass to the limit M → ∞
    simp only [not_exists] at hfin
    have hcpos : ∀ M, 0 < c M := fun M =>
      lt_of_lt_of_le ((hc0 (M + 1)).lt_of_ne (Ne.symm (hfin M))) (hc (Nat.le_succ M))
    have hP : Tendsto (fun M : ℕ => ∑ n ∈ range (M + 1), c n ^ 2) atTop (𝓝 1) :=
      (hnorm.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hS : Tendsto (fun M : ℕ => ∑ n ∈ range (M + 1), negMulLog (c n ^ 2)) atTop
        (𝓝 (∑' n, negMulLog (c n ^ 2))) :=
      (hH.hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    have hDt : Tendsto (fun M : ℕ => ∑ n ∈ range M, ((n : ℝ) + 1) * dd t c n ^ 2) atTop
        (𝓝 (∑' n : ℕ, ((n : ℝ) + 1) * dd t c n ^ 2)) := hD.hasSum.tendsto_sum_nat
    have hsqanti : Antitone (fun n => c n ^ 2) := fun a b hab =>
      pow_le_pow_left₀ (hc0 b) (hc hab) 2
    have hB0 : Tendsto (fun M : ℕ => ((M : ℝ) + 1) * (t * c M) ^ 2) atTop (𝓝 0) := by
      have := (tendsto_mul_antitone (fun n => c n ^ 2) (fun n => sq_nonneg _) hsqanti hnorm).const_mul
        (t ^ 2)
      simp only [mul_zero] at this
      refine this.congr (fun M => ?_)
      ring
    have hlog : Tendsto (fun M : ℕ => log (∑ n ∈ range (M + 1), c n ^ 2)) atTop (𝓝 0) := by
      rw [← Real.log_one]
      exact (Real.continuousAt_log one_ne_zero).tendsto.comp hP
    have hlim := ((hS.div hP one_ne_zero).add hlog).add
      (((hDt.add hB0).div hP one_ne_zero).const_mul (lam q t))
    simp only [div_one, add_zero] at hlim
    exact ge_of_tendsto hlim (Eventually.of_forall
      (fun M => trunc_bound hq hqt ht hB c hc hc0 M (hcpos M)))

lemma dt_identity (hq0 : 0 ≤ q) (hq1 : q < 1) : dt t q - 1 + t ^ 2 = (t - q) ^ 2 / (1 - q ^ 2) := by
  have : 1 - q ^ 2 ≠ 0 := by nlinarith [sq_nonneg q]
  unfold dt; field_simp; ring

/-- **Theorem 1** (affine extremality), matrix model. With `E(ψ) = H(c²)` (Eq. S:entropy) and
`D_t(ψ) = G + 1 − t²` (Eq. S:Gdef), where `G = ∑ |t c_i X_ij − c_j Y_ij|²` (Eq. S:Gmatrix):
`E(ψ) + λ_{q,t} [D_t(ψ) − d_t(q)] ≥ 𝓔(q)` for all `0 < q < t ≤ 1`. -/
theorem theorem1 (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) (hB : BRK t (lam q t))
    (c : ℕ → ℝ) (hc : Antitone c) (hc0 : ∀ n, 0 ≤ c n) (hnorm : HasSum (fun n => c n ^ 2) 1)
    (hH : Summable (fun n => negMulLog (c n ^ 2)))
    (X Y : ℕ → ℕ → ℂ) (G : ℝ)
    (hG : HasSum (fun ij : ℕ × ℕ => ‖((t * c ij.1 : ℝ) : ℂ) * X ij.1 ij.2
      - (c ij.2 : ℂ) * Y ij.1 ij.2‖ ^ 2) G)
    (rX cX rY cY : ℕ → ℝ)
    (hrX : ∀ i, 0 < c i → HasSum (fun j => ‖X i j‖ ^ 2) (rX i))
    (hcX : ∀ i, 0 < c i → HasSum (fun j => ‖X j i‖ ^ 2) (cX i))
    (hrY : ∀ i, 0 < c i → HasSum (fun j => ‖Y i j‖ ^ 2) (rY i))
    (hcY : ∀ i, 0 < c i → HasSum (fun j => ‖Y j i‖ ^ 2) (cY i))
    (hX : ∀ i, 0 < c i → rX i - cX i = 1) (hY : ∀ i, 0 < c i → rY i - cY i = 1) :
    EE q ≤ ∑' n, negMulLog (c n ^ 2) + lam q t * ((G + 1 - t ^ 2) - dt t q) := by
  have ht0 : 0 < t := hq.trans hqt
  obtain ⟨hDs, hDle⟩ := defect_inequality_tsum ht0 ht hc hc0 X Y G hG rX cX rY cY
    hrX hcX hrY hcY hX hY
  have h := thm1_spectrum hq hqt ht hB c hc hc0 hnorm hH hDs
  have hL := (lam_pos hq hqt ht).le
  have hq1 : q < 1 := lt_of_lt_of_le hqt ht
  unfold phi at h
  rw [show (G + 1 - t ^ 2) - dt t q = G - (dt t q - 1 + t ^ 2) by ring, dt_identity hq.le hq1]
  have := mul_le_mul_of_nonneg_left hDle hL
  nlinarith

/-- **Eq. (S:fixedE)**: `E(ψ) ≤ 𝓔(q)` implies `D_t(ψ) ≥ d_t(q)`. -/
theorem fixed_entanglement (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1) {E D : ℝ}
    (h1 : EE q ≤ E + lam q t * (D - dt t q)) (hE : E ≤ EE q) : dt t q ≤ D := by
  have hL := lam_pos hq hqt ht
  by_contra hc
  rw [not_le] at hc
  have : lam q t * (D - dt t q) < 0 := mul_neg_of_pos_of_neg hL (by linarith)
  linarith

lemma EE_continuousAt {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) : ContinuousAt EE s := by
  have hd : 1 - s ^ 2 ≠ 0 := by nlinarith
  have heq : (fun x => -log (1 - x ^ 2) - 2 * (x ^ 2 / (1 - x ^ 2)) * log x) =ᶠ[𝓝 s] EE := by
    have : Set.Ioo (0:ℝ) 1 ∈ 𝓝 s := Ioo_mem_nhds hs0 hs1
    filter_upwards [this] with x hx
    rw [EE_formula hx.1 hx.2]
  refine ContinuousAt.congr ?_ heq
  have c1 : ContinuousAt (fun x : ℝ => 1 - x ^ 2) s := by fun_prop
  exact (c1.log hd).neg.sub ((continuousAt_const.mul
    ((continuousAt_id.pow 2).div c1 hd)).mul (Real.continuousAt_log hs0.ne'))

/-- **Eq. (S:endpoint)**: for `t < 1`, if the affine bound holds for all `q < t` and
`D_t(ψ) = d_t(t) = 1 − t²`, then `E(ψ) ≥ 𝓔(t)`. -/
theorem theorem1_endpoint (ht0 : 0 < t) (ht1 : t < 1) {E : ℝ}
    (h : ∀ q, 0 < q → q < t → EE q ≤ E + lam q t * (dt t t - dt t q)) : EE t ≤ E := by
  have hle : ∀ q, 0 < q → q < t → EE q ≤ E := by
    intro q hq hqt
    have hL := (lam_pos hq hqt ht1.le).le
    have hq1 : q < 1 := hqt.trans ht1
    have e : dt t t - dt t q = -((t - q) ^ 2 / (1 - q ^ 2)) := by
      have a1 : 1 - q ^ 2 ≠ 0 := by nlinarith
      have a2 : 1 - t ^ 2 ≠ 0 := by nlinarith
      unfold dt; field_simp; ring
    have : 0 ≤ (t - q) ^ 2 / (1 - q ^ 2) := div_nonneg (sq_nonneg _) (by nlinarith)
    have := h q hq hqt
    rw [e] at this
    nlinarith
  have hc := (EE_continuousAt ht0 ht1).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioo 0 t))
  have hev : ∀ᶠ q in 𝓝[Set.Ioo 0 t] t, EE q ≤ E :=
    eventually_nhdsWithin_of_forall (fun q hq => hle q hq.1 hq.2)
  have : (𝓝[Set.Ioo 0 t] t).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo ht0.ne]
    exact ⟨ht0.le, le_rfl⟩
  exact le_of_tendsto hc hev

end Thm1Cert
