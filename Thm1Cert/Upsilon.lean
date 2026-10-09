/-
The Beigi–Rahimi-Keshari input in the form used in the Supplemental Material (Eqs. S:Upsilon,
S:parameters, S:Fmoments, S:UpsilonF), for diagonal states ρ_z = ∑ z_n² |n⟩⟨n|:

    Υ(ρ_z) = 2ν₀[(n̄+1) − T_z] + ω n̄ + H(z²),   ν₀ = λt, ν₁ = 0, ω = λ(1−t)²,
    n̄ = ∑ n z_n²,   T_z = ∑ (n+1) z_n z_{n+1}.

Certified: 𝓕_t(z) = t²(n̄+1) + n̄ − 2t T_z (S:Fmoments) and Υ(ρ_z) = H(z²) + λ𝓕_t(z) + λ(2t − t²)
(S:UpsilonF), both for finitely supported z and for the thermal sequences z^{(s)}; hence the
statement "inf Υ is attained on thermal states" (`BRKUpsilon`, restricted to diagonal states of
finite rank) implies the sequence form `BRK` used in `Assembly.lean`.
The diagonal-state moment formulas Tr(ρ_z a†a) = n̄, Tr(√ρ_z a √ρ_z a†) = T_z are inputs.
-/
import Thm1Cert.Assembly

open Finset Real Filter Topology

set_option autoImplicit false

noncomputable section

namespace Thm1Cert

/-- Mean photon number `n̄ = ∑ n z_n²`. -/
def nbar (z : ℕ → ℝ) : ℝ := ∑' n : ℕ, (n : ℝ) * z n ^ 2

/-- `T_z = ∑ (n+1) z_n z_{n+1} = Tr(√ρ_z a √ρ_z a†)` (Eq. S:Tz). -/
def Tz (z : ℕ → ℝ) : ℝ := ∑' n : ℕ, ((n : ℝ) + 1) * z n * z (n + 1)

/-- `Υ(ρ_z)` for `ν₀ = λt`, `ν₁ = 0`, `ω = λ(1−t)²` (Eqs. S:Upsilon, S:parameters). -/
def Ups (t L : ℝ) (z : ℕ → ℝ) : ℝ :=
  2 * (L * t) * ((nbar z + 1) - Tz z) + L * (1 - t) ^ 2 * nbar z + Hs z

/-- **Input (Beigi–Rahimi-Keshari)**, restricted to diagonal states of finite rank:
`Υ(ρ_z) ≥ inf_{0 ≤ s < 1} Υ(τ_s)`. -/
def BRKUpsilon (t L : ℝ) : Prop :=
  ∀ z : ℕ → ℝ, (∀ n, 0 ≤ z n) → (∃ M, ∀ n, M < n → z n = 0) → HasSum (fun n => z n ^ 2) 1 →
    ∀ c0 : ℝ, (∀ s, 0 ≤ s → s < 1 → c0 ≤ Ups t L (zs s)) → c0 ≤ Ups t L z

/-- **Eq. (S:Fmoments)** in `HasSum` form. -/
lemma Fmoments (t : ℝ) (z : ℕ → ℝ) {N T : ℝ} (h1 : HasSum (fun n => z n ^ 2) 1)
    (hN : HasSum (fun n : ℕ => (n : ℝ) * z n ^ 2) N)
    (hT : HasSum (fun n : ℕ => ((n : ℝ) + 1) * z n * z (n + 1)) T) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * (t * z n - z (n + 1)) ^ 2)
      (t ^ 2 * (N + 1) + N - 2 * t * T) := by
  have hA : HasSum (fun n : ℕ => ((n : ℝ) + 1) * z n ^ 2) (N + 1) := by
    have := hN.add h1; simpa [add_mul] using this
  have hB : HasSum (fun n : ℕ => ((n : ℝ) + 1) * z (n + 1) ^ 2) N := by
    have := (hasSum_nat_add_iff' 1).mpr hN
    simp only [range_one, sum_singleton, Nat.cast_zero, zero_mul, sub_zero] at this
    simpa using this
  have := ((hA.mul_left (t ^ 2)).add hB).sub (hT.mul_left (2 * t))
  convert this using 1
  funext n; ring

/-- **Eq. (S:UpsilonF)**: `Υ(ρ_z) = H(z²) + λ𝓕_t(z) + λ(2t − t²)`. -/
lemma Ups_eq (t L : ℝ) (z : ℕ → ℝ) (h1 : HasSum (fun n => z n ^ 2) 1)
    (hN : Summable (fun n : ℕ => (n : ℝ) * z n ^ 2))
    (hT : Summable (fun n : ℕ => ((n : ℝ) + 1) * z n * z (n + 1))) :
    Ups t L z = Hs z + L * Ft t z + L * (2 * t - t ^ 2) := by
  have hF := Fmoments t z h1 hN.hasSum hT.hasSum
  unfold Ups Ft nbar Tz
  rw [hF.tsum_eq]
  ring

lemma summable_of_finite_support (f : ℕ → ℝ) (M : ℕ) (hf : ∀ n, M < n → f n = 0) :
    Summable f :=
  summable_of_ne_finset_zero (s := range (M + 1)) (fun n hn => hf n (by simp at hn; omega))

lemma zs_summable {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    HasSum (fun n => zs s n ^ 2) 1 ∧ Summable (fun n : ℕ => (n : ℝ) * zs s n ^ 2) ∧
      Summable (fun n : ℕ => ((n : ℝ) + 1) * zs s n * zs s (n + 1)) := by
  have hx0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hx1 : s ^ 2 < 1 := by nlinarith
  have ha : 0 < 1 - s ^ 2 := by linarith
  have hg := hasSum_geometric_of_lt_one hx0 hx1
  have hn := hasSum_coe_mul_geometric_of_norm_lt_one
    (show ‖s ^ 2‖ < 1 by rw [Real.norm_of_nonneg hx0]; exact hx1)
  refine ⟨?_, ?_, ?_⟩
  · have := hg.mul_left (1 - s ^ 2)
    rw [mul_inv_cancel₀ ha.ne'] at this
    simpa [zs_sq hs1 hs0] using this
  · have := (hn.mul_left (1 - s ^ 2)).summable
    refine this.congr (fun n => ?_)
    rw [zs_sq hs1 hs0]; ring
  · have := ((hn.add hg).mul_left ((1 - s ^ 2) * s)).summable
    refine this.congr (fun n => ?_)
    unfold zs
    have hsq : √(1 - s ^ 2) ^ 2 = 1 - s ^ 2 := Real.sq_sqrt ha.le
    linear_combination (-((n : ℝ) + 1) * s ^ n * s ^ (n + 1)) * hsq

/-- The Beigi–Rahimi-Keshari input in Υ form implies the sequence form `BRK`. -/
theorem brk_of_upsilon {t L : ℝ} (hU : BRKUpsilon t L) : BRK t L := by
  intro z hz0 ⟨M, hM⟩ h1 c0 hc0
  have hNz := summable_of_finite_support (fun n : ℕ => (n : ℝ) * z n ^ 2) M
    (fun n hn => by simp [hM n hn])
  have hTz := summable_of_finite_support (fun n : ℕ => ((n : ℝ) + 1) * z n * z (n + 1)) M
    (fun n hn => by simp [hM n hn])
  have key := hU z hz0 ⟨M, hM⟩ h1 (c0 + L * (2 * t - t ^ 2)) (fun s hs0 hs1 => by
    obtain ⟨a, b, c⟩ := zs_summable hs0 hs1
    rw [Ups_eq t L (zs s) a b c]
    linarith [hc0 s hs0 hs1])
  rw [Ups_eq t L z h1 hNz hTz] at key
  linarith

/-- **Theorem 1** with the Beigi–Rahimi-Keshari input in its Υ form. -/
theorem theorem1_upsilon {q t : ℝ} (hq : 0 < q) (hqt : q < t) (ht : t ≤ 1)
    (hU : BRKUpsilon t (Thm2Cert.lam q t))
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
    Thm2Cert.EE q ≤ ∑' n, negMulLog (c n ^ 2)
      + Thm2Cert.lam q t * ((G + 1 - t ^ 2) - Thm2Cert.dt t q) :=
  theorem1 hq hqt ht (brk_of_upsilon hU) c hc hc0 hnorm hH X Y G hG rX cX rY cY
    hrX hcX hrY hcY hX hY

/-- **Endpoint `q = t < 1`** (Eq. S:endpoint): a state with `D_t(ψ) = d_t(t) = 1 − t²`
(i.e. `G = 0`) has `E(ψ) ≥ 𝓔(t)`. -/
theorem theorem1_endpoint_state {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hU : ∀ q, 0 < q → q < t → BRKUpsilon t (Thm2Cert.lam q t))
    (c : ℕ → ℝ) (hc : Antitone c) (hc0 : ∀ n, 0 ≤ c n) (hnorm : HasSum (fun n => c n ^ 2) 1)
    (hH : Summable (fun n => negMulLog (c n ^ 2)))
    (X Y : ℕ → ℕ → ℂ)
    (hG : HasSum (fun ij : ℕ × ℕ => ‖((t * c ij.1 : ℝ) : ℂ) * X ij.1 ij.2
      - (c ij.2 : ℂ) * Y ij.1 ij.2‖ ^ 2) 0)
    (rX cX rY cY : ℕ → ℝ)
    (hrX : ∀ i, 0 < c i → HasSum (fun j => ‖X i j‖ ^ 2) (rX i))
    (hcX : ∀ i, 0 < c i → HasSum (fun j => ‖X j i‖ ^ 2) (cX i))
    (hrY : ∀ i, 0 < c i → HasSum (fun j => ‖Y i j‖ ^ 2) (rY i))
    (hcY : ∀ i, 0 < c i → HasSum (fun j => ‖Y j i‖ ^ 2) (cY i))
    (hX : ∀ i, 0 < c i → rX i - cX i = 1) (hY : ∀ i, 0 < c i → rY i - cY i = 1) :
    Thm2Cert.EE t ≤ ∑' n, negMulLog (c n ^ 2) := by
  apply theorem1_endpoint ht0 ht1
  intro q hq hqt
  have h := theorem1_upsilon hq hqt ht1.le (hU q hq hqt) c hc hc0 hnorm hH X Y 0 hG
    rX cX rY cY hrX hcX hrY hcY hX hY
  have hdt : Thm2Cert.dt t t = 1 - t ^ 2 := by
    have : 1 - t ^ 2 ≠ 0 := by nlinarith
    unfold Thm2Cert.dt; field_simp
  rw [hdt]
  simpa using h

end Thm1Cert
