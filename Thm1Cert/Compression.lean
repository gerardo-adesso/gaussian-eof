/-
Certificate for Theorem S2 (geometric isotonic compression) of the Supplemental Material of
G. Adesso, "Optimality of Gaussian entanglement of formation" (arXiv:2608.01909v3).

For c_0 ≥ … ≥ c_M > 0 with ∑ c_n² = 1 (c_{M+1} = 0) and t > 0 there is a normalized
z_0, …, z_M ≥ 0 (z_{M+1} = 0) with
    z_{n+1} ≤ t z_n,     H(z²) ≤ H(c²),
    ∑ (n+1)(t z_n − z_{n+1})² ≤ ∑ (n+1)(t c_n − c_{n+1})₊².

The pool-adjacent-violators construction is formalized as an existence proof by strong induction
on the number of level breaks: pooling two adjacent maximal constant runs that violate
monotonicity preserves the total mass, can only raise every prefix sum, and does not increase
the drop energy (S:senergy); prefix domination then gives H(z²) ≤ H(c²) by a tangent-line /
Abel-summation form of Schur concavity.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Thm1Cert.Defect

open Finset Real

set_option autoImplicit false

noncomputable section

namespace Thm1Cert

variable (M : ℕ) (t : ℝ)

/-- Weights `w_n = t^{2n}`. -/
def wt (n : ℕ) : ℝ := (t ^ n) ^ 2

/-- Total weighted mass `∑_{n ≤ M} w_n ℓ_n`. -/
def mass (ℓ : ℕ → ℝ) : ℝ := ∑ n ∈ range (M + 1), wt t n * ℓ n

/-- Prefix mass `∑_{n ≤ K} w_n ℓ_n`. -/
def pre (ℓ : ℕ → ℝ) (K : ℕ) : ℝ := ∑ n ∈ range (K + 1), wt t n * ℓ n

/-- Drop energy (S:senergy): `∑_{n ≤ M} (n+1) t^{2n+2} ((√ℓ_n − √ℓ_{n+1})₊)²`. -/
def en (ℓ : ℕ → ℝ) : ℝ :=
  ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * (t ^ (n + 1)) ^ 2 * pos (√(ℓ n) - √(ℓ (n + 1))) ^ 2

/-- Number of level breaks on `[0, M]`. -/
def brk (ℓ : ℕ → ℝ) : ℕ := ((range M).filter (fun n => ℓ n ≠ ℓ (n + 1))).card

/-- Invariants of the pooling procedure, relative to the initial levels `r`. -/
structure Inv (r ℓ : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ ℓ n
  supp : ∀ n, M < n → ℓ n = 0
  mass_eq : mass M t ℓ = mass M t r
  prefix_ge : ∀ K, K ≤ M → pre t r K ≤ pre t ℓ K
  en_le : en M t ℓ ≤ en M t r

variable {M t}

lemma wt_pos (ht : 0 < t) (n : ℕ) : 0 < wt t n := by unfold wt; positivity

lemma pos_mul_left {k : ℝ} (hk : 0 ≤ k) (u : ℝ) : pos (k * u) = k * pos u := by
  unfold pos
  rcases le_total u 0 with h | h
  · rw [max_eq_right h, max_eq_right (mul_nonpos_of_nonneg_of_nonpos hk h), mul_zero]
  · rw [max_eq_left h, max_eq_left (mul_nonneg hk h)]

/-- **Pooling step.** If two adjacent levels violate monotonicity, pooling the two maximal
constant runs around them preserves the invariants and strictly reduces the number of breaks. -/
theorem pool_step (ht : 0 < t) {r ℓ : ℕ → ℝ} (hI : Inv M t r ℓ) {n : ℕ} (hn : n < M)
    (hv : ℓ n < ℓ (n + 1)) : ∃ ℓ', Inv M t r ℓ' ∧ brk M ℓ' < brk M ℓ := by
  classical
  -- left run [a, n]
  have hPa : ∃ a, ∀ k, a ≤ k → k ≤ n → ℓ k = ℓ n :=
    ⟨n, fun k h1 h2 => by rw [le_antisymm h2 h1]⟩
  set a := Nat.find hPa with ha_def
  have ha : ∀ k, a ≤ k → k ≤ n → ℓ k = ℓ n := Nat.find_spec hPa
  have han : a ≤ n := Nat.find_min' hPa (fun k h1 h2 => by rw [le_antisymm h2 h1])
  have hamin : 0 < a → ℓ (a - 1) ≠ ℓ n := by
    intro hpos heq
    apply Nat.find_min hPa (Nat.sub_lt hpos one_pos)
    intro k h1 h2
    rcases Nat.lt_or_ge k a with hk | hk
    · rw [show k = a - 1 by omega]; exact heq
    · exact ha k hk h2
  -- right run [n+1, b]
  set Pb : ℕ → Prop := fun b => n + 1 ≤ b ∧ ∀ k, n + 1 ≤ k → k ≤ b → ℓ k = ℓ (n + 1) with hPb
  have hPb1 : Pb (n + 1) := ⟨le_rfl, fun k h1 h2 => by rw [le_antisymm h2 h1]⟩
  set b := Nat.findGreatest Pb M with hb_def
  have hb : Pb b := Nat.findGreatest_spec (m := n + 1) (by omega) hPb1
  have hbM : b ≤ M := Nat.findGreatest_le M
  have hbmax : b < M → ℓ (b + 1) ≠ ℓ (n + 1) := by
    intro hlt heq
    apply Nat.findGreatest_is_greatest (P := Pb) (k := b + 1) (Nat.lt_succ_self b) (show b + 1 ≤ M from hlt)
    refine ⟨by omega, fun k h1 h2 => ?_⟩
    rcases Nat.lt_or_ge b k with hk | hk
    · rw [show k = b + 1 by omega]; exact heq
    · exact hb.2 k h1 hk
  have hnb : n + 1 ≤ b := hb.1
  set x := ℓ n with hx
  set y := ℓ (n + 1) with hy
  have hval : ∀ k, a ≤ k → k ≤ b → x ≤ ℓ k ∧ ℓ k ≤ y := by
    intro k h1 h2
    rcases Nat.lt_or_ge n k with hk | hk
    · rw [hb.2 k hk h2]; exact ⟨hv.le, le_rfl⟩
    · rw [ha k h1 hk]; exact ⟨le_rfl, hv.le⟩
  -- pooled level
  set W := ∑ k ∈ Icc a b, wt t k with hW
  have hWpos : 0 < W := sum_pos (fun k _ => wt_pos ht k) ⟨a, by simp; omega⟩
  set m := (∑ k ∈ Icc a b, wt t k * ℓ k) / W with hm
  have hxm : x ≤ m := by
    rw [hm, le_div_iff₀ hWpos, hW, mul_sum]
    exact sum_le_sum (fun k hk => by
      simp only [mem_Icc] at hk
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left (hval k hk.1 hk.2).1 (wt_pos ht k).le)
  have hmy : m ≤ y := by
    rw [hm, div_le_iff₀ hWpos, hW, mul_sum]
    exact sum_le_sum (fun k hk => by
      simp only [mem_Icc] at hk
      rw [mul_comm y]; exact mul_le_mul_of_nonneg_left (hval k hk.1 hk.2).2 (wt_pos ht k).le)
  set ℓ' : ℕ → ℝ := fun k => if a ≤ k ∧ k ≤ b then m else ℓ k with hℓ'
  set g : ℕ → ℝ := fun k => wt t k * (ℓ' k - ℓ k) with hg
  have hgout : ∀ k, ¬ (a ≤ k ∧ k ≤ b) → g k = 0 := by
    intro k hk; simp only [hg, hℓ', ite_f hk, sub_self, mul_zero]
  have hgtot : ∑ k ∈ range (M + 1), g k = 0 := by
    have hsub : Icc a b ⊆ range (M + 1) := by
      intro k hk; simp only [mem_Icc] at hk; simp only [mem_range]; omega
    rw [← sum_subset hsub (fun k _ hk => hgout k (by simpa using hk))]
    have : ∑ k ∈ Icc a b, g k = m * W - ∑ k ∈ Icc a b, wt t k * ℓ k := by
      rw [hW, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl (fun k hk => ?_)
      simp only [mem_Icc] at hk
      simp only [hg, hℓ', ite_t hk]; ring
    rw [this, hm, div_mul_cancel₀ _ hWpos.ne', sub_self]
  have hgnn : ∀ k, k ≤ n → 0 ≤ g k := by
    intro k hk
    by_cases h : a ≤ k ∧ k ≤ b
    · simp only [hg, hℓ', ite_t h, ha k h.1 hk]
      exact mul_nonneg (wt_pos ht k).le (by linarith)
    · rw [hgout k h]
  have hgnp : ∀ k, n + 1 ≤ k → g k ≤ 0 := by
    intro k hk
    by_cases h : a ≤ k ∧ k ≤ b
    · simp only [hg, hℓ', ite_t h, hb.2 k hk h.2]
      exact mul_nonpos_of_nonneg_of_nonpos (wt_pos ht k).le (by linarith)
    · rw [hgout k h]
  have hpre_diff : ∀ K, pre t ℓ' K - pre t ℓ K = ∑ k ∈ range (K + 1), g k := by
    intro K; unfold pre; rw [← sum_sub_distrib]
    exact sum_congr rfl (fun k _ => by simp only [hg]; ring)
  refine ⟨ℓ', ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- nonneg
    intro k
    simp only [hℓ']
    split_ifs
    · exact (hI.nonneg n).trans hxm
    · exact hI.nonneg k
  · -- support
    intro k hk
    simp only [hℓ']
    rw [ite_f (by omega)]
    exact hI.supp k hk
  · -- mass
    have h1 := hpre_diff M
    have h2 := hI.mass_eq
    unfold pre at h1
    unfold mass at h2 ⊢
    linarith
  · -- prefix
    intro K hK
    have hdiff : 0 ≤ ∑ k ∈ range (K + 1), g k := by
      rcases Nat.lt_or_ge n K with hnK | hnK
      · have hsplit := sum_range_add_sum_Ico g (show K + 1 ≤ M + 1 by omega)
        have : ∑ k ∈ Ico (K + 1) (M + 1), g k ≤ 0 :=
          sum_nonpos (fun k hk => by simp at hk; exact hgnp k (by omega))
        linarith
      · exact sum_nonneg (fun k hk => by simp at hk; exact hgnn k (by omega))
    have := hpre_diff K
    linarith [hI.prefix_ge K hK]
  · -- energy
    refine le_trans (sum_le_sum (fun j _ => ?_)) hI.en_le
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply pow_le_pow_left₀ (pos_nonneg _)
    by_cases hj : a ≤ j ∧ j ≤ b
    · by_cases hj1 : a ≤ j + 1 ∧ j + 1 ≤ b
      · simp only [hℓ', ite_t hj, ite_t hj1, sub_self]
        unfold pos; rw [max_self]; exact le_max_right _ _
      · have hjb : j = b := by omega
        have hyj : ℓ j = y := by rw [hjb]; exact hb.2 b hnb le_rfl
        simp only [hℓ', ite_t hj, ite_f hj1]
        have : √m ≤ √(ℓ j) := Real.sqrt_le_sqrt (by rw [hyj]; exact hmy)
        exact max_le_max (by linarith) le_rfl
    · by_cases hj1 : a ≤ j + 1 ∧ j + 1 ≤ b
      · have hja : j + 1 = a := by omega
        have hxa : ℓ (j + 1) = x := by rw [hja]; exact ha a le_rfl han
        simp only [hℓ', ite_f hj, ite_t hj1]
        have : √(ℓ (j + 1)) ≤ √m := Real.sqrt_le_sqrt (by rw [hxa]; exact hxm)
        exact max_le_max (by linarith) le_rfl
      · simp only [hℓ', ite_f hj, ite_f hj1]; exact le_rfl
  · -- breaks
    unfold brk
    have hnS : n ∈ (range M).filter (fun j => ℓ j ≠ ℓ (j + 1)) := by
      simp only [mem_filter, mem_range]; exact ⟨hn, hv.ne⟩
    have hsub : (range M).filter (fun j => ℓ' j ≠ ℓ' (j + 1))
        ⊆ ((range M).filter (fun j => ℓ j ≠ ℓ (j + 1))).erase n := by
      intro j hjS
      simp only [mem_filter, mem_range] at hjS
      obtain ⟨hjM, hne⟩ := hjS
      simp only [mem_erase, mem_filter, mem_range]
      by_cases hj : a ≤ j ∧ j ≤ b
      · by_cases hj1 : a ≤ j + 1 ∧ j + 1 ≤ b
        · simp only [hℓ', ite_t hj, ite_t hj1] at hne; exact absurd rfl hne
        · have hjb : j = b := by omega
          refine ⟨by omega, hjM, ?_⟩
          rw [hjb, hb.2 b hnb le_rfl]
          exact fun h => hbmax (by omega) h.symm
      · by_cases hj1 : a ≤ j + 1 ∧ j + 1 ≤ b
        · have hja : j + 1 = a := by omega
          refine ⟨by omega, hjM, ?_⟩
          rw [hja, ha a le_rfl han, show j = a - 1 by omega]
          exact hamin (by omega)
        · simp only [hℓ', ite_f hj, ite_f hj1] at hne
          exact ⟨fun h => hj ⟨by omega, by omega⟩, hjM, hne⟩
    calc _ ≤ (((range M).filter (fun j => ℓ j ≠ ℓ (j + 1))).erase n).card := card_le_card hsub
      _ < _ := card_erase_lt_of_mem hnS

/-- **Pool-adjacent-violators, existence form.** There are levels satisfying the invariants
that are nonincreasing on `[0, M]`. -/
theorem pava_exists (ht : 0 < t) {r : ℕ → ℝ} (hI : Inv M t r r) :
    ∃ ℓ, Inv M t r ℓ ∧ ∀ n, n < M → ℓ (n + 1) ≤ ℓ n := by
  suffices h : ∀ k ℓ, brk M ℓ = k → Inv M t r ℓ →
      ∃ ℓ', Inv M t r ℓ' ∧ ∀ n, n < M → ℓ' (n + 1) ≤ ℓ' n from h _ r rfl hI
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro ℓ hk hIℓ
    by_cases hall : ∀ n, n < M → ℓ (n + 1) ≤ ℓ n
    · exact ⟨ℓ, hIℓ, hall⟩
    · push Not at hall
      obtain ⟨n, hn, hv⟩ := hall
      obtain ⟨ℓ', hI', hlt⟩ := pool_step ht hIℓ hn hv
      exact ih _ (hk ▸ hlt) ℓ' rfl hI'

/-! ## Schur concavity of the entropy under prefix domination -/

lemma tangent (p q : ℝ) (hp : 0 < p) (hq : 0 ≤ q) :
    negMulLog q ≤ negMulLog p + (-log p - 1) * (q - p) := by
  unfold negMulLog
  rcases hq.eq_or_lt with h0 | hqp
  · subst h0; simp; nlinarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hp hqp)
    rw [Real.log_div hp.ne' hqp.ne'] at h
    have : q * (log p - log q) ≤ q * (p / q - 1) := mul_le_mul_of_nonneg_left h hqp.le
    have e : q * (p / q - 1) = p - q := by field_simp
    rw [e] at this
    nlinarith

/-- If `p` is positive and nonincreasing on `[0, M]` and every prefix sum of `q ≥ 0` dominates
that of `p`, with equal totals, then `H(q) ≤ H(p)`. -/
theorem entropy_le_of_prefix (p q : ℕ → ℝ) (hp : ∀ n, n ≤ M → 0 < p n)
    (hanti : ∀ n, n < M → p (n + 1) ≤ p n) (hq : ∀ n, 0 ≤ q n)
    (hpre : ∀ K, K ≤ M → ∑ n ∈ range (K + 1), p n ≤ ∑ n ∈ range (K + 1), q n)
    (htot : ∑ n ∈ range (M + 1), p n = ∑ n ∈ range (M + 1), q n) :
    ∑ n ∈ range (M + 1), negMulLog (q n) ≤ ∑ n ∈ range (M + 1), negMulLog (p n) := by
  set g : ℕ → ℝ := fun n => -log (p n) - 1 with hg
  have hgmono : ∀ n, n < M → g n ≤ g (n + 1) := by
    intro n hn
    simp only [hg]
    have := Real.log_le_log (hp (n + 1) (by omega)) (hanti n hn)
    linarith
  -- Abel summation: ∑_{n ≤ K} g_n Δ_n ≤ g_K S_K
  set S : ℕ → ℝ := fun K => ∑ n ∈ range (K + 1), (q n - p n) with hS
  have hSnn : ∀ K, K ≤ M → 0 ≤ S K := by
    intro K hK; simp only [hS, sum_sub_distrib]; linarith [hpre K hK]
  have habel : ∀ K, K ≤ M → ∑ n ∈ range (K + 1), g n * (q n - p n) ≤ g K * S K := by
    intro K
    induction K with
    | zero => intro _; simp [hS]
    | succ K ih =>
      intro hK
      rw [sum_range_succ, show S (K + 1) = S K + (q (K + 1) - p (K + 1)) by
        simp only [hS]; rw [sum_range_succ]]
      have h1 := ih (by omega)
      have h2 := mul_le_mul_of_nonneg_right (hgmono K (by omega)) (hSnn K (by omega))
      nlinarith
  have hSM : S M = 0 := by simp only [hS, sum_sub_distrib]; linarith
  have hlin : ∑ n ∈ range (M + 1), g n * (q n - p n) ≤ 0 := by
    have := habel M le_rfl; rw [hSM, mul_zero] at this; exact this
  have htan : ∑ n ∈ range (M + 1), negMulLog (q n)
      ≤ ∑ n ∈ range (M + 1), (negMulLog (p n) + g n * (q n - p n)) :=
    sum_le_sum (fun n hn => by
      simp only [mem_range] at hn
      exact tangent (p n) (q n) (hp n (by omega)) (hq n))
  rw [sum_add_distrib] at htan
  linarith

/-! ## Theorem S2 -/

/-- **Theorem S2** (geometric isotonic compression). -/
theorem compression (ht : 0 < t) (c : ℕ → ℝ) (hcpos : ∀ n, n ≤ M → 0 < c n)
    (hanti : ∀ n, n < M → c (n + 1) ≤ c n) (hsupp : ∀ n, M < n → c n = 0)
    (hnorm : ∑ n ∈ range (M + 1), c n ^ 2 = 1) :
    ∃ z : ℕ → ℝ, (∀ n, 0 ≤ z n) ∧ (∀ n, M < n → z n = 0) ∧
      ∑ n ∈ range (M + 1), z n ^ 2 = 1 ∧ (∀ n, z (n + 1) ≤ t * z n) ∧
      ∑ n ∈ range (M + 1), negMulLog (z n ^ 2) ≤ ∑ n ∈ range (M + 1), negMulLog (c n ^ 2) ∧
      ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * (t * z n - z (n + 1)) ^ 2
        ≤ ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * pos (t * c n - c (n + 1)) ^ 2 := by
  classical
  set r : ℕ → ℝ := fun n => if n ≤ M then c n ^ 2 / wt t n else 0 with hr
  have hrnn : ∀ n, 0 ≤ r n := by
    intro n; simp only [hr]; split_ifs
    · exact div_nonneg (sq_nonneg _) (wt_pos ht n).le
    · exact le_rfl
  -- c_n = t^n √r_n for all n ≤ M + 1
  have hcr : ∀ n, n ≤ M + 1 → c n = t ^ n * √(r n) := by
    intro n hn
    rcases Nat.lt_or_ge M n with h | h
    · rw [hsupp n h]; simp only [hr, ite_f (by omega : ¬ n ≤ M), Real.sqrt_zero, mul_zero]
    · simp only [hr, ite_t h]
      rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq (hcpos n h).le, wt,
        Real.sqrt_sq (by positivity)]
      field_simp
  have hwr : ∀ n, n ≤ M → wt t n * r n = c n ^ 2 := by
    intro n hn; simp only [hr, ite_t hn]; field_simp [(wt_pos ht n).ne']
  have hIr : Inv M t r r := ⟨hrnn, fun n hn => by simp only [hr, show ¬ n ≤ M by omega, ↓reduceIte],
    rfl, fun _ _ => le_rfl, le_rfl⟩
  obtain ⟨ℓ, hI, hmono⟩ := pava_exists ht hIr
  refine ⟨fun n => t ^ n * √(ℓ n), fun n => by positivity, fun n hn => by
    simp only [hI.supp n hn, Real.sqrt_zero, mul_zero], ?_, ?_, ?_, ?_⟩
  · -- normalization
    have : ∑ n ∈ range (M + 1), (t ^ n * √(ℓ n)) ^ 2 = mass M t ℓ := by
      unfold mass wt
      exact sum_congr rfl (fun n _ => by rw [mul_pow, Real.sq_sqrt (hI.nonneg n)])
    rw [this, hI.mass_eq]
    unfold mass
    rw [← hnorm]
    exact sum_congr rfl (fun n hn => hwr n (by simp at hn; omega))
  · -- ratio
    intro n
    show t ^ (n + 1) * √(ℓ (n + 1)) ≤ t * (t ^ n * √(ℓ n))
    rcases Nat.lt_or_ge n M with hn | hn
    · rw [pow_succ]
      have := Real.sqrt_le_sqrt (hmono n hn)
      have ht' : 0 ≤ t ^ n * t := by positivity
      calc t ^ n * t * √(ℓ (n + 1)) ≤ t ^ n * t * √(ℓ n) := mul_le_mul_of_nonneg_left this ht'
        _ = t * (t ^ n * √(ℓ n)) := by ring
    · simp only [hI.supp (n + 1) (by omega), Real.sqrt_zero, mul_zero]
      positivity
  · -- entropy
    have hq : ∀ n, (t ^ n * √(ℓ n)) ^ 2 = wt t n * ℓ n := by
      intro n; unfold wt; rw [mul_pow, Real.sq_sqrt (hI.nonneg n)]
    simp only [hq]
    apply entropy_le_of_prefix (fun n => c n ^ 2) (fun n => wt t n * ℓ n)
    · intro n hn; exact pow_pos (hcpos n hn) 2
    · intro n hn
      exact pow_le_pow_left₀ (hcpos (n + 1) (by omega)).le (hanti n hn) 2
    · intro n; exact mul_nonneg (wt_pos ht n).le (hI.nonneg n)
    · intro K hK
      have := hI.prefix_ge K hK
      unfold pre at this
      calc ∑ n ∈ range (K + 1), c n ^ 2 = ∑ n ∈ range (K + 1), wt t n * r n :=
            sum_congr rfl (fun n hn => (hwr n (by simp at hn; omega)).symm)
        _ ≤ _ := this
    · have := hI.mass_eq
      unfold mass at this
      rw [this]
      exact sum_congr rfl (fun n hn => (hwr n (by simp at hn; omega)).symm)
  · -- energy
    have hL : ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * (t * (t ^ n * √(ℓ n))
        - t ^ (n + 1) * √(ℓ (n + 1))) ^ 2 = en M t ℓ := by
      unfold en
      refine sum_congr rfl (fun n hn => ?_)
      simp only [mem_range] at hn
      have hd : 0 ≤ √(ℓ n) - √(ℓ (n + 1)) := by
        rcases Nat.lt_or_ge n M with h | h
        · have := Real.sqrt_le_sqrt (hmono n h); linarith
        · rw [hI.supp (n + 1) (by omega), Real.sqrt_zero, sub_zero]; positivity
      rw [show pos (√(ℓ n) - √(ℓ (n + 1))) = √(ℓ n) - √(ℓ (n + 1)) from max_eq_left hd]
      ring
    have hR : ∑ n ∈ range (M + 1), ((n : ℝ) + 1) * pos (t * c n - c (n + 1)) ^ 2 = en M t r := by
      unfold en
      refine sum_congr rfl (fun n hn => ?_)
      simp only [mem_range] at hn
      rw [hcr n (by omega), hcr (n + 1) (by omega)]
      have : t * (t ^ n * √(r n)) - t ^ (n + 1) * √(r (n + 1))
          = t ^ (n + 1) * (√(r n) - √(r (n + 1))) := by ring
      rw [this]
      rw [pos_mul_left (by positivity : (0:ℝ) ≤ t ^ (n + 1))]
      ring
    rw [hL, hR]
    exact hI.en_le

end Thm1Cert
