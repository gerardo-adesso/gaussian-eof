/-
Certificate for the derivation of Eqs. (S:Q12) and (S:defects) of the Supplemental Material,
in the Schmidt-basis matrix model:

  * coefficient matrices: ψ ↦ C = diag(c_l); (a ψ)_lm = A_lm c_m, (b† ψ)_lm = c_l conj(B_lm),
    (a† ψ)_lm = conj(A_ml) c_m, (b ψ)_lm = c_l B_ml, with A_lr = ⟨u_l|a|u_r⟩, B_lr = ⟨v_l|b|v_r⟩;
  * test vectors O₁ψ = (a − q b†)ψ, O₂ψ = (q a† − b)ψ;
  * (S:defects): ‖O₁ψ‖² + ‖O₂ψ‖² = ∑ c_l c_r z† K z  (exact, any real c_l);
  * (S:Q12): Q(O_iψ) = Re⟨O_iψ, (T − μ − 𝖥) O_iψ⟩ equals the stated expressions, where
    (T − μ) O ψ is replaced by O 𝒢(C) + [T, O] ψ (Euler equation (S:euler)), with
    𝒢(C) = diag(c_l ln p_l), [T, a − q b†] = (qκ − α) a + (κ − qβ) b†,
    [T, q a† − b] = (qα − κ) a† + (β − qκ) b, and 𝖥 the Daleckii–Krein divided difference
    F_lr = (p_l ln p_l − p_r ln p_r)/(p_l − p_r), F_ll = 1 + ln p_l  (c_l ≥ 0, kernel entries by continuity, with 0 ln 0 = 0).
  * `stationary_rigidity`: chaining (S:Q12), (S:mainid), Lemma S5 (M ≥ γK) and (S:defects):
    if the second variations along all test vectors sum to ≥ 0, every O_{i,j}ψ vanishes.

Inputs (not derived here):
  * the matrix model itself: ψ in Schmidt form on a finite index set (support plus the finitely
    many kernel directions reached by a, a†, b, b†), with A_lr, B_lr the matrix elements;
    `O1v`, `O2v` are DEFINED as the resulting coefficient matrices;
  * the sum rules (S:wccr) (consequences of the canonical commutation relations);
  * the Euler equation (S:euler) and the commutators [T, O] (CCR), which enter by writing
    (T − μ)Oψ as O𝒢 + [T,O]ψ directly in the statements;
  * the second-variation formula Q(Y) = Re⟨Y, (T − μ − 𝖥)Y⟩ (Daleckii–Krein) and the
    stability inequality (S:stability), which enters as the hypothesis `0 ≤ ∑ Q`.
-/
import Thm2Cert.Comparison

open Real Finset ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace Thm2Cert

variable {ι : Type*} [Fintype ι]

/-! ## (S:defects) -/

/-- Coefficient matrix of `O₁ψ = (a − q b†)ψ`. -/
def O1v (q : ℝ) (c : ι → ℝ) (A B : ι → ι → ℂ) (l m : ι) : ℂ :=
  A l m * (c m : ℂ) - (q : ℂ) * (c l : ℂ) * conj (B l m)

/-- Coefficient matrix of `O₂ψ = (q a† − b)ψ`. -/
def O2v (q : ℝ) (c : ι → ℝ) (A B : ι → ι → ℂ) (l m : ι) : ℂ :=
  (q : ℂ) * (c m : ℂ) * conj (A m l) - (c l : ℂ) * B m l

lemma defect_term (q cl cr : ℝ) (A B : ℂ) :
    Complex.normSq (A * (cr : ℂ) - (q : ℂ) * (cl : ℂ) * conj B)
      + Complex.normSq ((q : ℂ) * (cl : ℂ) * conj A - (cr : ℂ) * B) = kterm q cl cr A B := by
  unfold kterm
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

/-- **Eq. (S:defects)**: `‖O₁ψ‖² + ‖O₂ψ‖² = ∑_{l,r} c_l c_r z† K(x_lr) z` (in `p`-variables). -/
theorem defects (q : ℝ) (c : ι → ℝ) (A B : ι → ι → ℂ) :
    ∑ l, ∑ m, Complex.normSq (O1v q c A B l m) + ∑ l, ∑ m, Complex.normSq (O2v q c A B l m)
      = ∑ l, ∑ r, kterm q (c l) (c r) (A l r) (B l r) := by
  rw [Finset.sum_comm (f := fun l m => Complex.normSq (O2v q c A B l m)), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  unfold O1v O2v
  exact defect_term q (c l) (c r) (A l r) (B l r)

/-- If both test vectors have zero norm, all their coefficients vanish. -/
theorem defects_zero (q : ℝ) (c : ι → ℝ) (A B : ι → ι → ℂ)
    (h0 : ∑ l, ∑ r, kterm q (c l) (c r) (A l r) (B l r) = 0) :
    ∀ l m, O1v q c A B l m = 0 ∧ O2v q c A B l m = 0 := by
  rw [← defects] at h0
  have n1 : 0 ≤ ∑ l, ∑ m, Complex.normSq (O1v q c A B l m) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  have n2 : 0 ≤ ∑ l, ∑ m, Complex.normSq (O2v q c A B l m) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _))
  have z1 : ∑ l, ∑ m, Complex.normSq (O1v q c A B l m) = 0 := by linarith
  have z2 : ∑ l, ∑ m, Complex.normSq (O2v q c A B l m) = 0 := by linarith
  intro l m
  have hz : ∀ (g : ι → ι → ℂ), ∑ l, ∑ m, Complex.normSq (g l m) = 0 → g l m = 0 := by
    intro g hg
    have hl := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg
      (fun j _ => Complex.normSq_nonneg (g i j)))).mp hg l (Finset.mem_univ l)
    have hm := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      Complex.normSq_nonneg (g l j))).mp hl m (Finset.mem_univ m)
    exact Complex.normSq_eq_zero.mp hm
  exact ⟨hz _ z1, hz _ z2⟩

/-! ## Daleckii–Krein divided difference -/

/-- `F(p, p') = (p ln p − p' ln p')/(p − p')`, `= 1 + ln p` on the diagonal. -/
def Fdk (p p' : ℝ) : ℝ := if p = p' then 1 + log p else (p * log p - p' * log p') / (p - p')

lemma Lker_symm (p p' : ℝ) : Lker p p' = Lker p' p := by
  unfold Lker
  by_cases h : p = p'
  · subst h; rfl
  · have h' : p' ≠ p := fun e => h e.symm
    simp only [h, h', ↓reduceIte]
    rw [← neg_div_neg_eq]; ring_nf

lemma Fdk_symm (p p' : ℝ) : Fdk p p' = Fdk p' p := by
  unfold Fdk
  by_cases h : p = p'
  · subst h; rfl
  · have h' : p' ≠ p := fun e => h e.symm
    simp only [h, h', ↓reduceIte]
    rw [← neg_div_neg_eq]; ring_nf

/-- `ln p_r − F_lr = −p_l L_lr` and `ln p_l − F_lr = −p_r L_lr` (multiplied by `c`). -/
lemma F_rel {cl cm : ℝ} (hl : 0 < cl) (hm : 0 < cm) :
    cm * log (cm ^ 2) = cm * Fdk (cl ^ 2) (cm ^ 2) - cl ^ 2 * Lker (cl ^ 2) (cm ^ 2) * cm ∧
    cl * log (cl ^ 2) = cl * Fdk (cl ^ 2) (cm ^ 2) - cm ^ 2 * Lker (cl ^ 2) (cm ^ 2) * cl := by
  have hl2 : 0 < cl ^ 2 := by positivity
  have hm2 : 0 < cm ^ 2 := by positivity
  unfold Fdk Lker
  by_cases h : cl ^ 2 = cm ^ 2
  · simp only [h, ↓reduceIte]
    constructor <;> field_simp <;> ring
  · simp only [h, ↓reduceIte]
    have hd : cl ^ 2 - cm ^ 2 ≠ 0 := sub_ne_zero.mpr h
    constructor <;> field_simp <;> ring

/-- `F_rel` for `c ≥ 0`: with the conventions `0 ln 0 = 0` and the continuous values
`F_lr = ln p_l` if `p_r = 0 < p_l`, the relations persist on kernel entries. -/
lemma F_rel' {cl cm : ℝ} (hl : 0 ≤ cl) (hm : 0 ≤ cm) :
    cm * log (cm ^ 2) = cm * Fdk (cl ^ 2) (cm ^ 2) - cl ^ 2 * Lker (cl ^ 2) (cm ^ 2) * cm ∧
    cl * log (cl ^ 2) = cl * Fdk (cl ^ 2) (cm ^ 2) - cm ^ 2 * Lker (cl ^ 2) (cm ^ 2) * cl := by
  rcases hl.eq_or_lt with h0 | hlp
  · subst h0
    rcases hm.eq_or_lt with h1 | hmp
    · subst h1; simp
    · have hm2 : (0:ℝ) ≠ cm ^ 2 := (by positivity : (0:ℝ) < cm ^ 2).ne
      unfold Fdk
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, hm2, ↓reduceIte,
        log_zero, zero_mul, zero_sub, mul_zero, sub_zero, zero_mul]
      have : cm ^ 2 ≠ 0 := fun e => hm2 e.symm
      refine ⟨?_, ?_⟩ <;> first | trivial | field_simp
  · rcases hm.eq_or_lt with h1 | hmp
    · subst h1
      have hl2 : cl ^ 2 ≠ 0 := (by positivity : (0:ℝ) < cl ^ 2).ne'
      unfold Fdk
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, hl2, ↓reduceIte,
        log_zero, mul_zero, sub_zero, zero_mul]
      refine ⟨?_, ?_⟩ <;> first | trivial | field_simp
    · exact F_rel hlp hmp

/-! ## (S:Q12), first line -/

lemma Q1_term (q κ α β cl cm gl gm F L : ℝ) (A B : ℂ)
    (hgm : gm = cm * F - cl ^ 2 * L * cm) (hgl : gl = cl * F - cm ^ 2 * L * cl) :
    (conj (A * (cm : ℂ) - (q : ℂ) * (cl : ℂ) * conj B)
      * ((A * (gm : ℂ) - (q : ℂ) * (gl : ℂ) * conj B
          + ((q * κ - α : ℝ) : ℂ) * A * (cm : ℂ) + ((κ - q * β : ℝ) : ℂ) * (cl : ℂ) * conj B)
        - (F : ℂ) * (A * (cm : ℂ) - (q : ℂ) * (cl : ℂ) * conj B))).re
    = (q * κ - α) * (cm ^ 2 * Complex.normSq A)
      + (q ^ 2 * β - q * κ) * (cl ^ 2 * Complex.normSq B)
      + (κ * (1 - q ^ 2) + q * (α - β)) * (cl * cm * (A * B).re)
      - cl ^ 2 * cm ^ 2 * L * Complex.normSq A
      - q ^ 2 * (cl ^ 2 * cm ^ 2 * L * Complex.normSq B)
      + q * (cl * cm * (cl ^ 2 + cm ^ 2) * L * (A * B).re) := by
  subst hgm hgl
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **Eq. (S:Q12), first line**, derived from the Euler equation and `[T, O₁]`. -/
theorem Q1_from_euler (c : ι → ℝ) (hc : ∀ l, 0 ≤ c l) (A B : ι → ι → ℂ)
    (α β κ q nA nB : ℝ)
    (hA0 : nA = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A l r))
    (hB1 : nB + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B l r)) :
    (∑ l, ∑ m, conj (O1v q c A B l m)
      * ((A l m * ((c m * log (c m ^ 2) : ℝ) : ℂ)
          - (q : ℂ) * ((c l * log (c l ^ 2) : ℝ) : ℂ) * conj (B l m)
          + ((q * κ - α : ℝ) : ℂ) * A l m * (c m : ℂ)
          + ((κ - q * β : ℝ) : ℂ) * (c l : ℂ) * conj (B l m))
        - (Fdk (c l ^ 2) (c m ^ 2) : ℂ) * O1v q c A B l m)).re
    = Q1 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B) := by
  unfold Q1
  rw [hA0, hB1]
  unfold kk sfA sfC
  simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun m _ => ?_))
  obtain ⟨h1, h2⟩ := F_rel' (hc l) (hc m)
  have hs : √(c l ^ 2 * c m ^ 2) = c l * c m := by
    rw [show c l ^ 2 * c m ^ 2 = (c l * c m) * (c l * c m) by ring]
    exact sqrt_mul_self (mul_nonneg (hc l) (hc m))
  unfold O1v
  rw [Q1_term q κ α β (c l) (c m) _ _ (Fdk (c l ^ 2) (c m ^ 2)) (Lker (c l ^ 2) (c m ^ 2))
    (A l m) (B l m) h1 h2, hs]

/-! ## (S:Q12), second line -/

lemma Q2_term (q κ α β cx cy gx gy F L : ℝ) (A B : ℂ)
    (hgx : gx = cx * F - cy ^ 2 * L * cx) (hgy : gy = cy * F - cx ^ 2 * L * cy) :
    (conj ((q : ℂ) * (cx : ℂ) * conj A - (cy : ℂ) * B)
      * (((q : ℂ) * (gx : ℂ) * conj A - (gy : ℂ) * B
          + ((q * α - κ : ℝ) : ℂ) * (cx : ℂ) * conj A + ((β - q * κ : ℝ) : ℂ) * (cy : ℂ) * B)
        - (F : ℂ) * ((q : ℂ) * (cx : ℂ) * conj A - (cy : ℂ) * B))).re
    = (q ^ 2 * α - q * κ) * (cx ^ 2 * Complex.normSq A)
      + (q * κ - β) * (cy ^ 2 * Complex.normSq B)
      + (κ * (1 - q ^ 2) - q * (α - β)) * (cx * cy * (A * B).re)
      - q ^ 2 * (cx ^ 2 * cy ^ 2 * L * Complex.normSq A)
      - cx ^ 2 * cy ^ 2 * L * Complex.normSq B
      + q * (cx * cy * (cx ^ 2 + cy ^ 2) * L * (A * B).re) := by
  subst hgx hgy
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  ring

/-- **Eq. (S:Q12), second line**, derived from the Euler equation and `[T, O₂]`. -/
theorem Q2_from_euler (c : ι → ℝ) (hc : ∀ l, 0 ≤ c l) (A B : ι → ι → ℂ)
    (α β κ q nA nB : ℝ)
    (hA1 : nA + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A l r))
    (hB0 : nB = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B l r)) :
    (∑ l, ∑ m, conj (O2v q c A B l m)
      * (((q : ℂ) * ((c m * log (c m ^ 2) : ℝ) : ℂ) * conj (A m l)
          - ((c l * log (c l ^ 2) : ℝ) : ℂ) * B m l
          + ((q * α - κ : ℝ) : ℂ) * (c m : ℂ) * conj (A m l)
          + ((β - q * κ : ℝ) : ℂ) * (c l : ℂ) * B m l)
        - (Fdk (c l ^ 2) (c m ^ 2) : ℂ) * O2v q c A B l m)).re
    = Q2 α β κ q nA nB (kk c A B) (sfA c A) (sfA c B) (sfC c A B) := by
  rw [Finset.sum_comm]
  unfold Q2
  rw [hA1, hB0]
  unfold kk sfA sfC
  simp only [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
  obtain ⟨h1, h2⟩ := F_rel' (hc y) (hc x)
  have hs : √(c x ^ 2 * c y ^ 2) = c x * c y := by
    rw [show c x ^ 2 * c y ^ 2 = (c x * c y) * (c x * c y) by ring]
    exact sqrt_mul_self (mul_nonneg (hc x) (hc y))
  rw [Lker_symm] at h1 h2
  unfold O2v
  rw [Q2_term q κ α β (c x) (c y) _ _ (Fdk (c y ^ 2) (c x ^ 2)) (Lker (c x ^ 2) (c y ^ 2))
    (A x y) (B x y) h1 h2, hs]

/-! ## Rigidity at a stable stationary point -/

/-- **Rigidity.** For `m` pairs with the hypotheses of Lemma S5, Schmidt coefficients `c ≥ 0`
and the sum rules, if the second variations (S:Q12) along all test vectors `O₁,ⱼψ, O₂,ⱼψ` —
computed from the Euler equation — sum to a nonnegative number, then every test vector
vanishes: `(a_j − q_j b_j†)ψ = 0` and `(q_j a_j† − b_j)ψ = 0` for all `j`. -/
theorem stationary_rigidity {m : ℕ} (κ α β w : Fin m → ℝ)
    (h : ∀ j, Hyp (κ j) (α j) (β j) (w j))
    (c : ι → ℝ) (hc : ∀ l, 0 ≤ c l) (A B : Fin m → ι → ι → ℂ) (nA nB : Fin m → ℝ)
    (hA0 : ∀ j, nA j = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (A j l r))
    (hA1 : ∀ j, nA j + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (A j l r))
    (hB0 : ∀ j, nB j = ∑ l, ∑ r, c r ^ 2 * Complex.normSq (B j l r))
    (hB1 : ∀ j, nB j + 1 = ∑ l, ∑ r, c l ^ 2 * Complex.normSq (B j l r))
    (hstab : 0 ≤ ∑ j,
      ((∑ l, ∑ m', conj (O1v (exp (-w j)) c (A j) (B j) l m')
        * ((A j l m' * ((c m' * log (c m' ^ 2) : ℝ) : ℂ)
            - ((exp (-w j) : ℝ) : ℂ) * ((c l * log (c l ^ 2) : ℝ) : ℂ) * conj (B j l m')
            + ((exp (-w j) * κ j - α j : ℝ) : ℂ) * A j l m' * (c m' : ℂ)
            + ((κ j - exp (-w j) * β j : ℝ) : ℂ) * (c l : ℂ) * conj (B j l m'))
          - (Fdk (c l ^ 2) (c m' ^ 2) : ℂ) * O1v (exp (-w j)) c (A j) (B j) l m')).re
      + (∑ l, ∑ m', conj (O2v (exp (-w j)) c (A j) (B j) l m')
        * ((((exp (-w j) : ℝ) : ℂ) * ((c m' * log (c m' ^ 2) : ℝ) : ℂ) * conj (A j m' l)
            - ((c l * log (c l ^ 2) : ℝ) : ℂ) * B j m' l
            + ((exp (-w j) * α j - κ j : ℝ) : ℂ) * (c m' : ℂ) * conj (A j m' l)
            + ((β j - exp (-w j) * κ j : ℝ) : ℂ) * (c l : ℂ) * B j m' l)
          - (Fdk (c l ^ 2) (c m' ^ 2) : ℂ) * O2v (exp (-w j)) c (A j) (B j) l m')).re)) :
    ∀ j l m', O1v (exp (-w j)) c (A j) (B j) l m' = 0 ∧ O2v (exp (-w j)) c (A j) (B j) l m' = 0 := by
  have hQ : ∀ j, ((∑ l, ∑ m', conj (O1v (exp (-w j)) c (A j) (B j) l m')
        * ((A j l m' * ((c m' * log (c m' ^ 2) : ℝ) : ℂ)
            - ((exp (-w j) : ℝ) : ℂ) * ((c l * log (c l ^ 2) : ℝ) : ℂ) * conj (B j l m')
            + ((exp (-w j) * κ j - α j : ℝ) : ℂ) * A j l m' * (c m' : ℂ)
            + ((κ j - exp (-w j) * β j : ℝ) : ℂ) * (c l : ℂ) * conj (B j l m'))
          - (Fdk (c l ^ 2) (c m' ^ 2) : ℂ) * O1v (exp (-w j)) c (A j) (B j) l m')).re
      + (∑ l, ∑ m', conj (O2v (exp (-w j)) c (A j) (B j) l m')
        * ((((exp (-w j) : ℝ) : ℂ) * ((c m' * log (c m' ^ 2) : ℝ) : ℂ) * conj (A j m' l)
            - ((c l * log (c l ^ 2) : ℝ) : ℂ) * B j m' l
            + ((exp (-w j) * α j - κ j : ℝ) : ℂ) * (c m' : ℂ) * conj (A j m' l)
            + ((β j - exp (-w j) * κ j : ℝ) : ℂ) * (c l : ℂ) * B j m' l)
          - (Fdk (c l ^ 2) (c m' ^ 2) : ℂ) * O2v (exp (-w j)) c (A j) (B j) l m')).re)
      = Q1 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
          (sfA c (B j)) (sfC c (A j) (B j))
        + Q2 (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (kk c (A j) (B j)) (sfA c (A j))
          (sfA c (B j)) (sfC c (A j) (B j)) := by
    intro j
    rw [Q1_from_euler c hc (A j) (B j) (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (hA0 j) (hB1 j),
      Q2_from_euler c hc (A j) (B j) (α j) (β j) (κ j) (exp (-w j)) (nA j) (nB j) (hA1 j) (hB0 j)]
  simp only [hQ] at hstab
  -- γ₀ = min_j γ_j (or 1 if there are no pairs)
  obtain ⟨γ0, hγ0, hγ⟩ : ∃ γ0 : ℝ, 0 < γ0 ∧ ∀ j, γ0 ≤ gam (κ j) (α j) (β j) (w j) := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm; exact ⟨1, one_pos, fun j => j.elim0⟩
    · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      obtain ⟨j0, -, hj0⟩ := Finset.exists_min_image Finset.univ
        (fun j => gam (κ j) (α j) (β j) (w j)) Finset.univ_nonempty
      exact ⟨_, gam_pos (h j0), fun j => hj0 j (Finset.mem_univ j)⟩
  have hz := (rigidity_multi κ α β w h γ0 hγ0 hγ c hc A B nA nB hA0 hA1 hB0 hB1).2 hstab
  intro j l m'
  exact defects_zero (exp (-w j)) c (A j) (B j) (hz j) l m'

end Thm2Cert
