# gaussian-eof

Lean 4 certificate for G. Adesso, *Optimality of Gaussian entanglement of formation*,
[arXiv:2608.01909v3](https://arxiv.org/abs/2608.01909v3).

Machine-checked proofs (Lean 4 + Mathlib) of every finite-dimensional, algebraic and
real-analytic step in the proofs of **Theorem 1** (affine extremality) and **Theorem 2**
(many-pair affine EPR inequality) in the Supplemental Material. Nothing uses `sorry`, and each
listed theorem depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). See `VERIFICATION.txt`.

Printable certificates, each with every certified statement, the verification record and the
full source:
- Theorem 1: [`Thm1Cert/certificate_theorem1.pdf`](Thm1Cert/certificate_theorem1.pdf)
- Theorem 2: [`Thm2Cert/certificate_theorem2.pdf`](Thm2Cert/certificate_theorem2.pdf)

They are regenerated with `python3 tools/make_certificate_pdf.py` (XeLaTeX).

## Checking it
```
# requires elan: https://github.com/leanprover/elan
lake exe cache get            # prebuilt Mathlib
lake build                    # ~1 min after the cache
lake env lean Certificate.lean   # axiom audit
```

## Theorem 1 (`Thm1Cert/`, [certificate](Thm1Cert/certificate_theorem1.pdf))

**Theorem S1, singular-value defect inequality** (`Defect.lean`), in the Schmidt-basis matrix
model G_t(C) = Σ_{ij} |t c_i X_ij − c_j Y_ij|²:
- `drop_lemma` (S:drop), `pointwise` (S:pointwise, cases i < j, i = j, i > j);
- `defect_inequality_tsum`: Σ_n (n+1) d_n² ≤ G_t(C), d_n = (t c_n − c_{n+1})₊.

**Theorem S2, geometric isotonic compression** (`Compression.lean`):
- `pava_exists`: pool-adjacent-violators, as an existence proof by strong induction on the
  number of level breaks (mass preserved, prefix sums raised, drop energy not increased);
- `entropy_le_of_prefix`: Schur concavity of the entropy under prefix domination;
- `compression`: z_{n+1} ≤ t z_n, H(z²) ≤ H(c²), 𝓕_t(z) ≤ Σ (n+1)(t c_n − c_{n+1})₊².

**Thermal closure** (`Closure.lean`, `Upsilon.lean`):
- `H_thermal`, `F_thermal` (S:thermalF);
- `support` (S:support): s = q minimises 𝓔(s) + λ_{q,t}(t−s)²/(1−s²) on [0, 1), via the
  monotonicity of Λ_t (S:LambdaMon);
- `Fmoments`, `Ups_eq` (S:Fmoments, S:UpsilonF), and `brk_of_upsilon`.

**Assembly** (`Assembly.lean`, `Upsilon.lean`, `Corollaries.lean`):
- `thm1_spectrum`: H(c²) + λ Σ (n+1) d_n² ≥ 𝓔(q) + λ(t−q)²/(1−q²) for every decreasing
  spectrum with finite entropy. Finite and infinite rank are both handled; the infinite case
  goes through the limit of normalised truncations;
- `theorem1`, `theorem1_upsilon`: **E(ψ) + λ_{q,t}[D_t(ψ) − d_t(q)] ≥ 𝓔(q)** for 0 < q < t ≤ 1;
- `theorem1_endpoint_state` (q = t), `fixed_entanglement`, `fixed_entanglement_endpoint`,
  `separability_criterion` (S:fixedE for 0 ≤ q ≤ t), `theorem1_limit`, `entropy_truncation`.

**Inputs for Theorem 1:**
- The Beigi–Rahimi-Keshari meta log-Sobolev theorem: Υ is minimised on thermal states.
  It is used only for diagonal states of finite rank (`BRKUpsilon`). The moment formulas
  Tr(ρ_z a†a) = n̄ and Tr(√ρ_z a √ρ_z a†) = T_z are also inputs.
- Fock-space facts:
  - E(ψ) = H(c²) and D_t = G_t + 1 − t²;
  - the matrix model X = U†aU, Y = V†aV in Schmidt bases indexed by ℕ, which exist for every
    finite-rank state;
  - the index identities from [a, a†] = 1;
  - for general infinite-rank states, the convergence G_t(C^(L)) → G_t(C) of normalised
    Schmidt truncations, after which `theorem1_limit` applies.

## Theorem 2 (`Thm2Cert/`, [certificate](Thm2Cert/certificate_theorem2.pdf))

**Lemma S5, all of it** (`MatrixLemma.lean`, `Comparison.lean`). Hypotheses: α, β, κ, w > 0,
κ² ≤ αβ, κ cosh w − w = (α+β)/2; q = e^{−w}.
- `lemmaS5_psd`, `lemmaS5_pd`, `lemmaS5_kernel`, `lemmaS5_null` and the `_complex` versions:
  M(x) ≥ 0, M(x) > 0 for x ≠ w, and ker M(w) = span{(1,1)}, over ℝ² and for z = (A, conj B).
- `lemmaS5_gamma`, `lemmaS5_gamma_complex`, `gam_pos`: M(x) ≥ γK(x) for all x, with the
  **explicit** constant γ = κ sinh w − w coth w − |α−β|/2 > 0. This replaces the compactness
  argument of the paper.

**Eqs. (S:defects), (S:Q12), (S:mainid)** (`Derivation.lean`, `Identity.lean`), in the
Schmidt-basis matrix model, for every finite Schmidt spectrum with kernel directions included:
- `defects`: ‖O₁ψ‖² + ‖O₂ψ‖² = Σ c_l c_r z†Kz.
- `Q1_from_euler`, `Q2_from_euler`: the two lines of (S:Q12), from the Euler equation, [T,O],
  and the Daleckii–Krein divided differences.
- `mainid`, `mainid_general`: Q(O₁ψ) + Q(O₂ψ) = −Σ c_l c_r z†M(x_lr)z.

**Rigidity** (`Comparison.lean`, `Derivation.lean`):
- `rigidity`, `rigidity_multi`: Σ_j [Q(O₁,ⱼψ) + Q(O₂,ⱼψ)] ≤ −γ Σ_j (‖O₁,ⱼψ‖² + ‖O₂,ⱼψ‖²).
- `stationary_rigidity`: the whole chain combined. If the second variations along all test
  vectors sum to ≥ 0, then (a_j − q_j b_j†)ψ = (q_j a_j† − b_j)ψ = 0 for every j.

**Reduction to Theorem 2** (`Reduction.lean`):
- `calib_iff`, `lam_pos`, `hyp_of_lam`: the calibration holds exactly when λ = λ_{q,t}, and
  Theorem 2's parameters satisfy the hypotheses of Lemma S5.
- `tmsv_value`, `energy_identity`, `thm2_of_minprinciple`: the equality value, and the step
  from the minimum principle to Theorem 2.

**Inputs for Theorem 2:**
- Operator facts on Fock space: the canonical commutation relations, which give [T,O], the sum
  rules (S:wccr) and the matrix model with finitely many relevant directions. Also the TMSV
  moments and the identity λD̂_t = T + λ.
- The second-variation formula Q(Y) = Re⟨Y,(T−μ−𝖥)Y⟩ (Daleckii–Krein), the Euler equation,
  and the stability inequality (S:stability).
- The vacuum/gap statement (S:gap), i.e. that the joint vacuum of the f_j, e_j is ⊗_j Ψ_{q_j}.
- The infinite-dimensional analysis: infinite Schmidt rank, Lemma S6, regularization, and
  existence of minimizers.

The inputs need operator theory on infinite-dimensional Hilbert spaces: unbounded ladder
operators, trace-class operators and von Neumann entropy. Mathlib does not yet provide these.
