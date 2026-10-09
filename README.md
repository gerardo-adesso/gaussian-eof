# gaussian-eof

Lean 4 certificate for G. Adesso, *Optimality of Gaussian entanglement of formation*,
[arXiv:2608.01909v3](https://arxiv.org/abs/2608.01909v3).

Machine-checked proofs (Lean 4 + Mathlib) of every finite-dimensional, algebraic and
real-analytic step in the proof of Theorem 2 (Supplemental Material, "Proof of Theorem 2").
Nothing uses `sorry`, and each listed theorem depends only on Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). See `VERIFICATION.txt`.

## Checking it
```
# requires elan: https://github.com/leanprover/elan
lake exe cache get            # prebuilt Mathlib
lake build                    # ~35 s after the cache
lake env lean Certificate.lean   # axiom audit
```

## Certified

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

## Inputs (stated, not derived)
- Operator facts on Fock space: the canonical commutation relations, which give [T,O], the sum
  rules (S:wccr) and the matrix model with finitely many relevant directions. Also the TMSV
  moments and the identity λD̂_t = T + λ.
- The second-variation formula Q(Y) = Re⟨Y,(T−μ−𝖥)Y⟩ (Daleckii–Krein), the Euler equation,
  and the stability inequality (S:stability).
- The vacuum/gap statement (S:gap), i.e. that the joint vacuum of the f_j, e_j is ⊗_j Ψ_{q_j}.
- The infinite-dimensional analysis: infinite Schmidt rank, Lemma S6, regularization, and
  existence of minimizers.

These need operator theory on infinite-dimensional Hilbert spaces: unbounded ladder operators,
trace-class operators and von Neumann entropy. Mathlib does not yet provide these.
