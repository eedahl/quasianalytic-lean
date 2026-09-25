# quasianalytic-lean

Machine-checked proofs, in Lean 4 with Mathlib, of results on quasianalytic Denjoy–Carleman classes
and Gevrey regularity.

Every theorem below depends only on Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`), and the library contains no `sorry`. Run `lake env lean QuasianalyticLean/Axioms.lean`
to see this for yourself.

## Contents

| theorem | file | statement |
| --- | --- | --- |
| `Ingham.ingham_threshold` (with `ingham_uniqueness`, `ingham_existence`) | `Ingham/` | **Ingham's theorem at the quasianalytic threshold.** Let `ω_β(t) = t / log(e + t)^β` with `β > 0`. A nonzero continuous compactly supported `f : ℝ → ℂ` with `‖𝓕 f ξ‖ ≤ C e^{-τ ω_β(\|ξ\|)}` for some `τ > 0` exists if and only if `β > 1`. The uniqueness half holds for any continuous integrable `f` vanishing on an open interval. |
| `DenjoyCarleman.uniqueness` | `DenjoyCarleman/Uniqueness.lean` | **Denjoy–Carleman uniqueness.** Let `M` be positive and log-convex with `Σ M n / M (n+1) = ∞`. If `f` is smooth near `[a, b]`, satisfies `\|f⁽ⁿ⁾\| ≤ M n` on `[a, b]`, and all its derivatives vanish at one point of `[a, b]`, then `f = 0` on `[a, b]`. |
| `DenjoyCarleman.identity_theorem` | `DenjoyCarleman/Identity.lean` | **Identity theorem in several variables.** In a finite-dimensional real normed space, let `U` be open and connected and let `F` be in the class `‖DⁿF‖ ≤ C Aⁿ M n` on compact subsets of `U`, with `M` as above. If `F` vanishes on a nonempty open subset of `U`, it vanishes on `U`. |
| `DenjoyCarleman.exists_bump_of_summable` | `DenjoyCarleman/Converse.lean` | **Denjoy–Carleman converse.** If `M` is positive and log-convex with `Σ M n / M (n+1) < ∞`, there is a nonzero, smooth, compactly supported `f` with `\|f⁽ⁿ⁾\| ≤ C Aⁿ M n` (Hörmander's construction by iterated moving averages). |
| `DenjoyCarleman.weightSeq_quasianalytic`, `weightSeq_not_quasianalytic`, `weightSeq_logConvex` | `DenjoyCarleman/WeightSeq.lean` | **Log-weights at the threshold.** For `ω_β(t) = t / log(e + t)^β` and `τ > 0`, the sequence `M_k = sup_{s ≥ 1} s^k e^{-τ ω_β(s)}` is log-convex (shifted by one) and is quasianalytic if and only if `β ≤ 1` (stated for `0 < β ≤ 2`). |
| `DenjoyCarleman.omegaB_concaveOn`, `omegaB_subadd`, `omegaB_norm_subadd` | `DenjoyCarleman/OmegaSubadd.lean` | **Subadditivity of the log-weights.** For `0 ≤ β ≤ 1`, `ω_β(t) = t / log(e + t)^β` is increasing and concave on `[0, ∞)`, hence `ω_β(‖x + y‖) ≤ ω_β(‖x‖) + ω_β(‖y‖)` in any normed space. |
| `FlatSwitch.switch_in_omega_class`, `flat_small`, `no_gevrey_switch`, `no_slow_double_switch` | `FlatSwitch/` | **Switches in the log-weight classes.** The doubly exponential switch `e^{-θ exp(c y^{-γ})}` has `\|∂ⁿ\| ≤ C Aⁿ n! log(e+n)^{βn}` on `(0, δ)` when `γ ≥ 1/(β−1)`. Conversely a smooth function vanishing on `(-∞, 0]` in that class is doubly exponentially small near `0`, so no switch bounded below by `e^{-c/y^k}`, and no doubly exponential one with `γ < 1/β`, lies in the class. |
| `GevreyEdge.theoremD` | `GevreyEdge/TheoremD.lean` | **Gevrey edge factorisation.** Let `k ≥ 1`, `c, δ > 0` and `s ≥ 1`. If `b` satisfies `\|b⁽ⁿ⁾\| ≤ C Dⁿ (n!)^s` on `(0, δ)`, then `B(y) = y^{-(k+1)} e^{c/yᵏ} ∫₀^y e^{-c/uᵏ} b(u) du` satisfies such bounds of order `max(s, 1 + 1/k)` on `(0, δ)`, uniformly. |
| `symmetry_propagates` | `SymmetryPropagation.lean` | **Symmetry from a shrinking core.** Let a continuous field on `B(1) × (-1, 0)` vanish on `B(ρ(t))` at each time `t`, with `ρ > 0` but otherwise arbitrary. Assume it has the unique-continuation property (vanishing on an open set forces vanishing on the time slab above it; this is a hypothesis, not proved here). Then it vanishes everywhere. |

`NonVacuous.lean` files check that the hypotheses are satisfiable: `M n = n!` for Denjoy–Carleman,
and `b ≡ 1` for the edge factorisation.

## What is *not* proved here

- **Unique continuation.** `symmetry_propagates` takes unique continuation as a hypothesis. The PDE
  theorem that supplies it (Saut–Temam; Fabre, ESAIM COCV 1996) is not formalised.
- **Endpoint and sharpness.** For the edge factorisation, the value at `y = 0` and the sharpness of
  the index are not formalised.

## Mathematical sources

- **Denjoy–Carleman.** The proof follows Th. Bang's real-variable argument (1953), as reproduced by
  F. Nazarov, M. Sodin and A. Volberg, *Lower bounds for quasianalytic functions I*
  (arXiv:math/0208233), §2. It is recast in a discrete-chain form that avoids Bang's continuity and
  supremum arguments.
- **Ingham.** A. E. Ingham, *A note on Fourier transforms*, J. London Math. Soc. 9 (1934); the formal proof
  goes through the Denjoy–Carleman theorem in both directions rather than Ingham's original argument.
- **Converse.** L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, Thm 1.3.5.
- **Edge factorisation.** A Gevrey version of a Laplace-type factorisation lemma used in recent work
  on forced Navier–Stokes blow-up.

## How this was produced

This library was written with substantial help from an AI system (Claude, Anthropic):
- **Proof design.** It chose the proofs and designed the decomposition of each theorem into
  components with fixed statements.
- **Proofs.** It wrote the Lean proofs, using several AI subagents working in parallel.
- **Checking.** Every proof was checked by the Lean kernel, and each component was re-verified
  independently: identical statement, no `sorry`, standard axioms only.

The proofs are machine-checked, but the code has not been reviewed by a human Lean expert for style
or for fitness for Mathlib. It is not proposed for Mathlib in its current form.

## Building

The toolchain and Mathlib are pinned (`leanprover/lean4:v4.34.0-rc2`).

```sh
lake exe cache get
lake build
lake env lean QuasianalyticLean/Axioms.lean
```

## License

Apache-2.0, as Mathlib.
