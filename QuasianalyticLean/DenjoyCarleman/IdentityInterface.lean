import QuasianalyticLean.DenjoyCarleman.Uniqueness

/-!
# Denjoy–Carleman classes in several variables

`InClass M F U`: `F` is smooth on the open set `U` and, on every compact `K ⊆ U`,
`‖D^n F‖ ≤ C Aⁿ M n`. With the operator norm, restriction to a line `s ↦ F (x + s v)` has
`|g⁽ⁿ⁾| ≤ ‖Dⁿ F‖ ‖v‖ⁿ`, with no multinomial factor.
-/

open Set Real Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

/-- Denjoy–Carleman class on an open set of a normed space. -/
def InClass (M : ℕ → ℝ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : E → ℝ) (U : Set E) : Prop :=
  ContDiffOn ℝ ∞ F U ∧ ∀ K ⊆ U, IsCompact K →
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ∀ x ∈ K, ‖iteratedFDeriv ℝ n F x‖ ≤ C * A ^ n * M n

end DenjoyCarleman
