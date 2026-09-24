import QuasianalyticLean.DenjoyCarleman.Interfaces

/-!
# Denjoy–Carleman uniqueness theorem (one variable)

If `M` is positive, log-convex and `Σ M n / M (n+1) = ∞`, and `f` is smooth near `[a, b]` with
`|f⁽ⁿ⁾| ≤ M n` on `[a, b]` and all derivatives zero at some `x₀ ∈ [a, b]`, then `f = 0` on `[a, b]`.
-/

open Set Real
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

theorem uniqueness {M : ℕ → ℝ} (hM : LogConvexSeq M) (hQ : Quasianalytic M) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hbd : ∀ n : ℕ, ∀ y ∈ Icc a b, |iteratedDeriv n f y| ≤ M n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hflat : ∀ n : ℕ, iteratedDeriv n f x₀ = 0) :
    ∀ x ∈ Icc a b, f x = 0 := by
  intro x hx
  rcases le_total x₀ x with h | h
  · exact DC4_forward hM hQ hU hab hf hbd hx₀ hflat x ⟨h, hx.2⟩
  · exact DC5_backward hM hQ hU hab hf hbd hx₀ hflat x ⟨hx.1, h⟩

end DenjoyCarleman
