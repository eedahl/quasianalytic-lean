import QuasianalyticLean.Ingham.Uniqueness
import QuasianalyticLean.Ingham.Existence

/-!
# The Ingham threshold for `ω_β`

A nonzero continuous compactly supported `f` with `‖𝓕 f ξ‖ ≤ C e^{-τ ω_β(|ξ|)}` for some `τ > 0`
exists if and only if `β > 1`, where `ω_β(t) = t / log(e + t)^β`. This is the uncertainty principle
at the quasianalytic threshold: `∫ ω_β(t) / t² dt` diverges exactly when `β ≤ 1`.
-/

open Set Real MeasureTheory Metric
open scoped FourierTransform ContDiff

noncomputable section

namespace Ingham

open DenjoyCarleman

theorem ingham_threshold {β : ℝ} (hβ0 : 0 < β) :
    (∃ f : ℝ → ℂ, Continuous f ∧ HasCompactSupport f ∧ f ≠ 0 ∧
      ∃ C τ : ℝ, 0 < τ ∧ ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * Real.exp (-τ * omegaB β |ξ|)) ↔ 1 < β := by
  constructor
  · rintro ⟨f, hc, hs, hne, C, τ, hτ, hdec⟩
    by_contra hβ
    push_neg at hβ
    obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
    have hzero : ∀ x ∈ Ioo (|R|) (|R| + 1), f x = 0 := by
      intro x hx
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have := hR hmem
      rw [mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_abs_self R, le_abs_self x, hx.1]
    exact hne (ingham_uniqueness hc (hc.integrable_of_hasCompactSupport hs) hτ hβ0 hβ hdec
      (by linarith) hzero)
  · intro hβ
    obtain ⟨f, hf, hs, hne, C, τ, _, hτ, hdec⟩ := ingham_existence hβ
    exact ⟨f, hf.continuous, hs, hne, C, τ, hτ, hdec⟩

end Ingham
