import QuasianalyticLean.Ingham.E1
import QuasianalyticLean.Ingham.E3
import QuasianalyticLean.DenjoyCarleman.Converse

/-!
# Ingham existence above the threshold

For `β > 1` there is a nonzero smooth compactly supported `f` with
`‖𝓕 f ξ‖ ≤ C e^{-τ ω_β(|ξ|)}`: the Denjoy–Carleman converse applied to the steps
`a_j = 1/((j+1) log(e+j+1)^β)`, followed by `n`-fold integration by parts with `n ≈ ω_β(|ξ|)`.
-/

open Set Real MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace Ingham

open DenjoyCarleman

theorem ingham_existence {β : ℝ} (hβ : 1 < β) :
    ∃ f : ℝ → ℂ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f ≠ 0 ∧
      ∃ C τ : ℝ, 0 < C ∧ 0 < τ ∧ ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * Real.exp (-τ * omegaB β |ξ|) := by
  obtain ⟨u, hu, hs, hne, C₀, A₀, hC₀, hA₀, hb⟩ :=
    exists_bump_of_summable (E2_logConvex (by linarith)) (E2_summable hβ)
  obtain ⟨L, hL, hF⟩ := E1_fourier_le hu hs
  obtain ⟨C, τ, hC, hτ, hn⟩ := E3_choose (β := β) (A := A₀ / (2 * π)) (by linarith) (by positivity)
  refine ⟨fun x => (u x : ℂ), ?_, ?_, ?_, L * C₀ * C, τ, by positivity, hτ, fun ξ => ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp hu
  · exact hs.comp_left Complex.ofReal_zero
  · intro h; apply hne; funext x; simpa using congrFun h x
  obtain ⟨n, hn⟩ := hn |ξ| (abs_nonneg ξ)
  have h1 := hF n ξ _ (hb n)
  set F := ‖𝓕 (fun x => (u x : ℂ)) ξ‖ with hFdef
  have hE : 0 < Real.exp (-τ * omegaB β |ξ|) := Real.exp_pos _
  rcases (abs_nonneg ξ).eq_or_lt with h0 | hpos
  · -- ξ = 0: `n = 0` is forced unless the right side vanishes; use the `n = 0` bound directly
    have h0' := hF 0 ξ _ (hb 0)
    have hn0 : A₀ ^ n * stepM β n ≤ 0 ∨ n = 0 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · exact Or.inr h
      · left
        have := hn; rw [← h0, zero_pow h.ne', mul_zero] at this
        calc A₀ ^ n * stepM β n = (2 * π) ^ n * ((A₀ / (2 * π)) ^ n * stepM β n) := by
              rw [div_pow]; field_simp
          _ ≤ (2 * π) ^ n * 0 := by gcongr
          _ = 0 := mul_zero _
    have hM0 : stepM β 0 = 1 := by simp [stepM]
    rcases hn0 with h | h
    · have hpos' : 0 < A₀ ^ n * stepM β n :=
        mul_pos (pow_pos hA₀ _) ((E2_logConvex (β := β) (by linarith)).pos n)
      linarith
    · subst h
      simp only [pow_zero, one_mul, mul_one, hM0] at h0' hn
      calc F ≤ L * (C₀ * 1) := by simpa using h0'
        _ = L * C₀ * 1 := by ring
        _ ≤ L * C₀ * (C * Real.exp (-τ * omegaB β |ξ|)) := by gcongr
        _ = L * C₀ * C * Real.exp (-τ * omegaB β |ξ|) := by ring
  · have hsn : 0 < (2 * π * |ξ|) ^ n := by positivity
    have key : (2 * π * |ξ|) ^ n * F ≤ (2 * π * |ξ|) ^ n * (L * C₀ * C * Real.exp (-τ * omegaB β |ξ|)) := by
      calc (2 * π * |ξ|) ^ n * F ≤ L * (C₀ * A₀ ^ n * stepM β n) := h1
        _ = L * C₀ * (2 * π) ^ n * ((A₀ / (2 * π)) ^ n * stepM β n) := by
            rw [div_pow]; field_simp
        _ ≤ L * C₀ * (2 * π) ^ n * (C * Real.exp (-τ * omegaB β |ξ|) * |ξ| ^ n) := by gcongr
        _ = (2 * π * |ξ|) ^ n * (L * C₀ * C * Real.exp (-τ * omegaB β |ξ|)) := by ring
    exact le_of_mul_le_mul_left key hsn

end Ingham
