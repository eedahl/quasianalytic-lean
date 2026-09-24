import QuasianalyticLean.Ingham.I1

/-!
# Ingham uniqueness, component I2: Fourier decay gives smoothness and derivative bounds

If `f` is continuous and integrable and `‖𝓕 f ξ‖ ≤ C e^{-τ ω_β(|ξ|)}`, then by Fourier inversion
`f = 𝓕⁻ (𝓕 f)`, which is smooth, and `‖f⁽ⁿ⁾(x)‖ ≤ C (2π)ⁿ ∫ |ξ|ⁿ e^{-τ ω_β(|ξ|)} dξ`.
-/

open Set Real MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace Ingham

open DenjoyCarleman

theorem I2_smooth_bound {f : ℝ → ℂ} (hc : Continuous f) (hi : Integrable f)
    {τ β C : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β)
    (hdec : ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * Real.exp (-τ * omegaB β |ξ|)) :
    ContDiff ℝ ∞ f ∧ ∀ (n : ℕ) (x : ℝ), ‖iteratedDeriv n f x‖ ≤
      C * (2 * π) ^ n * ∫ ξ : ℝ, |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) := by
  set g : ℝ → ℂ := 𝓕 f with hg_def
  have hgc : Continuous g := by
    have : ContDiff ℝ (0 : ℕ∞) g := Real.contDiff_fourier (N := 0) (fun n hn => by
      have : n = 0 := by exact_mod_cast le_zero_iff.mp hn
      subst this; simpa using hi.norm)
    exact this.continuous
  set w : ℝ → ℝ := fun ξ => Real.exp (-τ * omegaB β |ξ|) with hw
  have hint : ∀ n : ℕ, Integrable (fun ξ : ℝ => |ξ| ^ n * w ξ) := fun n => I1_integrable hτ hβ0 n
  -- reflected transform
  set h : ℝ → ℂ := fun x => g (-x) with hh
  have hhc : Continuous h := hgc.comp continuous_neg
  have hhb : ∀ ξ, ‖h ξ‖ ≤ C * w ξ := fun ξ => by
    simpa [hh, hw, abs_neg] using hdec (-ξ)
  have hmom : ∀ n : ℕ, Integrable (fun x : ℝ => x ^ n • h x) := by
    intro n
    refine Integrable.mono' ((hint n).const_mul C) ?_ ?_
    · exact ((continuous_id.pow n).smul hhc).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ξ => ?_)
      rw [norm_smul, norm_pow, Real.norm_eq_abs]
      calc |ξ| ^ n * ‖h ξ‖ ≤ |ξ| ^ n * (C * w ξ) :=
            mul_le_mul_of_nonneg_left (hhb ξ) (by positivity)
        _ = C * (|ξ| ^ n * w ξ) := by ring
  have hgi : Integrable g := by
    have := (hmom 0).comp_neg
    simpa [hh] using this
  have hf_eq : f = 𝓕 h := by
    rw [← fourierInv_eq_fourier_comp_neg]
    exact (hc.fourierInv_fourier_eq hi hgi).symm
  have hmom' : ∀ n : ℕ, (n : ℕ∞) ≤ (⊤ : ℕ∞) → Integrable (fun x : ℝ => x ^ n • h x) :=
    fun n _ => hmom n
  refine ⟨?_, ?_⟩
  · rw [hf_eq]
    have : ContDiff ℝ (⊤ : ℕ∞) (𝓕 h) := Real.contDiff_fourier (fun n _ => by
      simpa [norm_smul] using (hmom n).norm)
    exact this
  · intro n x
    rw [hf_eq, Real.iteratedDeriv_fourier hmom' le_top, Real.fourier_eq]
    refine (norm_integral_le_integral_norm _).trans ?_
    have key : ∀ ξ : ℝ, ‖𝐞 (-(inner ℝ ξ x)) • ((-2 * π * Complex.I * ξ) ^ n • h ξ)‖ ≤
        C * (2 * π) ^ n * (|ξ| ^ n * w ξ) := by
      intro ξ
      rw [Circle.norm_smul, norm_smul, norm_pow]
      have e1 : ‖(-2 * π * Complex.I * ξ)‖ = 2 * π * |ξ| := by
        simp [abs_of_pos Real.pi_pos]
      rw [e1, mul_pow]
      calc (2 * π) ^ n * |ξ| ^ n * ‖h ξ‖ ≤ (2 * π) ^ n * |ξ| ^ n * (C * w ξ) :=
            mul_le_mul_of_nonneg_left (hhb ξ) (by positivity)
        _ = C * (2 * π) ^ n * (|ξ| ^ n * w ξ) := by ring
    calc ∫ ξ, ‖𝐞 (-(inner ℝ ξ x)) • ((-2 * π * Complex.I * ξ) ^ n • h ξ)‖
        ≤ ∫ ξ, C * (2 * π) ^ n * (|ξ| ^ n * w ξ) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
            ((hint n).const_mul _) (Filter.Eventually.of_forall key)
      _ = C * (2 * π) ^ n * ∫ ξ, |ξ| ^ n * w ξ := integral_const_mul _ _

end Ingham
