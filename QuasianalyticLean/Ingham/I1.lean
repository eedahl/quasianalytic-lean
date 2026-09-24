import QuasianalyticLean.DenjoyCarleman.WeightSeq

/-!
# Ingham uniqueness, component I1: moments of the weight

`∫ |ξ|ⁿ e^{-τ ω_β(|ξ|)} dξ ≤ K M_{n+2}`: split at `|ξ| = 1`; outside, write
`|ξ|ⁿ e^{-τω} = |ξ|^{n+2} e^{-τω} / ξ² ≤ M_{n+2} / ξ²`; inside, the integrand is `≤ 1 ≤ M_{n+2}/M-lower`.
-/

open Set Real MeasureTheory

noncomputable section

namespace Ingham

open DenjoyCarleman

lemma I1_continuous (β : ℝ) (n : ℕ) (τ : ℝ) :
    Continuous (fun ξ : ℝ => |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|)) := by
  unfold omegaB
  have hlog : Continuous (fun ξ : ℝ => Real.log (Real.exp 1 + |ξ|)) :=
    (continuous_const.add continuous_abs).log fun ξ => by
      have := Real.exp_pos 1; have := abs_nonneg ξ; simp only [Pi.add_apply]; linarith
  have hpow : Continuous (fun ξ : ℝ => Real.log (Real.exp 1 + |ξ|) ^ β) :=
    hlog.rpow_const fun ξ => Or.inl (log_e_add_pos (abs_nonneg ξ)).ne'
  refine (continuous_abs.pow n).mul (Real.continuous_exp.comp
    (continuous_const.mul (continuous_abs.div hpow fun ξ => ?_)))
  exact (Real.rpow_pos_of_pos (log_e_add_pos (abs_nonneg ξ)) _).ne'

lemma I1_pointwise {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (n : ℕ) (ξ : ℝ) :
    |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) ≤
      (2 * max 1 (1 / Real.exp (-τ * omegaB β 1))) * weightSeq τ β (n + 2) * (1 + ξ ^ 2)⁻¹ := by
  set m₀ := Real.exp (-τ * omegaB β 1) with hm₀
  have hm0 : 0 < m₀ := Real.exp_pos _
  have hM := weightSeq_pos hτ hβ0 (n + 2)
  have hM1 : m₀ ≤ weightSeq τ β (n + 2) := by
    have := le_weightSeq hτ hβ0 (n + 2) (le_refl (1 : ℝ)); rw [one_pow, one_mul] at this; exact this
  have hq : 0 < 1 + ξ ^ 2 := by positivity
  have ha := abs_nonneg ξ
  have hω := omegaB_nonneg β ha
  have he : Real.exp (-τ * omegaB β |ξ|) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
  have he0 := Real.exp_pos (-τ * omegaB β |ξ|)
  rcases le_or_gt 1 |ξ| with h1 | h1
  · have hb := le_weightSeq hτ hβ0 (n + 2) h1
    have hsq : |ξ| ^ 2 = ξ ^ 2 := sq_abs ξ
    have key : |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) * ξ ^ 2 ≤ weightSeq τ β (n + 2) := by
      rw [← hsq]; calc _ = |ξ| ^ (n + 2) * Real.exp (-τ * omegaB β |ξ|) := by ring
        _ ≤ _ := hb
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    have hξ2 : 1 ≤ ξ ^ 2 := by rw [← hsq]; nlinarith
    have hmax : 1 ≤ max 1 (1 / m₀) := le_max_left _ _
    have hf0 : 0 ≤ |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) := by positivity
    calc |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) * (1 + ξ ^ 2)
        ≤ |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) * (2 * ξ ^ 2) := by gcongr; linarith
      _ ≤ 2 * weightSeq τ β (n + 2) := by linarith
      _ ≤ 2 * max 1 (1 / m₀) * weightSeq τ β (n + 2) := by nlinarith
  · have hpn : |ξ| ^ n ≤ 1 := pow_le_one₀ ha h1.le
    have hf : |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) ≤ 1 := by
      calc |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    rw [← div_eq_mul_inv, le_div_iff₀ hq]
    have hξ2 : ξ ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith
    have hmax : 1 / m₀ ≤ max 1 (1 / m₀) := le_max_right _ _
    have h1M : 1 ≤ 1 / m₀ * weightSeq τ β (n + 2) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hm0]; linarith
    have hf0 : 0 ≤ |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) := by positivity
    calc |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) * (1 + ξ ^ 2) ≤ 1 * 2 := by
          apply mul_le_mul hf (by linarith) hq.le zero_le_one
      _ ≤ 2 * (1 / m₀ * weightSeq τ β (n + 2)) := by linarith
      _ ≤ 2 * max 1 (1 / m₀) * weightSeq τ β (n + 2) := by
          have := mul_le_mul_of_nonneg_right hmax hM.le; nlinarith

theorem I1_integrable {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (n : ℕ) :
    Integrable (fun ξ : ℝ => |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|)) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul
    ((2 * max 1 (1 / Real.exp (-τ * omegaB β 1))) * weightSeq τ β (n + 2)))
    (I1_continuous β n τ).aestronglyMeasurable (Filter.Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact I1_pointwise hτ hβ0 n ξ

theorem I1_integral_le {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      ∫ ξ : ℝ, |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) ≤ K * weightSeq τ β (n + 2) := by
  refine ⟨2 * max 1 (1 / Real.exp (-τ * omegaB β 1)) * π, by positivity, fun n => ?_⟩
  calc ∫ ξ : ℝ, |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|)
      ≤ ∫ ξ : ℝ, (2 * max 1 (1 / Real.exp (-τ * omegaB β 1))) * weightSeq τ β (n + 2) *
          (1 + ξ ^ 2)⁻¹ :=
        integral_mono (I1_integrable hτ hβ0 n) (integrable_inv_one_add_sq.const_mul _)
          (fun ξ => I1_pointwise hτ hβ0 n ξ)
    _ = _ := by rw [integral_const_mul, integral_univ_inv_one_add_sq]; ring

end Ingham
