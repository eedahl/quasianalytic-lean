import Mathlib

/-!
# Ingham existence, component E1: Fourier decay from derivative bounds

For smooth compactly supported `u`, `(2π|ξ|)ⁿ ‖𝓕 u ξ‖ = ‖𝓕 u⁽ⁿ⁾ ξ‖ ≤ ∫ |u⁽ⁿ⁾| ≤ L sup |u⁽ⁿ⁾|`,
with `L` the length of an interval containing the support.
-/

open Set Real MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace Ingham

lemma iteratedDeriv_ofReal_comp {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (n : ℕ) :
    iteratedDeriv n (fun x => (u x : ℂ)) = fun x => ((iteratedDeriv n u x : ℝ) : ℂ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    ext x
    have hd : HasDerivAt (iteratedDeriv n u) (deriv (iteratedDeriv n u) x) x :=
      ((hu.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _)) x).hasDerivAt
    rw [hd.ofReal_comp.deriv, iteratedDeriv_succ]

lemma iteratedDeriv_eq_zero_of_notMem {u : ℝ → ℝ} (n : ℕ) {x : ℝ} (hx : x ∉ tsupport u) :
    iteratedDeriv n u x = 0 := by
  have h : iteratedFDeriv ℝ n u x = 0 := by
    by_contra h
    exact hx (support_iteratedFDeriv_subset n h)
  rw [iteratedDeriv_eq_iteratedFDeriv, h]
  simp

theorem E1_fourier_le {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hs : HasCompactSupport u) :
    ∃ L : ℝ, 0 < L ∧ ∀ (n : ℕ) (ξ B : ℝ), (∀ x, |iteratedDeriv n u x| ≤ B) →
      (2 * π * |ξ|) ^ n * ‖𝓕 (fun x => (u x : ℂ)) ξ‖ ≤ L * B := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  refine ⟨2 * |R| + 1, by positivity, ?_⟩
  intro n ξ B hB
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set v : ℝ → ℂ := fun x => (u x : ℂ) with hv
  have hvc : ContDiff ℝ ∞ v := Complex.ofRealCLM.contDiff.comp hu
  have hint : ∀ k : ℕ, Integrable (iteratedDeriv k v) := by
    intro k
    rw [hv, iteratedDeriv_ofReal_comp hu k]
    apply Continuous.integrable_of_hasCompactSupport
    · exact Complex.continuous_ofReal.comp (hu.continuous_iteratedDeriv k (by exact_mod_cast WithTop.coe_le_coe.2 le_top))
    · refine HasCompactSupport.intro hs.isCompact (fun x hx => ?_)
      simp [iteratedDeriv_eq_zero_of_notMem k hx]
  have hF := congrFun (Real.fourier_iteratedDeriv (f := v) (N := n) (n := n)
    (hvc.of_le (by exact_mod_cast le_top)) (fun k _ => hint k) le_rfl) ξ
  have h1 : (2 * π * |ξ|) ^ n * ‖𝓕 v ξ‖ = ‖𝓕 (iteratedDeriv n v) ξ‖ := by
    rw [hF, norm_smul, norm_pow]
    congr 2
    simp [Complex.norm_real, abs_of_pos Real.pi_pos]
  rw [h1, Real.fourier_eq]
  refine (norm_integral_le_integral_norm _).trans ?_
  simp only [Circle.norm_smul]
  rw [iteratedDeriv_ofReal_comp hu n]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have hsub : ∀ x, x ∉ Icc (-|R|) |R| → |iteratedDeriv n u x| = 0 := by
    intro x hx
    rw [iteratedDeriv_eq_zero_of_notMem n (fun h => hx ?_), abs_zero]
    have := hR h
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact abs_le.1 (this.trans (le_abs_self R))
  calc ∫ x, |iteratedDeriv n u x| = ∫ x in Icc (-|R|) |R|, |iteratedDeriv n u x| := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsub]
    _ ≤ ∫ x in Icc (-|R|) |R|, B := by
        refine setIntegral_mono_on ?_ (integrableOn_const (by simp) ) measurableSet_Icc
          (fun x _ => hB x)
        exact (Continuous.integrableOn_Icc (Continuous.abs
          (hu.continuous_iteratedDeriv n (by exact_mod_cast WithTop.coe_le_coe.2 le_top))))
    _ = 2 * |R| * B := by
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Icc]
        congr 1
        rw [max_eq_left (by linarith [abs_nonneg R])]; ring
    _ ≤ (2 * |R| + 1) * B := by nlinarith

end Ingham
