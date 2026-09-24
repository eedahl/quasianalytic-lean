import Mathlib

/-!
# Ingham uniqueness, component I4: derivatives of real and imaginary parts
-/

open scoped ContDiff

noncomputable section

namespace Ingham

theorem I4_re_im {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y => (f y).re) x = (iteratedDeriv n f x).re ∧
      iteratedDeriv n (fun y => (f y).im) x = (iteratedDeriv n f x).im := by
  have hre : (fun y => (f y).re) = Complex.reCLM ∘ f := rfl
  have him : (fun y => (f y).im) = Complex.imCLM ∘ f := rfl
  rw [hre, him]
  constructor
  · rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
      Complex.reCLM.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)]
    rfl
  · rw [iteratedDeriv_eq_iteratedFDeriv, iteratedDeriv_eq_iteratedFDeriv,
      Complex.imCLM.iteratedFDeriv_comp_left hf.contDiffAt (by exact_mod_cast le_top)]
    rfl

theorem I4_contDiff_re_im {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun y => (f y).re) ∧ ContDiff ℝ ∞ (fun y => (f y).im) := by
  exact ⟨Complex.reCLM.contDiff.comp hf, Complex.imCLM.contDiff.comp hf⟩

end Ingham
