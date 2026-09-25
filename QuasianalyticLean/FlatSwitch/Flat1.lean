import Mathlib

/-!
# Flat functions, component F1: Taylor at a flat point

If `f` is smooth, vanishes on `(-∞, 0]`, and `|f⁽ⁿ⁾| ≤ B` on `(0, y)`, then
`|f(y)| ≤ B yⁿ / n!`: Taylor's theorem at `0`, where every derivative vanishes.
-/

open Set Real
open scoped Nat ContDiff

noncomputable section

namespace FlatSwitch

theorem iteratedDeriv_zero_of_flat {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (h0 : ∀ t ≤ 0, f t = 0)
    (k : ℕ) : iteratedDeriv k f 0 = 0 := by
  have hc : Continuous (iteratedDeriv k f) := hf.continuous_iteratedDeriv k (by simp)
  have hIio : Iio (0:ℝ) ⊆ {x | iteratedDeriv k f x = 0} := by
    intro x hx
    have hEq : EqOn f (fun _ => (0:ℝ)) (Iio 0) := fun t ht => h0 t (le_of_lt ht)
    have h1 := iteratedDerivWithin_of_isOpen (n := k) (f := f) isOpen_Iio hx
    show iteratedDeriv k f x = 0
    rw [← h1, iteratedDerivWithin_congr hEq hx]
    simp
  have hcl : IsClosed {x | iteratedDeriv k f x = 0} := isClosed_eq hc continuous_const
  have := closure_minimal hIio hcl
  rw [closure_Iio] at this
  exact this (mem_Iic.mpr (le_refl 0))

theorem F1_taylor {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (h0 : ∀ t ≤ 0, f t = 0)
    {y B : ℝ} (hy : 0 < y) (n : ℕ) (hB : ∀ t ∈ Ioo 0 y, |iteratedDeriv n f t| ≤ B) :
    |f y| ≤ B * y ^ n / n ! := by
  cases n with
  | zero =>
    simp only [iteratedDeriv_zero] at hB
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, mul_one, div_one]
    have hcl : IsClosed {t | |f t| ≤ B} :=
      isClosed_le (continuous_abs.comp hf.continuous) continuous_const
    have := closure_minimal (fun t ht => hB t ht) hcl
    rw [closure_Ioo hy.ne] at this
    exact this ⟨hy.le, le_refl y⟩
  | succ m =>
    have hU : uIcc 0 y = Icc 0 y := uIcc_of_le hy.le
    have hUo : uIoo 0 y = Ioo 0 y := uIoo_of_le hy.le
    have hud : UniqueDiffOn ℝ (Icc 0 y) := uniqueDiffOn_Icc hy
    have hcd : ContDiffOn ℝ m f (uIcc 0 y) := (hf.of_le (by exact_mod_cast le_top)).contDiffOn
    have hdiff : DifferentiableOn ℝ (iteratedDerivWithin m f (uIcc 0 y)) (uIoo 0 y) := by
      rw [hU, hUo]
      exact ((hf.contDiffOn (s := Icc 0 y)).differentiableOn_iteratedDerivWithin
        (by exact_mod_cast WithTop.coe_lt_top _) hud).mono Ioo_subset_Icc_self
    obtain ⟨x', hx', hx'eq⟩ := taylor_mean_remainder_lagrange hy.ne hcd hdiff
    rw [hU] at hx'eq
    rw [hUo] at hx'
    have hT : taylorWithinEval f m (Icc 0 y) 0 y = 0 := by
      rw [taylor_within_apply]
      apply Finset.sum_eq_zero
      intro k _
      rw [iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le
        (by exact_mod_cast le_top)) ⟨le_refl 0, hy.le⟩, iteratedDeriv_zero_of_flat hf h0]
      simp
    rw [hT, sub_zero, iteratedDerivWithin_eq_iteratedDeriv hud (hf.contDiffAt.of_le
        (by exact_mod_cast le_top)) (Ioo_subset_Icc_self hx'), sub_zero] at hx'eq
    rw [hx'eq, abs_div, abs_mul, abs_of_pos (pow_pos hy _),
      abs_of_pos (by positivity : (0:ℝ) < ((m+1)! : ℝ))]
    gcongr
    exact hB x' hx'

end FlatSwitch
