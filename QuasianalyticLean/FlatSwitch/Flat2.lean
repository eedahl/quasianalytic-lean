import Mathlib

/-!
# Flat functions, component F2: the doubly exponential envelope

`inf_n (A y)ⁿ log(e+n)^{βn}` is doubly exponentially small: with `n = ⌊exp(s)⌋`,
`s = (e A y)^{-1/β}`, one has `A y log(e+n)^β ≤ 1/e` for small `y`, so the infimum is at most
`e^{-n} ≤ e · exp(-exp(s))`.
-/

open Set Real
open scoped Nat

noncomputable section

namespace FlatSwitch

theorem F2_envelope {A β : ℝ} (hA : 0 < A) (hβ : 0 < β) :
    ∃ y₀ c' : ℝ, 0 < y₀ ∧ 0 < c' ∧ ∀ y ∈ Ioo 0 y₀, ∃ n : ℕ,
      (A * y) ^ n * Real.log (Real.exp 1 + n) ^ (β * n) ≤
        Real.exp 1 * Real.exp (-Real.exp (c' * y ^ (-(1 / β)))) := by
  set a : ℝ := Real.exp 1 * A * (2 : ℝ) ^ β with ha_def
  have ha : 0 < a := by positivity
  refine ⟨1 / a, a ^ (-(1 / β)), by positivity, by positivity, fun y hy => ?_⟩
  obtain ⟨hy0, hy1⟩ := hy
  have hay : 0 < a * y := by positivity
  have hay1 : a * y < 1 := by
    have := mul_lt_mul_of_pos_left hy1 ha
    rwa [mul_one_div_cancel ha.ne'] at this
  set s : ℝ := a ^ (-(1 / β)) * y ^ (-(1 / β)) with hs_def
  have hs_eq : s = (a * y) ^ (-(1 / β)) := by
    rw [hs_def, Real.mul_rpow ha.le hy0.le]
  have hs1 : 1 < s := by
    rw [hs_eq]
    exact Real.one_lt_rpow_of_pos_of_lt_one_of_neg hay hay1 (by
      have : 0 < 1 / β := by positivity
      linarith)
  have hs0 : 0 < s := by linarith
  have hsβ : s ^ β = (a * y)⁻¹ := by
    rw [hs_eq, ← Real.rpow_mul hay.le]
    rw [show -(1 / β) * β = -1 by field_simp, Real.rpow_neg_one]
  set N : ℕ := ⌊Real.exp s⌋₊ with hN
  refine ⟨N, ?_⟩
  have hNle : (N : ℝ) ≤ Real.exp s := Nat.floor_le (Real.exp_pos s).le
  have hNgt : Real.exp s - 1 < N := by
    have := Nat.lt_floor_add_one (Real.exp s); rw [← hN] at this; linarith
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  set L : ℝ := Real.log (Real.exp 1 + N) with hL
  have he1 : Real.exp 1 ≤ Real.exp s := Real.exp_le_exp.mpr hs1.le
  have hL1 : 1 ≤ L := by
    rw [hL, Real.le_log_iff_exp_le (by positivity)]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hL2 : L ≤ 2 * s := by
    rw [hL, Real.log_le_iff_le_exp (by positivity)]
    have hlog2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; norm_num at this; linarith
    calc Real.exp 1 + N ≤ 2 * Real.exp s := by linarith
      _ = Real.exp (Real.log 2 + s) := by rw [Real.exp_add, Real.exp_log (by norm_num)]
      _ ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr (by linarith)
  have hLβ : A * y * L ^ β ≤ Real.exp (-1) := by
    have h1 : L ^ β ≤ (2 * s) ^ β := Real.rpow_le_rpow hL0 hL2 hβ.le
    rw [Real.mul_rpow (by norm_num) hs0.le, hsβ] at h1
    have h2 : A * y * ((2 : ℝ) ^ β * (a * y)⁻¹) = Real.exp (-1) := by
      rw [ha_def, Real.exp_neg]
      have : (0:ℝ) < 2 ^ β := by positivity
      field_simp
    calc A * y * L ^ β ≤ A * y * ((2 : ℝ) ^ β * (a * y)⁻¹) := by gcongr
      _ = _ := h2
  have hpow : (A * y) ^ N * L ^ (β * N) = (A * y * L ^ β) ^ N := by
    rw [Real.rpow_mul hL0, Real.rpow_natCast]; ring
  rw [hpow]
  have hX0 : 0 ≤ A * y * L ^ β := by positivity
  calc (A * y * L ^ β) ^ N ≤ (Real.exp (-1)) ^ N := pow_le_pow_left₀ hX0 hLβ N
    _ = Real.exp (-(N : ℝ)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (1 - Real.exp s) := Real.exp_le_exp.mpr (by linarith)
    _ = Real.exp 1 * Real.exp (-Real.exp s) := by rw [← Real.exp_add]; ring_nf

end FlatSwitch
