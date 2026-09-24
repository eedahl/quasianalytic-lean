import QuasianalyticLean.Ingham.E2

/-!
# Ingham existence, component E3: choosing the number of derivatives

For `s ≥ 0` take `n = ⌊s / (e A log(e+s)^β)⌋`. Then `n ≤ s`, so `A n log(e+n)^β / s ≤ 1/e`, and
`Aⁿ M n / sⁿ ≤ e^{-n} ≤ e · e^{-ω_β(s)/(eA)}`.
-/

open Set Real

noncomputable section

namespace Ingham

open DenjoyCarleman

theorem E3_choose {β A : ℝ} (hβ : 0 ≤ β) (hA : 0 < A) :
    ∃ C τ : ℝ, 0 < C ∧ 0 < τ ∧ ∀ s : ℝ, 0 ≤ s →
      ∃ n : ℕ, A ^ n * stepM β n ≤ C * Real.exp (-τ * omegaB β s) * s ^ n := by
  set A' := max A 1 with hA'
  have hA'1 : 1 ≤ A' := le_max_right _ _
  have hAA' : A ≤ A' := le_max_left _ _
  have he1 : 1 ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  set K := Real.exp 1 * A' with hK
  have hK1 : 1 ≤ K := by nlinarith
  have hK0 : 0 < K := by linarith
  refine ⟨Real.exp 1, 1 / K, Real.exp_pos 1, by positivity, fun s hs => ?_⟩
  set ℓ := Real.log (Real.exp 1 + s) with hℓdef
  have hℓ : 1 ≤ ℓ := one_le_log_e_add hs
  have hℓβ : 1 ≤ ℓ ^ β := Real.one_le_rpow hℓ hβ
  set w := omegaB β s with hwdef
  have hw : w = s / ℓ ^ β := rfl
  have hw0 : 0 ≤ w := omegaB_nonneg β hs
  have hws : w * ℓ ^ β = s := by rw [hw]; field_simp
  have hwle : w ≤ s := by nlinarith
  set n := ⌊w / K⌋₊ with hndef
  have hn1 : (n : ℝ) ≤ w / K := Nat.floor_le (by positivity)
  have hn2 : w / K < n + 1 := Nat.lt_floor_add_one _
  have hnK : (n : ℝ) * K ≤ w := (le_div_iff₀ hK0).mp hn1
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hwK : w / K ≤ w := div_le_self hw0 hK1
  have hns : (n : ℝ) ≤ s := by linarith
  refine ⟨n, ?_⟩
  have hlogn : Real.log (Real.exp 1 + n) ≤ ℓ := by
    have := log_e_add_pos hn0
    apply Real.log_le_log (by positivity); linarith
  have hX : (n : ℝ) * Real.log (Real.exp 1 + n) ^ β ≤ n * ℓ ^ β := by
    have := log_e_add_pos hn0
    gcongr
  have hkey : A' * (n * ℓ ^ β) ≤ s / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]
    have : A' * (n * ℓ ^ β) * Real.exp 1 = (n * K) * ℓ ^ β := by rw [hK]; ring
    rw [this, ← hws]
    exact mul_le_mul_of_nonneg_right hnK (by positivity)
  have hlog0 := log_e_add_pos hn0
  have hstep1 : A ^ n * stepM β n ≤ (s / Real.exp 1) ^ n := by
    calc A ^ n * stepM β n ≤ A' ^ n * ((n : ℝ) * Real.log (Real.exp 1 + n) ^ β) ^ n := by
          apply mul_le_mul (pow_le_pow_left₀ hA.le hAA' n) (E2_le hβ n)
            (stepM_pos β n).le (by positivity)
      _ = (A' * ((n : ℝ) * Real.log (Real.exp 1 + n) ^ β)) ^ n := (mul_pow _ _ _).symm
      _ ≤ (A' * (n * ℓ ^ β)) ^ n := by gcongr
      _ ≤ (s / Real.exp 1) ^ n := by gcongr
  have hsn : (s / Real.exp 1) ^ n = s ^ n * Real.exp (-(n : ℝ)) := by
    rw [div_pow, Real.exp_neg, ← Real.exp_nat_mul, mul_one, div_eq_mul_inv]
  have hexp : Real.exp (-(n : ℝ)) ≤ Real.exp 1 * Real.exp (-(1 / K) * w) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have : 1 / K * w = w / K := by ring
    nlinarith
  calc A ^ n * stepM β n ≤ s ^ n * Real.exp (-(n : ℝ)) := hstep1.trans hsn.le
    _ ≤ s ^ n * (Real.exp 1 * Real.exp (-(1 / K) * w)) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end Ingham
