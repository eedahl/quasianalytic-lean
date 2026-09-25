import QuasianalyticLean.FlatSwitch.S1
import QuasianalyticLean.FlatSwitch.S2
import QuasianalyticLean.FlatSwitch.S3

/-!
# The doubly exponential switch lies in the `ω_β` class when `γ ≥ 1/(β−1)`

`e^{-θ exp(c y^{-γ})}` has `|∂ⁿ| ≤ C Aⁿ n! log(e+n)^{(1+1/γ)n}` on `(0, δ)`, `δ ≤ 1`, uniformly:
Cauchy on `D(y, κ y^{1+γ})` (S1, S2), then the supremum over `y` (S3). For `1 + 1/γ ≤ β` this
is the Denjoy–Carleman class `n! log(e+n)^{βn}` of the Fourier weight `ω_β`, which is
non-quasianalytic for `β > 1`: a flat switch that the class admits, where no `e^{-c/y^k}` does.
-/

open Set Real
open scoped Nat

noncomputable section

namespace FlatSwitch

theorem switch_in_class {c γ θ δ : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hθ : 0 < θ) (hδ1 : δ ≤ 1) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ∀ y ∈ Ioo 0 δ,
      |iteratedDeriv n (switchR c γ θ) y| ≤ C * A ^ n * classM γ n := by
  obtain ⟨κ, hκ, hκ2, hS1⟩ := S1_disc hc hγ hθ
  obtain ⟨C, A, hC, hA, hS3⟩ := S3_sup hc hγ hθ hκ
  refine ⟨C, A, hC, hA, fun n y hy => ?_⟩
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2.le.trans hδ1
  have hr : 0 < κ * y ^ (1 + γ) := mul_pos hκ (Real.rpow_pos_of_pos hy0 _)
  have hyγ : y ^ (1 + γ) ≤ y := by
    calc y ^ (1 + γ) ≤ y ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hy0 hy1 (by linarith)
      _ = y := Real.rpow_one y
  have hry : κ * y ^ (1 + γ) < y := by
    calc κ * y ^ (1 + γ) ≤ (1 / 2) * y := by gcongr
      _ < y := by linarith
  calc |iteratedDeriv n (switchR c γ θ) y|
      ≤ n ! * Real.exp (-(θ / 2) * Real.exp (c * y ^ (-γ))) / (κ * y ^ (1 + γ)) ^ n :=
        S2_cauchy hy0 hr hry (hS1 y hy0 hy1) n
    _ ≤ C * A ^ n * classM γ n := hS3 n y hy0 hy1

/-- In the `ω_β` class: `|∂ⁿ| ≤ C Aⁿ n! log(e+n)^{βn}` when `1 + 1/γ ≤ β`. -/
theorem switch_in_omega_class {c γ θ δ β : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hθ : 0 < θ)
    (hδ1 : δ ≤ 1) (hβ : 1 + 1 / γ ≤ β) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ∀ y ∈ Ioo 0 δ,
      |iteratedDeriv n (switchR c γ θ) y| ≤
        C * A ^ n * ((n ! : ℝ) * Real.log (Real.exp 1 + n) ^ (β * n)) := by
  obtain ⟨C, A, hC, hA, h⟩ := switch_in_class hc hγ hθ hδ1
  refine ⟨C, A, hC, hA, fun n y hy => (h n y hy).trans ?_⟩
  unfold classM
  have hL : 1 ≤ Real.log (Real.exp 1 + n) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  gcongr

end FlatSwitch
