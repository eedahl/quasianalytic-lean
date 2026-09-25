import Mathlib

/-!
# The doubly exponential switch

`φ(y) = exp(c y^{-γ})` and the switch `e^{-θφ}`, with its holomorphic extension to the right
half-plane. The class is `M_n = n! log(e+n)^{(1+1/γ) n}`, which lies inside the Fourier-weight
class `n! log(e+n)^{β n}` of `ω_β` whenever `1 + 1/γ ≤ β`, i.e. `γ ≥ 1/(β−1)`.
-/

open Set Real
open scoped Nat

noncomputable section

namespace FlatSwitch

/-- The switch on the real line. -/
def switchR (c γ θ : ℝ) (y : ℝ) : ℝ := Real.exp (-θ * Real.exp (c * y ^ (-γ)))

/-- Its holomorphic extension to `Re z > 0` (principal branch of `z ^ (-γ)`). -/
def switchC (c γ θ : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(θ : ℂ) * Complex.exp ((c : ℂ) * z ^ (-(γ : ℂ))))

/-- `M_n = n! · log(e+n)^{(1+1/γ) n}`. -/
def classM (γ : ℝ) (n : ℕ) : ℝ := (n ! : ℝ) * Real.log (Real.exp 1 + n) ^ ((1 + 1 / γ) * n)

end FlatSwitch
