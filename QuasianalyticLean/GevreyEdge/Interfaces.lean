import QuasianalyticLean.GevreyEdge.P1
import QuasianalyticLean.GevreyEdge.P2
import QuasianalyticLean.GevreyEdge.P3
import QuasianalyticLean.GevreyEdge.P4
import QuasianalyticLean.GevreyEdge.P5

/-!
# Theorem D: components

The five components, each proved in its own file with exactly the statement the assembly in
`TheoremD.lean` uses:

* `P1_comp_mul_bound` — one-variable Gevrey Faà di Bruno with a product (`P1.lean`).
* `P2_psi_hw_bounds` — derivative bounds for `ψ_w`, `h_w` from Cauchy estimates on complex discs of
  radius `κ (1+w)^{-1/k}`, uniform in `y` (`P2.lean`).
* `P3_representation` — `Bedge = Brep` on `(0, δ)` by change of variables (`P3.lean`).
* `P4_iteratedDeriv_Brep` — differentiation of `Brep` under the integral sign (`P4.lean`).
* `P5_integral_shape` — the Γ-integral bound (`P5.lean`).
-/
