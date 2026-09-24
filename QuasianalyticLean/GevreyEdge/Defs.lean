import Mathlib

/-!
# The Gevrey edge factorisation: definitions

`GevreyBound σ δ f`: `f` is smooth on `(0, δ)` and `|f⁽ⁿ⁾(y)| ≤ C Dⁿ (n!)^σ` there, uniformly in `y`.
Uniform bounds on the open interval are what "Gevrey up to `y = 0`" means: bounded derivatives of
every order extend `f` smoothly to the closed interval.
-/

open Set Real
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

/-- Gevrey-type bound of order `σ` on `Ioo 0 δ`. -/
def GevreyBound (σ δ : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f (Ioo 0 δ) ∧
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ n : ℕ, ∀ y ∈ Ioo 0 δ,
      |iteratedDeriv n f y| ≤ C * D ^ n * ((n ! : ℕ) : ℝ) ^ σ

/-- The inner map of the representation: `ψ_w(y) = y (1 + yᵏ w / c)^(-1/k)`. -/
def ψ (k : ℕ) (c w y : ℝ) : ℝ := y * (1 + y ^ k * w / c) ^ (-(1 : ℝ) / k)

/-- The weight of the representation: `h_w(y) = (1 + yᵏ w / c)^(-1-1/k)`. -/
def hw (k : ℕ) (c w y : ℝ) : ℝ := (1 + y ^ k * w / c) ^ (-1 - (1 : ℝ) / k)

/-- The original edge cofactor `B(y) = y^{-(k+1)} e^{c/yᵏ} ∫₀^y e^{-c/uᵏ} b(u) du`. -/
def Bedge (k : ℕ) (c : ℝ) (b : ℝ → ℝ) (y : ℝ) : ℝ :=
  (y ^ (k + 1))⁻¹ * Real.exp (c / y ^ k) * ∫ u in (0 : ℝ)..y, Real.exp (-c / u ^ k) * b u

/-- The integrand of the representation, as a function of `y` for fixed `w`. -/
def integrand (k : ℕ) (c : ℝ) (b : ℝ → ℝ) (w y : ℝ) : ℝ := b (ψ k c w y) * hw k c w y

/-- The representation `(1/(ck)) ∫₀^∞ e^{-w} b(ψ_w(y)) h_w(y) dw`. -/
def Brep (k : ℕ) (c : ℝ) (b : ℝ → ℝ) (y : ℝ) : ℝ :=
  (c * k)⁻¹ * ∫ w in Ioi (0 : ℝ), Real.exp (-w) * integrand k c b w y

/-- The combinatorial shape of the pointwise bound: `Σ_{j ≤ n} (j!)^s (n-j)! ρ^{n-j}`. -/
def shape (s ρ : ℝ) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), ((j ! : ℕ) : ℝ) ^ s * (((n - j) ! : ℕ) : ℝ) * ρ ^ (n - j)

end GevreyEdge
