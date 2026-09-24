import QuasianalyticLean.GevreyEdge.TheoremD

/-!
# Theorem D is not vacuous

The hypothesis `GevreyBound s δ b` is satisfiable (by `b ≡ 1`), so `theoremD` has content:
for `b ≡ 1` it gives Gevrey-`max(s, 1+1/k)` bounds for `y^{-(k+1)} e^{c/yᵏ} ∫₀^y e^{-c/uᵏ} du`.
-/

open Set Real
open scoped ContDiff Nat

namespace GevreyEdge

lemma gevreyBound_one {s δ : ℝ} (hs : 0 ≤ s) : GevreyBound s δ (fun _ => (1 : ℝ)) := by
  refine ⟨contDiffOn_const, 1, 1, zero_le_one, zero_le_one, fun n y _ => ?_⟩
  have h1 : (1 : ℝ) ≤ ((n ! : ℕ) : ℝ) ^ s :=
    Real.one_le_rpow (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero n)) hs
  rw [iteratedDeriv_const]
  split_ifs with hn
  · subst hn; simp
  · simp only [abs_zero, one_pow, one_mul]
    linarith

/-- `theoremD` applied to `b ≡ 1`. -/
example {k : ℕ} (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    GevreyBound (max 1 (1 + 1 / (k : ℝ))) δ (Bedge k c (fun _ => (1 : ℝ))) :=
  theoremD hk hc hδ le_rfl (gevreyBound_one zero_le_one)

end GevreyEdge
