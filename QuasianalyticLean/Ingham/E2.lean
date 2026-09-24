import QuasianalyticLean.DenjoyCarleman.WeightSeq

/-!
# Ingham existence, component E2: the step sequence

`a_j = 1 / ((j+1) log(e+j+1)^β)` and `M n = ∏_{j<n} 1/a_j`, so `M n / M (n+1) = a_n`. `M` is
log-convex for `β ≥ 0` (the steps decrease), and `Σ a_j < ∞` for `β > 1`.
-/

open Set Real Finset

noncomputable section

namespace Ingham

open DenjoyCarleman

/-- `1/a_j = (j+1) log(e+j+1)^β`. -/
def invStep (β : ℝ) (j : ℕ) : ℝ := ((j : ℝ) + 1) * Real.log (Real.exp 1 + ((j : ℝ) + 1)) ^ β

def stepM (β : ℝ) (n : ℕ) : ℝ := ∏ j ∈ range n, invStep β j

lemma invStep_pos (β : ℝ) (j : ℕ) : 0 < invStep β j := by
  unfold invStep
  have := log_e_add_pos (by positivity : (0:ℝ) ≤ (j:ℝ) + 1)
  positivity

lemma stepM_pos (β : ℝ) (n : ℕ) : 0 < stepM β n :=
  Finset.prod_pos fun j _ => invStep_pos β j

lemma stepM_succ (β : ℝ) (n : ℕ) : stepM β (n + 1) = stepM β n * invStep β n := by
  unfold stepM; rw [prod_range_succ]

lemma stepM_ratio (β : ℝ) (n : ℕ) : stepM β (n + 1) / stepM β n = invStep β n := by
  rw [stepM_succ, mul_div_cancel_left₀ _ (stepM_pos β n).ne']

lemma invStep_mono {β : ℝ} (hβ : 0 ≤ β) {i j : ℕ} (h : i ≤ j) : invStep β i ≤ invStep β j := by
  unfold invStep
  have h' : (i:ℝ) ≤ j := by exact_mod_cast h
  have h1 := log_e_add_pos (by positivity : (0:ℝ) ≤ (i:ℝ) + 1)
  gcongr

theorem E2_logConvex {β : ℝ} (hβ : 0 ≤ β) : LogConvexSeq (stepM β) := by
  refine ⟨stepM_pos β, fun n => ?_⟩
  rw [stepM_ratio, stepM_ratio]
  exact invStep_mono hβ (Nat.le_succ n)

theorem E2_summable {β : ℝ} (hβ : 1 < β) : Summable (fun n => stepM β n / stepM β (n + 1)) := by
  have h := (summable_nat_add_iff 1).mpr (summable_logSeries hβ)
  refine h.congr fun n => ?_
  rw [← one_div_div (stepM β (n + 1)) (stepM β n), stepM_ratio]
  unfold invStep
  push_cast
  ring_nf

/-- `stepM β n ≤ (n log(e+n)^β)ⁿ`. -/
theorem E2_le {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) :
    stepM β n ≤ ((n : ℝ) * Real.log (Real.exp 1 + n) ^ β) ^ n := by
  unfold stepM
  calc ∏ j ∈ range n, invStep β j ≤ ∏ _j ∈ range n, ((n : ℝ) * Real.log (Real.exp 1 + n) ^ β) := by
        apply Finset.prod_le_prod (fun j _ => (invStep_pos β j).le)
        intro j hj
        have hj' : (j:ℝ) + 1 ≤ n := by
          have := Finset.mem_range.mp hj; exact_mod_cast this
        unfold invStep
        have h1 := log_e_add_pos (by positivity : (0:ℝ) ≤ (j:ℝ) + 1)
        gcongr
    _ = _ := by rw [prod_const, card_range]

end Ingham
