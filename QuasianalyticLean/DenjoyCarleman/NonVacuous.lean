import QuasianalyticLean.DenjoyCarleman.Identity

/-!
# The Denjoy–Carleman theorems are not vacuous

`M n = n!` is positive, log-convex and quasianalytic (`Σ n!/(n+1)! = Σ 1/(n+1) = ∞`), so the
hypotheses of `uniqueness` and `identity_theorem` are satisfiable.
-/

open Real
open scoped Nat

namespace DenjoyCarleman

lemma logConvex_factorial : LogConvexSeq (fun n => ((n ! : ℕ) : ℝ)) := by
  refine ⟨fun n => by positivity, fun n => ?_⟩
  have h1 : ((n + 1)! : ℝ) / (n ! : ℝ) = (n + 1 : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]; field_simp; push_cast; ring
  have h2 : ((n + 2)! : ℝ) / ((n + 1)! : ℝ) = (n + 2 : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 by ring, Nat.factorial_succ, Nat.cast_mul]
    field_simp; push_cast; ring
  show ((n + 1)! : ℝ) / (n ! : ℝ) ≤ ((n + 2)! : ℝ) / ((n + 1)! : ℝ)
  rw [h1, h2]; linarith

lemma quasianalytic_factorial : Quasianalytic (fun n => ((n ! : ℕ) : ℝ)) := by
  unfold Quasianalytic
  have h : (fun n : ℕ => ((n ! : ℕ) : ℝ) / (((n + 1) ! : ℕ) : ℝ)) = fun n : ℕ => 1 / ((n : ℝ) + 1) := by
    funext n
    rw [Nat.factorial_succ, Nat.cast_mul]
    field_simp
    push_cast; ring
  rw [h]
  intro hs
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 1]
  simpa [Nat.cast_add, Nat.cast_one] using hs

end DenjoyCarleman
