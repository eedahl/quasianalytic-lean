import Mathlib

/-!
# Denjoy–Carleman uniqueness: definitions

A positive log-convex sequence `M` (ratios `M (n+1) / M n` nondecreasing) is *quasianalytic* if
`Σ M n / M (n+1) = ∞`. The uniqueness half of the Denjoy–Carleman theorem: a function whose
derivatives satisfy `|f⁽ⁿ⁾| ≤ M n` on an interval, and which is flat at a point of it, vanishes on the
interval. The proof formalised here is Bang's real-variable argument (Th. Bang, 1953; as reproduced
in Nazarov–Sodin–Volberg, arXiv:math/0208233, §2), in a discrete-chain form.
-/

open Set Real
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

/-- Positive, log-convex: `M (n+1) / M n` is nondecreasing. -/
structure LogConvexSeq (M : ℕ → ℝ) : Prop where
  pos : ∀ n, 0 < M n
  ratio_mono : ∀ n, M (n + 1) / M n ≤ M (n + 2) / M (n + 1)

/-- Quasianalyticity: `Σ M n / M (n+1)` diverges. -/
def Quasianalytic (M : ℕ → ℝ) : Prop := ¬ Summable (fun n => M n / M (n + 1))

/-- `A(q) = M q / M (q-1)`. -/
def ratio (M : ℕ → ℝ) (q : ℕ) : ℝ := M q / M (q - 1)

end DenjoyCarleman
