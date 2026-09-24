import QuasianalyticLean.DenjoyCarleman.WeightSeq

/-!
# Ingham uniqueness, component I3: the rescaled, shifted weight sequence

`N n = K Aⁿ M_{n+2}` is log-convex and quasianalytic when `β ≤ 1`: the ratios are those of
`k ↦ M_{k+1}` shifted by one and divided by `A`.
-/

open Set Real

noncomputable section

namespace Ingham

open DenjoyCarleman

theorem I3_shifted {τ β K A : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (hβ : β ≤ 1) (hK : 0 < K)
    (hA : 0 < A) :
    LogConvexSeq (fun n => K * A ^ n * weightSeq τ β (n + 2)) ∧
      Quasianalytic (fun n => K * A ^ n * weightSeq τ β (n + 2)) := by
  set M := weightSeq τ β with hM
  have hpos : ∀ k, 0 < M k := fun k => weightSeq_pos hτ hβ0 k
  have hL := weightSeq_logConvex hτ hβ0 (by linarith : β ≤ 2)
  have hQ := weightSeq_quasianalytic hτ hβ0 hβ
  have key : ∀ n, K * A ^ (n + 1) * M (n + 1 + 2) / (K * A ^ n * M (n + 2)) =
      A * (M (n + 3) / M (n + 2)) := by
    intro n
    have := hpos (n + 2)
    field_simp
    ring_nf
  have key' : ∀ n, K * A ^ n * M (n + 2) / (K * A ^ (n + 1) * M (n + 1 + 2)) =
      A⁻¹ * (M (n + 1 + 1) / M (n + 1 + 1 + 1)) := by
    intro n
    have := hpos (n + 3)
    field_simp
    ring_nf
  refine ⟨⟨fun n => by have := hpos (n + 2); positivity, fun n => ?_⟩, ?_⟩
  · have h1 := key n
    have h2 := key (n + 1)
    rw [h1, h2]
    have := hL.ratio_mono (n + 1)
    exact mul_le_mul_of_nonneg_left (by convert this using 2) hA.le
  · intro hs
    apply hQ
    simp_rw [key'] at hs
    have hs2 := hs.mul_left A
    simp_rw [← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul] at hs2
    exact (summable_nat_add_iff 1).mp hs2

end Ingham
