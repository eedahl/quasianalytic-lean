import QuasianalyticLean.DenjoyCarleman.DC12

open Set Real Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

lemma ratio_pos' {M : ℕ → ℝ} (hM : LogConvexSeq M) (q : ℕ) : 0 < ratio M q :=
  div_pos (hM.pos _) (hM.pos _)

lemma sum_Ioc_split (g : ℕ → ℝ) {j N : ℕ} (h : j + 1 ≤ N) :
    ∑ m ∈ Finset.Ioc j N, g m = g (j + 1) + ∑ m ∈ Finset.Ioc (j + 1) N, g m := by
  rw [← Finset.sum_Ioc_consecutive g (Nat.le_succ j) h]
  simp [Nat.Ioc_succ_singleton]

theorem DC3_chain {M : ℕ → ℝ} (hM : LogConvexSeq M) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hbd : ∀ n : ℕ, ∀ y ∈ Icc a b, |iteratedDeriv n f y| ≤ M n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hflat : ∀ n : ℕ, iteratedDeriv n f x₀ = 0)
    {L N : ℕ} (hLN : L ≤ N) :
    ∀ x : ℝ, x₀ ≤ x → x ≤ b →
      x ≤ x₀ + ∑ j ∈ Finset.Ioc L N, (2 * Real.exp 1 * ratio M j)⁻¹ →
      ∀ i : ℕ, |iteratedDeriv i f x| ≤ Real.exp (-(L : ℝ)) * Real.exp i * M i := by
  set g : ℕ → ℝ := fun j => (2 * Real.exp 1 * ratio M j)⁻¹ with hg
  have key : ∀ k j : ℕ, j + k = N → ∀ x : ℝ, x₀ ≤ x → x ≤ b →
      x ≤ x₀ + ∑ m ∈ Finset.Ioc j N, g m →
      ∀ i : ℕ, |iteratedDeriv i f x| ≤ Real.exp (-(j : ℝ)) * Real.exp i * M i := by
    intro k
    induction k with
    | zero =>
      intro j hj x hx1 _ hx3 i
      simp only [add_zero] at hj
      subst hj
      simp only [Finset.Ioc_self, Finset.sum_empty, add_zero] at hx3
      have : x = x₀ := le_antisymm hx3 hx1
      subst this
      rw [hflat, abs_zero]
      have := hM.pos i
      positivity
    | succ k ih =>
      intro j hj x hx1 hx2 hx3 i
      have hjN : j + 1 ≤ N := by omega
      have ih' := ih (j + 1) (by omega)
      rw [sum_Ioc_split g hjN] at hx3
      set S := ∑ m ∈ Finset.Ioc (j + 1) N, g m
      have hexp : Real.exp (-((j + 1 : ℕ) : ℝ)) ≤ Real.exp (-(j : ℝ)) := by
        apply Real.exp_le_exp.mpr; push_cast; linarith
      have hMi := hM.pos i
      by_cases hc : x ≤ x₀ + S
      · calc |iteratedDeriv i f x| ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) * Real.exp i * M i :=
              ih' x hx1 hx2 hc i
          _ ≤ Real.exp (-(j : ℝ)) * Real.exp i * M i := by gcongr
      · push Not at hc
        have hS0 : 0 ≤ S := Finset.sum_nonneg (fun m _ => by
          have := ratio_pos' hM m; simp only [hg]; positivity)
        set x' := x₀ + S
        have hx' : x' ∈ Icc a b := ⟨by linarith [hx₀.1], by linarith⟩
        have hbx' := ih' x' (by linarith) (by linarith) le_rfl
        have hA := ratio_pos' hM (j + 1)
        have h2 := DC2_bang_step hM hU hab hf hbd (x := x') (h := x - x')
          (β := Real.exp (-((j + 1 : ℕ) : ℝ))) (q := j + 1) (by omega) hx'
          (by linarith) (by linarith) le_rfl hbx' i
        rw [show x' + (x - x') = x by ring] at h2
        have hle : 2 * Real.exp 1 * (x - x') * ratio M (j + 1) ≤ 1 := by
          have hpos : 0 < 2 * Real.exp 1 * ratio M (j + 1) := by positivity
          have : x - x' ≤ g (j + 1) := by simp only [x']; linarith
          simp only [hg] at this
          calc 2 * Real.exp 1 * (x - x') * ratio M (j + 1)
              = (x - x') * (2 * Real.exp 1 * ratio M (j + 1)) := by ring
            _ ≤ (2 * Real.exp 1 * ratio M (j + 1))⁻¹ * (2 * Real.exp 1 * ratio M (j + 1)) := by
                gcongr
            _ = 1 := inv_mul_cancel₀ hpos.ne'
        calc |iteratedDeriv i f x|
            ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) *
                Real.exp (2 * Real.exp 1 * (x - x') * ratio M (j + 1)) * Real.exp i * M i := h2
          _ ≤ Real.exp (-((j + 1 : ℕ) : ℝ)) * Real.exp 1 * Real.exp i * M i := by
              gcongr
          _ = Real.exp (-(j : ℝ)) * Real.exp i * M i := by
              rw [← Real.exp_add]; congr 3; push_cast; ring
  intro x hx1 hx2 hx3 i
  exact key (N - L) L (by omega) x hx1 hx2 hx3 i

end DenjoyCarleman
