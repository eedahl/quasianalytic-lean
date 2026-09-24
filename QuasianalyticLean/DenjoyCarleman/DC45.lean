import QuasianalyticLean.DenjoyCarleman.DC3

/-!
# Denjoy–Carleman uniqueness: proofs of DC4 (forward) and DC5 (backward, by reflection)
-/

open Set Real Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

/-- Reindexing of the chain sum: `Σ_{L<j≤N} (2e A(j))⁻¹ = (2e)⁻¹ (Σ_{k<N} M k / M (k+1) - Σ_{k<L} …)`. -/
lemma chain_sum_eq (M : ℕ → ℝ) {L N : ℕ} (hLN : L ≤ N) :
    ∑ j ∈ Finset.Ioc L N, (2 * Real.exp 1 * ratio M j)⁻¹ =
      (2 * Real.exp 1)⁻¹ * (∑ k ∈ Finset.range N, M k / M (k + 1) -
        ∑ k ∈ Finset.range L, M k / M (k + 1)) := by
  induction N, hLN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, ih, Finset.sum_range_succ]
    simp only [ratio, Nat.add_sub_cancel]
    rw [mul_inv (2 * Real.exp 1), inv_div]
    ring

/-- For each `L`, the chain reaches any prescribed length. -/
lemma exists_chain_long {M : ℕ → ℝ} (hM : LogConvexSeq M) (hQ : Quasianalytic M) (L : ℕ)
    (c : ℝ) : ∃ N, L ≤ N ∧ c ≤ ∑ j ∈ Finset.Ioc L N, (2 * Real.exp 1 * ratio M j)⁻¹ := by
  have hnn : ∀ n, 0 ≤ M n / M (n + 1) := fun n => div_nonneg (hM.pos n).le (hM.pos _).le
  have ht := (not_summable_iff_tendsto_nat_atTop_of_nonneg hnn).1 hQ
  have ht2 : Tendsto (fun N : ℕ => (2 * Real.exp 1)⁻¹ * (∑ k ∈ Finset.range N, M k / M (k + 1) -
      ∑ k ∈ Finset.range L, M k / M (k + 1))) atTop atTop :=
    (tendsto_atTop_add_const_right _ _ ht).const_mul_atTop (by positivity)
  obtain ⟨N, hN⟩ := ((ht2.eventually_ge_atTop c).and (eventually_ge_atTop L)).exists
  exact ⟨N, hN.2, by rw [chain_sum_eq M hN.2]; exact hN.1⟩

theorem DC4_forward {M : ℕ → ℝ} (hM : LogConvexSeq M) (hQ : Quasianalytic M) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hbd : ∀ n : ℕ, ∀ y ∈ Icc a b, |iteratedDeriv n f y| ≤ M n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hflat : ∀ n : ℕ, iteratedDeriv n f x₀ = 0) :
    ∀ x ∈ Icc x₀ b, f x = 0 := by
  intro x hx
  have hL : ∀ L : ℕ, |f x| ≤ Real.exp (-(L : ℝ)) * M 0 := by
    intro L
    obtain ⟨N, hLN, hN⟩ := exists_chain_long hM hQ L (x - x₀)
    have := DC3_chain hM hU hab hf hbd hx₀ hflat hLN x hx.1 hx.2 (by linarith) 0
    simpa [iteratedDeriv_zero] using this
  have hlim : Tendsto (fun L : ℕ => Real.exp (-(L : ℝ)) * M 0) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).mul_const (M 0)
    simpa [Function.comp_def] using this
  have h0 : |f x| ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall hL)
  exact abs_nonpos_iff.1 h0

theorem DC5_backward {M : ℕ → ℝ} (hM : LogConvexSeq M) (hQ : Quasianalytic M) {f : ℝ → ℝ}
    {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hbd : ∀ n : ℕ, ∀ y ∈ Icc a b, |iteratedDeriv n f y| ≤ M n)
    {x₀ : ℝ} (hx₀ : x₀ ∈ Icc a b) (hflat : ∀ n : ℕ, iteratedDeriv n f x₀ = 0) :
    ∀ x ∈ Icc a x₀, f x = 0 := by
  set g : ℝ → ℝ := fun y => f (-y) with hg
  have hU' : IsOpen (Neg.neg ⁻¹' U : Set ℝ) := hU.preimage continuous_neg
  have hmem : ∀ y ∈ Icc (-b) (-a), -y ∈ Icc a b := fun y hy =>
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hab' : Icc (-b) (-a) ⊆ Neg.neg ⁻¹' U := fun y hy => hab (hmem y hy)
  have hf' : ContDiffOn ℝ ∞ g (Neg.neg ⁻¹' U) :=
    hf.comp contDiff_neg.contDiffOn (fun y hy => hy)
  have hbd' : ∀ n : ℕ, ∀ y ∈ Icc (-b) (-a), |iteratedDeriv n g y| ≤ M n := by
    intro n y hy
    rw [hg, iteratedDeriv_comp_neg, smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul]
    exact hbd n _ (hmem y hy)
  have hx₀' : -x₀ ∈ Icc (-b) (-a) := ⟨by linarith [hx₀.2], by linarith [hx₀.1]⟩
  have hflat' : ∀ n : ℕ, iteratedDeriv n g (-x₀) = 0 := by
    intro n
    rw [hg, iteratedDeriv_comp_neg, neg_neg, hflat, smul_zero]
  intro x hx
  have := DC4_forward hM hQ hU' hab' hf' hbd' hx₀' hflat' (-x)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  simpa [hg] using this

end DenjoyCarleman
