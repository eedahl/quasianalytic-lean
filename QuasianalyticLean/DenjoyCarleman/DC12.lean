import QuasianalyticLean.DenjoyCarleman.Defs

open Set Real Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

lemma ratio_le {M : ℕ → ℝ} (hM : LogConvexSeq M) {m q : ℕ} (hmq : m + 1 ≤ q) :
    M (m + 1) / M m ≤ ratio M q := by
  have hmono : Monotone (fun n => M (n + 1) / M n) :=
    monotone_nat_of_le_succ (fun n => hM.ratio_mono n)
  have h1 := hmono (show m ≤ q - 1 by omega)
  have h2 : q - 1 + 1 = q := by omega
  simp only [h2] at h1
  exact h1

lemma ratio_pos {M : ℕ → ℝ} (hM : LogConvexSeq M) (q : ℕ) : 0 < ratio M q :=
  div_pos (hM.pos _) (hM.pos _)

/-- **DC1.** -/
theorem DC1_ratio_pow {M : ℕ → ℝ} (hM : LogConvexSeq M) {i l q : ℕ} (hq : 1 ≤ q)
    (hil : i + l ≤ q) : M (i + l) ≤ M i * ratio M q ^ l := by
  induction l with
  | zero => simp
  | succ l ih =>
    have ih := ih (by omega)
    have hr := ratio_le hM (m := i + l) (q := q) (by omega)
    have hpos := hM.pos (i + l)
    have hrpos : 0 ≤ M (i + l + 1) / M (i + l) := div_nonneg (hM.pos _).le hpos.le
    calc M (i + (l + 1)) = M (i + l) * (M (i + l + 1) / M (i + l)) := by
          rw [mul_div_cancel₀ _ hpos.ne']; rfl
      _ ≤ (M i * ratio M q ^ l) * ratio M q := mul_le_mul ih hr hrpos
          (mul_nonneg (hM.pos i).le (pow_nonneg (ratio_pos hM q).le _))
      _ = M i * ratio M q ^ (l + 1) := by ring

lemma smooth_iter {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) :
    ∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv k f) U := by
  intro k
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv_of_isOpen hU (by simp)

lemma iter_iter (f : ℝ → ℝ) (m k : ℕ) :
    iteratedDeriv m (iteratedDeriv k f) = iteratedDeriv (m + k) f := by
  rw [iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate, iteratedDeriv_eq_iterate,
    Function.iterate_add_apply]


/-- **DC2.** Bang's step. -/
theorem DC2_bang_step {M : ℕ → ℝ} (hM : LogConvexSeq M) {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} (hab : Icc a b ⊆ U) (hf : ContDiffOn ℝ ∞ f U)
    (hbd : ∀ n : ℕ, ∀ y ∈ Icc a b, |iteratedDeriv n f y| ≤ M n)
    {x h β : ℝ} {q : ℕ} (hq : 1 ≤ q) (hx : x ∈ Icc a b) (hh : 0 ≤ h) (hxh : x + h ≤ b)
    (hβ : Real.exp (-(q : ℝ)) ≤ β)
    (hbx : ∀ i : ℕ, |iteratedDeriv i f x| ≤ β * Real.exp i * M i) :
    ∀ i : ℕ, |iteratedDeriv i f (x + h)| ≤
      β * Real.exp (2 * Real.exp 1 * h * ratio M q) * Real.exp i * M i := by
  intro i
  set A := ratio M q with hA
  have hApos : 0 < A := ratio_pos hM q
  set t := Real.exp 1 * A * h with ht
  have ht0 : 0 ≤ t := by positivity
  have hβpos : 0 < β := lt_of_lt_of_le (Real.exp_pos _) hβ
  have hMi := hM.pos i
  set P := β * Real.exp i * M i with hP
  have hPpos : 0 < P := by positivity
  have hsub : Icc x (x + h) ⊆ Icc a b := Icc_subset_Icc hx.1 hxh
  have hxhmem : x + h ∈ Icc a b := hsub (right_mem_Icc.2 (by linarith))
  have hgoal : β * Real.exp (2 * Real.exp 1 * h * ratio M q) * Real.exp i * M i
      = P * Real.exp t * Real.exp t := by
    rw [show 2 * Real.exp 1 * h * ratio M q = t + t by simp only [ht, hA]; ring, Real.exp_add]
    ring
  rw [hgoal]
  have het : 1 ≤ Real.exp t := Real.one_le_exp ht0
  rcases le_or_gt q i with hiq | hiq
  · -- large i
    have h1 : 1 ≤ β * Real.exp i := by
      calc (1 : ℝ) ≤ Real.exp (-(q : ℝ)) * Real.exp i := by
            rw [← Real.exp_add]; apply Real.one_le_exp
            have : (q : ℝ) ≤ i := by exact_mod_cast hiq
            linarith
        _ ≤ β * Real.exp i := by gcongr
    calc |iteratedDeriv i f (x + h)| ≤ M i := hbd i _ hxhmem
      _ ≤ P := by rw [hP]; nlinarith
      _ ≤ P * Real.exp t * Real.exp t := by
        have : 1 ≤ Real.exp t * Real.exp t := one_le_mul_of_one_le_of_one_le het het
        nlinarith
  · -- small i : Taylor
    obtain ⟨n, rfl⟩ : ∃ n, q = i + n + 1 := ⟨q - i - 1, by omega⟩
    rcases hh.eq_or_lt with hh0 | hhpos
    · subst hh0
      simp only [add_zero] at *
      have := hbx i
      rw [ht, mul_zero, Real.exp_zero]; simpa using this
    set g := iteratedDeriv i f with hg
    have hsm := smooth_iter hU hf i
    have hcdAt : ∀ y ∈ Icc x (x + h), ∀ m : ℕ, ContDiffAt ℝ m g y := fun y hy m =>
      (hsm.contDiffAt (hU.mem_nhds (hab (hsub hy)))).of_le (by exact_mod_cast (le_top : (m : ℕ∞) ≤ ⊤))
    have hderivs : ∀ y ∈ Icc x (x + h), ∀ k : ℕ,
        iteratedDerivWithin k g (Icc x (x + h)) y = iteratedDeriv (k + i) f y := by
      intro y hy k
      rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc (by linarith)) (hcdAt y hy k) hy,
        hg, iter_iter]
    have hcd : ContDiffOn ℝ (n + 1 : ℕ) g (Icc x (x + h)) :=
      (hsm.mono (hsub.trans hab)).of_le (by exact_mod_cast (le_top : ((n + 1 : ℕ) : ℕ∞) ≤ ⊤))
    have hrem := taylor_mean_remainder_bound (f := g) (n := n) (C := M (i + n + 1)) (x := x + h)
      (a := x) (b := x + h)
      (by linarith) (by exact_mod_cast hcd) (right_mem_Icc.2 (by linarith)) (fun y hy => by
        rw [hderivs y hy, show n + 1 + i = i + n + 1 by omega, Real.norm_eq_abs]
        exact hbd _ y (hsub hy))
    rw [Real.norm_eq_abs, show x + h - x = h by ring] at hrem
    rw [taylor_within_apply, show x + h - x = h by ring] at hrem
    simp only [smul_eq_mul] at hrem
    -- bound Taylor polynomial
    have hT : |∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) *
        iteratedDerivWithin k g (Icc x (x + h)) x| ≤ P * Real.exp t := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ k ∈ Finset.range (n + 1), |((k ! : ℝ)⁻¹ * h ^ k) *
            iteratedDerivWithin k g (Icc x (x + h)) x|
          ≤ ∑ k ∈ Finset.range (n + 1), P * (t ^ k / k !) := by
            apply Finset.sum_le_sum
            intro k hk
            rw [Finset.mem_range] at hk
            rw [hderivs x (left_mem_Icc.2 (by linarith)) k, abs_mul, abs_of_nonneg (by positivity), add_comm k i]
            have hD := hbx (k + i)
            have hDC := DC1_ratio_pow hM (i := i) (l := k) (q := i + n + 1) hq (by omega)
            have hexp : Real.exp ((k + i : ℕ) : ℝ) = Real.exp i * Real.exp 1 ^ k := by
              rw [Real.exp_one_pow, ← Real.exp_add]; push_cast; ring_nf
            rw [hexp, add_comm k i] at hD
            calc (k ! : ℝ)⁻¹ * h ^ k * |iteratedDeriv (i + k) f x|
                ≤ (k ! : ℝ)⁻¹ * h ^ k * (β * (Real.exp i * Real.exp 1 ^ k) * M (i + k)) := by
                  gcongr
              _ ≤ (k ! : ℝ)⁻¹ * h ^ k * (β * (Real.exp i * Real.exp 1 ^ k) * (M i * A ^ k)) := by
                  gcongr
              _ = P * (t ^ k / k !) := by
                  rw [hP, ht]; field_simp; ring
        _ = P * ∑ k ∈ Finset.range (n + 1), t ^ k / k ! := by rw [Finset.mul_sum]
        _ ≤ P * Real.exp t := by gcongr; exact Real.sum_le_exp_of_nonneg ht0 _
    -- bound remainder
    have hR : M (i + n + 1) * h ^ (n + 1) / n ! ≤ P * (t * Real.exp t) := by
      have hDC := DC1_ratio_pow hM (i := i) (l := n + 1) (q := i + n + 1) hq (by omega)
      rw [show i + (n + 1) = i + n + 1 by omega] at hDC
      have hβq : 1 ≤ β * Real.exp ((i + n + 1 : ℕ) : ℝ) := by
        calc (1 : ℝ) = Real.exp (-((i + n + 1 : ℕ) : ℝ)) * Real.exp ((i + n + 1 : ℕ) : ℝ) := by
              rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          _ ≤ β * Real.exp ((i + n + 1 : ℕ) : ℝ) := by gcongr
      have hexp : Real.exp ((i + n + 1 : ℕ) : ℝ) = Real.exp i * Real.exp 1 ^ (n + 1) := by
        rw [Real.exp_one_pow, ← Real.exp_add]; push_cast; ring_nf
      rw [hexp] at hβq
      have hpow := Real.pow_div_factorial_le_exp _ ht0 n
      calc M (i + n + 1) * h ^ (n + 1) / n ! ≤ M i * A ^ (n + 1) * h ^ (n + 1) / n ! := by
            gcongr
        _ ≤ (β * (Real.exp i * Real.exp 1 ^ (n + 1))) * (M i * A ^ (n + 1) * h ^ (n + 1) / n !) := by
            have : 0 ≤ M i * A ^ (n + 1) * h ^ (n + 1) / n ! := by positivity
            nlinarith
        _ = P * (t * (t ^ n / n !)) := by rw [hP, ht]; field_simp; ring
        _ ≤ P * (t * Real.exp t) := by gcongr
    have htri : |g (x + h)| ≤ |∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) *
        iteratedDerivWithin k g (Icc x (x + h)) x| + |g (x + h) - ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹ * h ^ k) * iteratedDerivWithin k g (Icc x (x + h)) x| := by
      have := abs_add_le (∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * h ^ k) *
        iteratedDerivWithin k g (Icc x (x + h)) x) (g (x + h) - ∑ k ∈ Finset.range (n + 1),
        ((k ! : ℝ)⁻¹ * h ^ k) * iteratedDerivWithin k g (Icc x (x + h)) x)
      simpa using this
    have h1t : 1 + t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
    calc |g (x + h)| ≤ P * Real.exp t + P * (t * Real.exp t) := by linarith
      _ = P * Real.exp t * (1 + t) := by ring
      _ ≤ P * Real.exp t * Real.exp t := by gcongr

end DenjoyCarleman
