import QuasianalyticLean.DenjoyCarleman.Defs

/-!
# Denjoy–Carleman: the converse direction

If `M` is positive and log-convex with `Σ M n / M (n+1) < ∞`, there is a nonzero, smooth,
compactly supported `f` with `|f⁽ⁿ⁾| ≤ C Aⁿ M n`. Construction (Hörmander): apply to a smooth bump
the moving averages `g ↦ a⁻¹ ∫_{x-a}^x g` with steps `a_j = M j / M (j+1)`; each average turns one
derivative into a difference quotient of size `2 / a_j`, and the total support stays finite.
-/

open Set Real Filter Topology MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

namespace Converse

/-- Moving average `(1/a) ∫_{x-a}^x g`, i.e. convolution with `(1/a) 1_{[0,a]}`. -/
def avgOp (a : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ := a⁻¹ * ∫ t in (x - a)..x, g t

lemma avgOp_eq (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    avgOp a g x = a⁻¹ * ((∫ t in (0:ℝ)..x, g t) - ∫ t in (0:ℝ)..(x - a), g t) := by
  unfold avgOp
  rw [intervalIntegral.integral_interval_sub_left (hg.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _)]

lemma hasDerivAt_avgOp (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    HasDerivAt (avgOp a g) (a⁻¹ * (g x - g (x - a))) x := by
  have h1 : HasDerivAt (fun y => ∫ t in (0:ℝ)..y, g t) (g x) x :=
    (hg.integral_hasStrictDerivAt 0 x).hasDerivAt
  have h2 : HasDerivAt (fun y => ∫ t in (0:ℝ)..y, g t) (g (x - a)) (x - a) :=
    (hg.integral_hasStrictDerivAt 0 (x - a)).hasDerivAt
  have h3 := (h1.sub h2.comp_sub_const).const_mul a⁻¹
  have : avgOp a g = fun y => a⁻¹ * ((∫ t in (0:ℝ)..y, g t) - ∫ t in (0:ℝ)..(y - a), g t) := by
    funext y; exact avgOp_eq a hg y
  rw [this]; exact h3

lemma deriv_avgOp (a : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    deriv (avgOp a g) = fun x => a⁻¹ * (g x - g (x - a)) := by
  funext x; exact (hasDerivAt_avgOp a hg x).deriv

lemma avgOp_deriv (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) (x : ℝ) :
    avgOp a (deriv g) x = a⁻¹ * (g x - g (x - a)) := by
  unfold avgOp
  rw [intervalIntegral.integral_deriv_eq_sub]
  · intro y _; exact (hg.differentiable one_ne_zero).differentiableAt
  · exact (hg.continuous_deriv le_rfl).intervalIntegrable _ _

lemma contDiff_avgOp (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (avgOp a g) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (hasDerivAt_avgOp a hg.continuous x).differentiableAt, ?_⟩
  rw [deriv_avgOp a hg.continuous]
  exact contDiff_const.mul (hg.sub (hg.comp (contDiff_id.sub contDiff_const)))

lemma deriv_avgOp' (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) :
    deriv (avgOp a g) = avgOp a (deriv g) := by
  rw [deriv_avgOp a hg.continuous]; funext x
  rw [avgOp_deriv a (hg.of_le (by simp))]

lemma iteratedDeriv_avgOp (a : ℝ) {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    iteratedDeriv n (avgOp a g) = avgOp a (iteratedDeriv n g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hgn : ContDiff ℝ ∞ (iteratedDeriv n g) := by
      rw [iteratedDeriv_eq_iterate]; exact hg.iterate_deriv n
    rw [iteratedDeriv_succ, ih, deriv_avgOp' a hgn, iteratedDeriv_succ]

lemma abs_avgOp_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} {B : ℝ} (hB : ∀ x, |g x| ≤ B) (x : ℝ) :
    |avgOp a g x| ≤ B := by
  unfold avgOp
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := x - a) (b := x) (C := B)
    (f := g) (fun t _ => hB t)
  rw [show x - (x - a) = a by ring, abs_of_pos ha] at h
  rw [abs_mul, abs_inv, abs_of_pos ha]
  calc a⁻¹ * |∫ t in (x - a)..x, g t| ≤ a⁻¹ * (B * a) := by
        gcongr; exact h
    _ = B := by field_simp

lemma abs_deriv_avgOp_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : Continuous g) {B : ℝ}
    (hB : ∀ x, |g x| ≤ B) (x : ℝ) : |deriv (avgOp a g) x| ≤ 2 * B / a := by
  rw [deriv_avgOp a hg, abs_mul, abs_inv, abs_of_pos ha]
  have : |g x - g (x - a)| ≤ 2 * B := by
    calc |g x - g (x - a)| ≤ |g x| + |g (x - a)| := abs_sub _ _
      _ ≤ 2 * B := by linarith [hB x, hB (x - a)]
  calc a⁻¹ * |g x - g (x - a)| ≤ a⁻¹ * (2 * B) := by gcongr
    _ = 2 * B / a := by field_simp

lemma abs_avgOp_sub_le {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : Differentiable ℝ g) {B : ℝ}
    (hB : ∀ x, |deriv g x| ≤ B) (x : ℝ) : |avgOp a g x - g x| ≤ a * B := by
  have hc : Continuous g := hg.continuous
  have e : avgOp a g x - g x = a⁻¹ * ∫ t in (x - a)..x, (g t - g x) := by
    unfold avgOp
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    field_simp; ring
  rw [e]
  have hb : ∀ t ∈ Set.uIoc (x - a) x, ‖g t - g x‖ ≤ B * a := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have := Convex.norm_image_sub_le_of_norm_deriv_le (s := univ) (f := g) (C := B)
      (fun y _ => hg y) (fun y _ => hB y) convex_univ (mem_univ x) (mem_univ t)
    calc ‖g t - g x‖ ≤ B * ‖t - x‖ := this
      _ ≤ B * a := by
        have hB0 : 0 ≤ B := le_trans (abs_nonneg _) (hB x)
        gcongr
        rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [ht.1, ht.2]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [show x - (x - a) = a by ring, abs_of_pos ha] at h
  rw [abs_mul, abs_inv, abs_of_pos ha]
  calc a⁻¹ * |∫ t in (x - a)..x, (g t - g x)| ≤ a⁻¹ * (B * a * a) := by gcongr; exact h
    _ = a * B := by field_simp

lemma avgOp_eq_zero_of_nonpos {a : ℝ} (ha : 0 < a) {g : ℝ → ℝ} (hg : ∀ t ≤ 0, g t = 0)
    {x : ℝ} (hx : x ≤ 0) : avgOp a g x = 0 := by
  unfold avgOp
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
  · simp
  · intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact hg t (by linarith [ht.2])

lemma avgOp_eq_zero_of_ge {a : ℝ} {g : ℝ → ℝ} {L : ℝ} (hg : ∀ t, L ≤ t → g t = 0)
    (ha : 0 < a) {x : ℝ} (hx : L + a ≤ x) : avgOp a g x = 0 := by
  unfold avgOp
  rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
  · simp
  · intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    exact hg t (by linarith [ht.1])


lemma integral_avgOp {a L B : ℝ} (ha : 0 < a) (hLB : L + a ≤ B) {g : ℝ → ℝ} (hg : Continuous g)
    (h0 : ∀ t ≤ 0, g t = 0) (h1 : ∀ t, L ≤ t → g t = 0) :
    ∫ x in (0:ℝ)..B, avgOp a g x = ∫ x in (0:ℝ)..B, g x := by
  set F : ℝ → ℝ := fun y => ∫ t in (0:ℝ)..y, g t with hF
  have hFc : Continuous F :=
    intervalIntegral.continuous_primitive (fun _ _ => hg.intervalIntegrable _ _) 0
  have hav : (fun x => avgOp a g x) = fun x => a⁻¹ * (F x - F (x - a)) := by
    funext x; exact avgOp_eq a hg x
  have hi : ∀ c d : ℝ, IntervalIntegrable F volume c d := fun c d => hFc.intervalIntegrable c d
  have hi2 : IntervalIntegrable (fun x => F (x - a)) volume 0 B :=
    (hFc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [hav, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hi _ _) hi2,
    intervalIntegral.integral_comp_sub_right (fun x => F x)]
  have e1 := intervalIntegral.integral_add_adjacent_intervals (hi 0 (B - a)) (hi (B - a) B)
  have e2 := intervalIntegral.integral_add_adjacent_intervals (hi (0 - a) 0) (hi 0 (B - a))
  have z : ∫ x in (0 - a)..0, F x = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
    · simp
    · intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      show ∫ t in (0:ℝ)..y, g t = 0
      rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
      · simp
      · intro t ht
        rw [Set.uIcc_of_ge hy.2] at ht
        exact h0 t ht.2
  have c : ∫ x in (B - a)..B, F x = a * ∫ x in (0:ℝ)..B, g x := by
    rw [intervalIntegral.integral_congr (g := fun _ => ∫ x in (0:ℝ)..B, g x)]
    · simp
    · intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      show ∫ t in (0:ℝ)..y, g t = ∫ x in (0:ℝ)..B, g x
      have := intervalIntegral.integral_interval_sub_left (μ := volume) (hg.intervalIntegrable 0 B)
        (hg.intervalIntegrable 0 y)
      have hz : ∫ x in y..B, g x = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
        · simp
        · intro t ht
          rw [Set.uIcc_of_le hy.2] at ht
          exact h1 t (by linarith [ht.1, hy.1])
      linarith
  have : (∫ x in (0:ℝ)..B, F x) - ∫ x in (0 - a)..(B - a), F x = a * ∫ x in (0:ℝ)..B, g x := by
    linarith
  rw [this]; field_simp

/-! ### The construction -/

/-- `a j = M j / M (j+1)`. -/
def seqA (M : ℕ → ℝ) (j : ℕ) : ℝ := M j / M (j + 1)

/-- A smooth bump supported in `(0,1)`. -/
def bump : ContDiffBump (1/2 : ℝ) := ⟨1/4, 1/2, by norm_num, by norm_num⟩

/-- `f_k = T_{a_{k-1}} ⋯ T_{a_0} φ`. -/
def fk (M : ℕ → ℝ) : ℕ → ℝ → ℝ
  | 0 => ⇑bump
  | k + 1 => avgOp (seqA M k) (fk M k)

lemma bump_contDiff : ContDiff ℝ ∞ (⇑bump) := bump.contDiff

lemma bump_zero_left {x : ℝ} (hx : x ≤ 0) : bump x = 0 := by
  apply bump.zero_of_le_dist
  show (1/2 : ℝ) ≤ dist x (1/2)
  rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith

lemma bump_zero_right {x : ℝ} (hx : 1 ≤ x) : bump x = 0 := by
  apply bump.zero_of_le_dist
  show (1/2 : ℝ) ≤ dist x (1/2)
  rw [Real.dist_eq, abs_of_nonneg (by linarith)]; linarith

lemma bump_pos {x : ℝ} (h0 : 0 < x) (h1 : x < 1) : 0 < bump x := by
  apply bump.pos_of_mem_ball
  show dist x (1/2) < (1/2 : ℝ)
  rw [Real.dist_eq, abs_lt]; constructor <;> linarith

lemma abs_bump_le (x : ℝ) : |bump x| ≤ 1 := by
  rw [abs_of_nonneg bump.nonneg]; exact bump.le_one

lemma exists_bound_iteratedDeriv_bump (m : ℕ) : ∃ C, ∀ x, |iteratedDeriv m bump x| ≤ C := by
  have hc : Continuous (iteratedFDeriv ℝ m bump) :=
    bump_contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support (bump.hasCompactSupport.iteratedFDeriv m)
  refine ⟨C, fun x => ?_⟩
  have := hC x
  rwa [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs] at this

/-- A uniform bound for `|φ^{(m)}|`. -/
def bumpBound (m : ℕ) : ℝ := Classical.choose (exists_bound_iteratedDeriv_bump m)

lemma bumpBound_spec (m : ℕ) (x : ℝ) : |iteratedDeriv m bump x| ≤ bumpBound m :=
  Classical.choose_spec (exists_bound_iteratedDeriv_bump m) x

section
variable {M : ℕ → ℝ} (hpos : ∀ n, 0 < M n)
include hpos

lemma seqA_pos (j : ℕ) : 0 < seqA M j := div_pos (hpos j) (hpos (j + 1))

omit hpos in
lemma fk_contDiff (k : ℕ) : ContDiff ℝ ∞ (fk M k) := by
  induction k with
  | zero => exact bump_contDiff
  | succ k ih => exact contDiff_avgOp _ ih

lemma fk_zero_left (k : ℕ) : ∀ x ≤ 0, fk M k x = 0 := by
  induction k with
  | zero => intro x hx; exact bump_zero_left hx
  | succ k ih => intro x hx; exact avgOp_eq_zero_of_nonpos (seqA_pos hpos k) ih hx

lemma fk_zero_right (k : ℕ) : ∀ x, 1 + ∑ j ∈ Finset.range k, seqA M j ≤ x → fk M k x = 0 := by
  induction k with
  | zero => intro x hx; exact bump_zero_right (by simpa using hx)
  | succ k ih =>
    intro x hx
    refine avgOp_eq_zero_of_ge ih (seqA_pos hpos k) ?_
    rw [Finset.sum_range_succ] at hx; linarith

lemma fk_bound (k m : ℕ) (x : ℝ) : |iteratedDeriv m (fk M k) x| ≤ bumpBound m := by
  induction k generalizing x with
  | zero => exact bumpBound_spec m x
  | succ k ih =>
    show |iteratedDeriv m (avgOp (seqA M k) (fk M k)) x| ≤ _
    rw [iteratedDeriv_avgOp _ (fk_contDiff k)]
    exact abs_avgOp_le (seqA_pos hpos k) ih x

omit hpos in
lemma iteratedDeriv_fk_contDiff (k n : ℕ) : ContDiff ℝ ∞ (iteratedDeriv n (fk M k)) := by
  rw [iteratedDeriv_eq_iterate]; exact (fk_contDiff k).iterate_deriv n

lemma fk_sharp (k : ℕ) : ∀ n ≤ k, ∀ x,
    |iteratedDeriv n (fk M k) x| ≤ 2 ^ n / ∏ j ∈ Finset.range n, seqA M j := by
  induction k with
  | zero =>
    intro n hn x
    obtain rfl : n = 0 := by omega
    simpa [fk] using abs_bump_le x
  | succ k ih =>
    intro n hn x
    show |iteratedDeriv n (avgOp (seqA M k) (fk M k)) x| ≤ _
    rcases Nat.lt_or_ge n (k + 1) with h | h
    · rw [iteratedDeriv_avgOp _ (fk_contDiff k)]
      exact abs_avgOp_le (seqA_pos hpos k) (ih n (by omega)) x
    · obtain rfl : n = k + 1 := by omega
      rw [iteratedDeriv_succ, iteratedDeriv_avgOp _ (fk_contDiff k)]
      have := abs_deriv_avgOp_le (seqA_pos hpos k) (iteratedDeriv_fk_contDiff k k).continuous
        (ih k le_rfl) x
      refine this.trans (le_of_eq ?_)
      rw [Finset.prod_range_succ, pow_succ]
      have := seqA_pos hpos k
      have : 0 < ∏ j ∈ Finset.range k, seqA M j :=
        Finset.prod_pos fun j _ => seqA_pos hpos j
      field_simp

lemma diff_bound (k n : ℕ) (x : ℝ) :
    |iteratedDeriv n (fk M (k + 1)) x - iteratedDeriv n (fk M k) x| ≤ seqA M k * bumpBound (n + 1) := by
  show |iteratedDeriv n (avgOp (seqA M k) (fk M k)) x - _| ≤ _
  rw [iteratedDeriv_avgOp _ (fk_contDiff k)]
  refine abs_avgOp_sub_le (seqA_pos hpos k)
    ((iteratedDeriv_fk_contDiff k n).differentiable (by simp)) (fun y => ?_) x
  rw [← iteratedDeriv_succ]; exact fk_bound hpos k (n + 1) y

lemma integral_fk {B : ℝ} (hB : ∀ k, 1 + ∑ j ∈ Finset.range (k + 1), seqA M j ≤ B) (k : ℕ) :
    ∫ x in (0:ℝ)..B, fk M k x = ∫ x in (0:ℝ)..B, bump x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← ih]
    show ∫ x in (0:ℝ)..B, avgOp (seqA M k) (fk M k) x = _
    refine integral_avgOp (seqA_pos hpos k) (L := 1 + ∑ j ∈ Finset.range k, seqA M j) ?_
      (fk_contDiff k).continuous (fk_zero_left hpos k) (fk_zero_right hpos k)
    have := hB k; rw [Finset.sum_range_succ] at this; linarith

lemma prod_seqA (n : ℕ) : ∏ j ∈ Finset.range n, seqA M j = M 0 / M n := by
  induction n with
  | zero => simp [(hpos 0).ne']
  | succ n ih =>
    rw [Finset.prod_range_succ, ih, seqA]
    have := hpos n; have := hpos (n + 1)
    field_simp

end

lemma cdAt {f : ℝ → ℝ} (h : ContDiff ℝ ∞ f) (n : ℕ) (x : ℝ) : ContDiffAt ℝ n f x :=
  (h.of_le (by exact_mod_cast le_top)).contDiffAt

/-- Telescoping differences `f_{k+1} - f_k`. -/
def dk (M : ℕ → ℝ) (k : ℕ) : ℝ → ℝ := fk M (k + 1) - fk M k

lemma dk_contDiff {M : ℕ → ℝ} (k : ℕ) : ContDiff ℝ ∞ (dk M k) :=
  (fk_contDiff (k + 1)).sub (fk_contDiff k)

section
variable {M : ℕ → ℝ} (hpos : ∀ n, 0 < M n) (hS : Summable (seqA M))
include hpos

lemma dk_bound (n k : ℕ) (x : ℝ) : |iteratedDeriv n (dk M k) x| ≤ seqA M k * bumpBound (n + 1) := by
  rw [dk, iteratedDeriv_sub (cdAt (fk_contDiff (k + 1)) _ _) (cdAt (fk_contDiff k) _ _)]
  exact diff_bound hpos k n x

include hS

lemma V_contDiff : ContDiff ℝ ∞ (fun x => ∑' k, dk M k x) :=
  contDiff_tsum (v := fun n k => seqA M k * bumpBound (n + 1)) dk_contDiff
    (fun n _ => hS.mul_right _) (fun n k x _ => by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs]
      exact dk_bound hpos n k x)

lemma summable_iteratedDeriv_dk (n : ℕ) (x : ℝ) :
    Summable (fun k => iteratedDeriv n (dk M k) x) :=
  Summable.of_norm_bounded (hS.mul_right (bumpBound (n + 1))) fun k => by
    rw [Real.norm_eq_abs]; exact dk_bound hpos n k x

lemma iteratedDeriv_V (n : ℕ) :
    iteratedDeriv n (fun x => ∑' k, dk M k x) = fun x => ∑' k, iteratedDeriv n (dk M k) x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    rw [deriv_tsum (u := fun k => seqA M k * bumpBound (n + 1 + 1))
      (g := fun k => iteratedDeriv n (dk M k)) (y₀ := 0) (hS.mul_right _)
      (fun k => (dk_contDiff k).differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top _))
      (fun k y => by
        rw [← iteratedDeriv_succ, Real.norm_eq_abs]; exact dk_bound hpos (n + 1) k y)
      (summable_iteratedDeriv_dk hpos hS n 0)]
    funext x; simp only [iteratedDeriv_succ]

end

end Converse

open Converse in
theorem exists_bump_of_summable {M : ℕ → ℝ} (hM : LogConvexSeq M)
    (hS : Summable (fun n => M n / M (n + 1))) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ f ≠ 0 ∧
      ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ∀ x : ℝ, |iteratedDeriv n f x| ≤ C * A ^ n * M n := by
  have hpos := hM.pos
  have hS' : Summable (seqA M) := hS
  set S := ∑' j, seqA M j with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg fun j => (seqA_pos hpos j).le
  have hpart : ∀ k, ∑ j ∈ Finset.range k, seqA M j ≤ S := fun k =>
    hS'.sum_le_tsum _ (fun j _ => (seqA_pos hpos j).le)
  set B := 1 + S with hBdef
  set V : ℝ → ℝ := fun x => ∑' k, dk M k x with hVdef
  have hVc : ContDiff ℝ ∞ V := V_contDiff hpos hS'
  refine ⟨fun x => bump x + V x, bump_contDiff.add hVc, ?_, ?_, ?_⟩
  · -- compact support
    refine HasCompactSupport.intro (isCompact_Icc (a := 0) (b := B)) fun x hx => ?_
    have hfk : ∀ k, fk M k x = 0 := by
      intro k
      rcases not_and_or.mp (show ¬ (0 ≤ x ∧ x ≤ B) from hx) with h | h
      · exact fk_zero_left hpos k x (by linarith)
      · exact fk_zero_right hpos k x (by linarith [hpart k])
    have h0 : bump x = 0 := hfk 0
    have hV : V x = 0 := by
      simp only [hVdef, dk, Pi.sub_apply, hfk, sub_self, tsum_zero]
    simp [h0, hV]
  · -- nonzero
    intro h
    have hB : ∀ k, 1 + ∑ j ∈ Finset.range (k + 1), seqA M j ≤ B := fun k => by
      linarith [hpart (k + 1)]
    have hVint : ∫ x in (0:ℝ)..B, V x = 0 := by
      have hs := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
        (a := 0) (b := B) (F := fun k => dk M k) (f := V)
        (fun k _ => seqA M k * bumpBound 1)
        (fun k => (dk_contDiff k).continuous.aestronglyMeasurable)
        (fun k => ae_of_all _ fun t _ => by
          have := dk_bound hpos 0 k t
          simpa [Real.norm_eq_abs] using this)
        (ae_of_all _ fun t _ => hS'.mul_right _)
        intervalIntegrable_const
        (ae_of_all _ fun t _ => by
          have := (summable_iteratedDeriv_dk hpos hS' 0 t).hasSum
          simpa using this)
      have hz : (fun k => ∫ t in (0:ℝ)..B, dk M k t) = fun _ => 0 := by
        funext k
        simp only [dk, Pi.sub_apply]
        rw [intervalIntegral.integral_sub ((fk_contDiff (k + 1)).continuous.intervalIntegrable _ _)
          ((fk_contDiff k).continuous.intervalIntegrable _ _),
          integral_fk hpos hB, integral_fk hpos hB, sub_self]
      rw [hz] at hs
      exact hs.unique hasSum_zero
    have hbpos : 0 < ∫ x in (0:ℝ)..B, bump x := by
      have e := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
        (bump.continuous.intervalIntegrable 0 1) (bump.continuous.intervalIntegrable 1 B)
      have z : ∫ x in (1:ℝ)..B, bump x = 0 := by
        rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ))]
        · simp
        · intro t ht
          rw [Set.uIcc_of_le (by linarith)] at ht
          exact bump_zero_right ht.1
      have p : 0 < ∫ x in (0:ℝ)..1, bump x :=
        intervalIntegral.intervalIntegral_pos_of_pos_on (bump.continuous.intervalIntegrable 0 1)
          (fun x hx => bump_pos hx.1 hx.2) one_pos
      linarith
    have hU : ∫ x in (0:ℝ)..B, (bump x + V x) = 0 := by
      simp only [show ∀ x, bump x + V x = 0 from fun x => congrFun h x]; simp
    rw [intervalIntegral.integral_add (bump.continuous.intervalIntegrable _ _)
      (hVc.continuous.intervalIntegrable _ _), hVint] at hU
    linarith
  · refine ⟨1 / M 0, 2, div_pos one_pos (hpos 0), two_pos, fun n x => ?_⟩
    have hDU : iteratedDeriv n (fun x => bump x + V x) x
        = iteratedDeriv n bump x + ∑' k, iteratedDeriv n (dk M k) x := by
      rw [iteratedDeriv_fun_add (cdAt bump_contDiff _ _) (cdAt hVc _ _), hVdef,
        iteratedDeriv_V hpos hS']
    have hsum := (summable_iteratedDeriv_dk hpos hS' n x).hasSum.tendsto_sum_nat
    have htel : ∀ K, ∑ k ∈ Finset.range K, iteratedDeriv n (dk M k) x
        = iteratedDeriv n (fk M K) x - iteratedDeriv n bump x := by
      intro K
      have : ∀ k, iteratedDeriv n (dk M k) x
          = iteratedDeriv n (fk M (k + 1)) x - iteratedDeriv n (fk M k) x := fun k => by
        rw [dk, iteratedDeriv_sub (cdAt (fk_contDiff (k + 1)) _ _) (cdAt (fk_contDiff k) _ _)]
      simp only [this]
      rw [Finset.sum_range_sub (fun k => iteratedDeriv n (fk M k) x)]
      rfl
    simp only [htel] at hsum
    have hlim : Tendsto (fun K => iteratedDeriv n (fk M K) x) atTop
        (𝓝 (iteratedDeriv n (fun x => bump x + V x) x)) := by
      rw [hDU]
      have := hsum.add_const (iteratedDeriv n bump x)
      simpa [add_comm] using this
    refine le_of_tendsto hlim.abs (Filter.eventually_atTop.2 ⟨n, fun K hK => ?_⟩)
    refine (fk_sharp hpos K n hK x).trans (le_of_eq ?_)
    rw [prod_seqA hpos]
    have := hpos 0; have := hpos n
    field_simp

end DenjoyCarleman
