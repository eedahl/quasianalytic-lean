import QuasianalyticLean.GevreyEdge.Defs

open Set Real Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

lemma P1_T_bound' (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i) ≤ (4 ^ (n + 2) - 3 * n - 7) / 9 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ']
    have : ∑ i ∈ Finset.range (n + 1), (4 : ℝ) ^ (i + 1) * (((n + 1 : ℕ) : ℝ) + 1 - ((i + 1 : ℕ) : ℝ))
        = 4 * ∑ i ∈ Finset.range (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i) := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; push_cast; ring
    rw [this]
    push_cast
    rw [pow_succ 4 (n + 2)]
    nlinarith

lemma P1_T_bound (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i) ≤ 4 ^ (n + 1) := by
  refine (P1_T_bound' n).trans ?_
  rw [pow_succ 4 (n + 1)]
  have : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have : (0:ℝ) ≤ 4 ^ (n + 1) := by positivity
  linarith

lemma P1_inner (n j : ℕ) (hj : j ≤ n) :
    ((j : ℝ) + 1) * ∑ i ∈ Finset.Ico j (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i)
      ≤ ((n : ℝ) + 1) * 4 ^ (n + 1) := by
  have hsub : ∑ i ∈ Finset.Ico j (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i)
      ≤ ∑ i ∈ Finset.range (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro i; simp [Finset.mem_Ico, Finset.mem_range]
    · intro i hi _
      have : (i : ℝ) ≤ n := by
        have := Finset.mem_range.mp hi; exact_mod_cast (by omega : i ≤ n)
      have : (0:ℝ) ≤ (n : ℝ) + 1 - i := by linarith
      positivity
  have hnn : 0 ≤ ∑ i ∈ Finset.Ico j (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i) := by
    apply Finset.sum_nonneg; intro i hi
    have : (i : ℝ) ≤ n := by
      have := (Finset.mem_Ico.mp hi).2; exact_mod_cast (by omega : i ≤ n)
    have : (0:ℝ) ≤ (n : ℝ) + 1 - i := by linarith
    positivity
  have hT := P1_T_bound n
  have hjn : (j : ℝ) ≤ n := by exact_mod_cast hj
  have h4 : (0:ℝ) ≤ 4 ^ (n + 1) := by positivity
  nlinarith

/-- Bound for the derivatives of `g^{(k)} ∘ f`. -/
def P1M (C A K r s : ℝ) (k n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), C * A ^ (k + j) * (((k + j) ! : ℕ) : ℝ) ^ s * K ^ j *
    (r⁻¹) ^ (n - j) * (4 ^ n * ((n ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ))

lemma P1_step {C A K r s : ℝ} (hr : 0 < r) (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 ≤ C) (k n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P1M C A K r s (k + 1) i *
      (K * (((n - i + 1) ! : ℕ) : ℝ) * (r⁻¹) ^ (n - i)) ≤ P1M C A K r s k (n + 1) := by
  set P : ℕ → ℝ := fun j => C * A ^ (k + (j + 1)) * (((k + (j + 1)) ! : ℕ) : ℝ) ^ s * K ^ (j + 1) *
    (r⁻¹) ^ (n - j) * (((n ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ)) with hP
  have hPnn : ∀ j, 0 ≤ P j := fun j => by simp only [hP]; positivity
  have h1 : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P1M C A K r s (k + 1) i *
      (K * (((n - i + 1) ! : ℕ) : ℝ) * (r⁻¹) ^ (n - i))
      = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
          P j * (4 ^ i * ((n : ℝ) + 1 - i)) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    unfold P1M
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hji : j ≤ i := by have := Finset.mem_range.mp hj; omega
    have e1 : k + 1 + j = k + (j + 1) := by omega
    have e2 : (r⁻¹) ^ (i - j) * (r⁻¹) ^ (n - i) = (r⁻¹) ^ (n - j) := by
      rw [← pow_add]; congr 1; omega
    have e3 : (n.choose i : ℝ) * ((i ! : ℕ) : ℝ) * (((n - i) ! : ℕ) : ℝ) = ((n ! : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
    have e4 : (((n - i + 1) ! : ℕ) : ℝ) = ((n : ℝ) + 1 - i) * (((n - i) ! : ℕ) : ℝ) := by
      rw [Nat.factorial_succ]; push_cast [Nat.cast_sub hin]; ring
    have hj0 : (((j ! : ℕ) : ℝ)) ≠ 0 := by positivity
    simp only [hP, e1, e4]
    rw [← e3, ← e2]
    field_simp
    ring
  have h2 : ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1),
          P j * (4 ^ i * ((n : ℝ) + 1 - i))
      = ∑ j ∈ Finset.range (n + 1), P j *
          ∑ i ∈ Finset.Ico j (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i) := by
    simp only [Finset.mul_sum]
    rw [Finset.range_eq_Ico, Finset.sum_Ico_Ico_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.range_eq_Ico]
  rw [h1, h2]
  calc ∑ j ∈ Finset.range (n + 1), P j *
          ∑ i ∈ Finset.Ico j (n + 1), (4 : ℝ) ^ i * ((n : ℝ) + 1 - i)
      ≤ ∑ j ∈ Finset.range (n + 1), P j * (((n : ℝ) + 1) * 4 ^ (n + 1) / ((j : ℝ) + 1)) := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hjn : j ≤ n := by have := Finset.mem_range.mp hj; omega
        refine mul_le_mul_of_nonneg_left ?_ (hPnn j)
        rw [le_div_iff₀ (by positivity)]
        have := P1_inner n j hjn
        linarith
    _ = ∑ j ∈ Finset.range (n + 1), C * A ^ (k + (j + 1)) * (((k + (j + 1)) ! : ℕ) : ℝ) ^ s *
          K ^ (j + 1) * (r⁻¹) ^ (n + 1 - (j + 1)) *
          (4 ^ (n + 1) * (((n + 1) ! : ℕ) : ℝ) / (((j + 1) ! : ℕ) : ℝ)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : n + 1 - (j + 1) = n - j := by omega
        have hj0 : (((j ! : ℕ) : ℝ)) ≠ 0 := by positivity
        simp only [hP, e, Nat.factorial_succ]
        push_cast
        field_simp
    _ ≤ P1M C A K r s k (n + 1) := by
        unfold P1M
        rw [Finset.sum_range_succ' _ (n + 1)]
        have : 0 ≤ C * A ^ (k + 0) * (((k + 0) ! : ℕ) : ℝ) ^ s * K ^ 0 * (r⁻¹) ^ (n + 1 - 0) *
            (4 ^ (n + 1) * (((n + 1) ! : ℕ) : ℝ) / ((0 ! : ℕ) : ℝ)) := by positivity
        linarith

lemma P1_final {C A K H r s : ℝ} (hr : 0 < r) (hA : 1 ≤ A) (hK : 1 ≤ K) (hC : 0 ≤ C)
    (hH : 0 ≤ H) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P1M C A K r s 0 i *
      (H * (((n - i) ! : ℕ) : ℝ) * (r⁻¹) ^ (n - i)) ≤ C * H * (16 * A * K) ^ n * shape s r⁻¹ n := by
  set Q : ℕ → ℝ := fun j => C * H * ((A * K) ^ n * 4 ^ n * 2 ^ n) *
    ((((j ! : ℕ) : ℝ) ^ s * (((n - j) ! : ℕ) : ℝ) * (r⁻¹) ^ (n - j))) with hQ
  have hQnn : ∀ j, 0 ≤ Q j := fun j => by simp only [hQ]; positivity
  have hA0 : 0 ≤ A := by linarith
  have hK0 : 0 ≤ K := by linarith
  have h1 : ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * P1M C A K r s 0 i *
      (H * (((n - i) ! : ℕ) : ℝ) * (r⁻¹) ^ (n - i))
      ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), Q j := by
    refine Finset.sum_le_sum fun i hi => ?_
    have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
    unfold P1M
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    have hji : j ≤ i := by have := Finset.mem_range.mp hj; omega
    have e2 : (r⁻¹) ^ (i - j) * (r⁻¹) ^ (n - i) = (r⁻¹) ^ (n - j) := by
      rw [← pow_add]; congr 1; omega
    have e3 : (n.choose i : ℝ) * ((i ! : ℕ) : ℝ) * (((n - i) ! : ℕ) : ℝ) = ((n ! : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_factorial_mul_factorial hin
    have hj0 : (((j ! : ℕ) : ℝ)) ≠ 0 := by positivity
    have eq : (n.choose i : ℝ) * (C * A ^ (0 + j) * (((0 + j) ! : ℕ) : ℝ) ^ s * K ^ j *
        (r⁻¹) ^ (i - j) * (4 ^ i * ((i ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ))) *
        (H * (((n - i) ! : ℕ) : ℝ) * (r⁻¹) ^ (n - i))
        = C * H * (A ^ j * K ^ j * 4 ^ i) * (((n ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ)) *
          (((j ! : ℕ) : ℝ) ^ s * (r⁻¹) ^ (n - j)) := by
      simp only [zero_add]
      rw [← e3, ← e2]
      field_simp
    rw [eq]
    have b1 : A ^ j * K ^ j * 4 ^ i ≤ (A * K) ^ n * 4 ^ n := by
      rw [mul_pow]
      have a1 := pow_le_pow_right₀ hA (hji.trans hin)
      have a2 := pow_le_pow_right₀ hK (hji.trans hin)
      have a3 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 4) hin
      exact mul_le_mul (mul_le_mul a1 a2 (by positivity) (by positivity)) a3 (by positivity)
        (by positivity)
    have hjn : j ≤ n := by omega
    have b2 : ((n ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ) ≤ 2 ^ n * (((n - j) ! : ℕ) : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      have e : (n.choose j : ℝ) * ((j ! : ℕ) : ℝ) * (((n - j) ! : ℕ) : ℝ) = ((n ! : ℕ) : ℝ) := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hjn
      have hc : (n.choose j : ℝ) ≤ 2 ^ n := by exact_mod_cast Nat.choose_le_two_pow n j
      rw [← e]
      have : (0:ℝ) ≤ ((j ! : ℕ) : ℝ) * (((n - j) ! : ℕ) : ℝ) := by positivity
      nlinarith
    simp only [hQ]
    have := mul_le_mul b1 b2 (by positivity) (by positivity)
    have hCH : 0 ≤ C * H := by positivity
    have hX : 0 ≤ ((j ! : ℕ) : ℝ) ^ s * (r⁻¹) ^ (n - j) := by positivity
    calc C * H * (A ^ j * K ^ j * 4 ^ i) * (((n ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ)) *
          (((j ! : ℕ) : ℝ) ^ s * (r⁻¹) ^ (n - j))
        = C * H * ((A ^ j * K ^ j * 4 ^ i) * (((n ! : ℕ) : ℝ) / ((j ! : ℕ) : ℝ))) *
          (((j ! : ℕ) : ℝ) ^ s * (r⁻¹) ^ (n - j)) := by ring
      _ ≤ C * H * (((A * K) ^ n * 4 ^ n) * (2 ^ n * (((n - j) ! : ℕ) : ℝ))) *
          (((j ! : ℕ) : ℝ) ^ s * (r⁻¹) ^ (n - j)) := by gcongr
      _ = _ := by ring
  refine h1.trans ?_
  have h2 : ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (i + 1), Q j
      ≤ ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1), Q j := by
    refine Finset.sum_le_sum fun i hi => ?_
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro j hj; simp only [Finset.mem_range] at *; omega
    · intro j _ _; exact hQnn j
  refine h2.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn2 : ((n + 1 : ℕ) : ℝ) ≤ 2 ^ n := by
    exact_mod_cast Nat.lt_two_pow_self (n := n)
  have hsum : ∑ j ∈ Finset.range (n + 1), Q j =
      C * H * ((A * K) ^ n * 4 ^ n * 2 ^ n) * shape s r⁻¹ n := by
    simp only [hQ, shape, Finset.mul_sum]
  have hS : 0 ≤ ∑ j ∈ Finset.range (n + 1), Q j := Finset.sum_nonneg fun j _ => hQnn j
  calc ((n + 1 : ℕ) : ℝ) * ∑ j ∈ Finset.range (n + 1), Q j
      ≤ 2 ^ n * ∑ j ∈ Finset.range (n + 1), Q j := mul_le_mul_of_nonneg_right hn2 hS
    _ = C * H * (16 * A * K) ^ n * shape s r⁻¹ n := by
        rw [hsum]
        have : (16 * A * K) ^ n = (A * K) ^ n * 4 ^ n * 2 ^ n * 2 ^ n := by
          rw [← mul_pow, ← mul_pow, ← mul_pow]; ring_nf
        rw [this]; ring

/-- **P1.** One-variable Gevrey Faà di Bruno with a product. -/
theorem P1_comp_mul_bound {g f h : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) {y : ℝ}
    {C A K H r s : ℝ} (hs : 1 ≤ s) (hr : 0 < r) (hr1 : r ≤ 1) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hC : 0 ≤ C) (hH : 0 ≤ H)
    (hg : ContDiffOn ℝ ∞ g U)
    (hgb : ∀ j : ℕ, ∀ x ∈ U, |iteratedDeriv j g x| ≤ C * A ^ j * ((j ! : ℕ) : ℝ) ^ s)
    (hφ : ContDiffAt ℝ ∞ f y) (hφU : f y ∈ U)
    (hφb : ∀ m : ℕ, 1 ≤ m → |iteratedDeriv m f y| ≤ K * (m ! : ℕ) * (r⁻¹) ^ (m - 1))
    (hh : ContDiffAt ℝ ∞ h y)
    (hhb : ∀ m : ℕ, |iteratedDeriv m h y| ≤ H * (m ! : ℕ) * (r⁻¹) ^ m) :
    ∀ n : ℕ, |iteratedDeriv n (fun x => g (f x) * h x) y| ≤
      C * H * (16 * A * K) ^ n * shape s r⁻¹ n := by
  have hgk : ∀ k : ℕ, ContDiffOn ℝ ∞ (iteratedDeriv k g) U := by
    intro k
    induction k with
    | zero => simpa using hg
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv_of_isOpen hU (by simp)
  have hFk : ∀ k : ℕ, ContDiffAt ℝ ∞ (fun x => iteratedDeriv k g (f x)) y := fun k =>
    ((hgk k).contDiffAt (hU.mem_nhds hφU)).comp y hφ
  have hdf : ContDiffAt ℝ ∞ (deriv f) y := hφ.derivWithin (by simp)
  have hev : ∀ᶠ x in 𝓝 y, DifferentiableAt ℝ f x ∧ f x ∈ U := by
    have h1 : ∀ᶠ x in 𝓝 y, ContDiffAt ℝ 1 f x := (hφ.of_le (by simp)).eventually (by simp)
    have h2 : ∀ᶠ x in 𝓝 y, f x ∈ U := hφ.continuousAt.preimage_mem_nhds (hU.mem_nhds hφU)
    filter_upwards [h1, h2] with x hx1 hx2
    exact ⟨hx1.differentiableAt one_ne_zero, hx2⟩
  have hderiv : ∀ k : ℕ, deriv (fun x => iteratedDeriv k g (f x)) =ᶠ[𝓝 y]
      fun x => iteratedDeriv (k + 1) g (f x) * deriv f x := by
    intro k
    filter_upwards [hev] with x hx
    have hgd : DifferentiableAt ℝ (iteratedDeriv k g) (f x) :=
      ((hgk k).differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx.2)
    rw [iteratedDeriv_succ]
    exact deriv_comp x hgd hx.1
  have main : ∀ n k : ℕ,
      |iteratedDeriv n (fun x => iteratedDeriv k g (f x)) y| ≤ P1M C A K r s k n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro k
    cases n with
    | zero =>
      simpa [P1M] using hgb k (f y) hφU
    | succ n =>
      rw [iteratedDeriv_succ', (hderiv k).iteratedDeriv_eq n,
        iteratedDeriv_fun_mul ((hFk (k + 1)).of_le (by simp)) (hdf.of_le (by simp))]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans ?_ (P1_step hr (by linarith) (by linarith) hC k n)
      refine Finset.sum_le_sum fun i hi => ?_
      have hin : i ≤ n := by have := Finset.mem_range.mp hi; omega
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), ← iteratedDeriv_succ']
      have b1 := ih i (by omega) (k + 1)
      have b2 := hφb (n - i + 1) (by omega)
      rw [Nat.add_sub_cancel] at b2
      have hM : 0 ≤ P1M C A K r s (k + 1) i := by
        unfold P1M
        refine Finset.sum_nonneg fun j _ => ?_
        have : 0 ≤ A := by linarith
        have : 0 ≤ K := by linarith
        positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left b1 (Nat.cast_nonneg _)) b2 (abs_nonneg _)
        (by positivity)
  intro n
  have hfun : (fun x => g (f x) * h x) = fun x => iteratedDeriv 0 g (f x) * h x := by
    simp [iteratedDeriv_zero]
  rw [hfun, iteratedDeriv_fun_mul ((hFk 0).of_le (by simp)) (hh.of_le (by simp))]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans ?_ (P1_final hr hA hK hC hH n)
  refine Finset.sum_le_sum fun i hi => ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hM : 0 ≤ P1M C A K r s 0 i := by
    unfold P1M
    refine Finset.sum_nonneg fun j _ => ?_
    have : 0 ≤ A := by linarith
    have : 0 ≤ K := by linarith
    positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left (main i 0) (Nat.cast_nonneg _)) (hhb (n - i))
    (abs_nonneg _) (by positivity)

end GevreyEdge
