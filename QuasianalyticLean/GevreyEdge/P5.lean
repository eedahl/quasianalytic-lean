import QuasianalyticLean.GevreyEdge.Defs

open Set Real Filter Topology MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

/-- `Γ(m/k + 1) ≤ (m!)^{1/k}` by log-convexity of `Γ`. -/
lemma P5_gamma_le {k : ℕ} (hk : 1 ≤ k) (m : ℕ) :
    Gamma ((m : ℝ) / k + 1) ≤ ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k) := by
  rcases Nat.lt_or_ge 1 k with h | h
  · have hk' : (1 : ℝ) < k := by exact_mod_cast h
    have hkpos : (0 : ℝ) < k := by linarith
    have ha : (0 : ℝ) < 1 / k := by positivity
    have hb : (0 : ℝ) < 1 - 1 / k := by
      rw [sub_pos, div_lt_one hkpos]; exact hk'
    have key := Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma (s := (m : ℝ) + 1) (t := 1)
      (by positivity) one_pos ha hb (by ring)
    have e : 1 / (k : ℝ) * ((m : ℝ) + 1) + (1 - 1 / k) * 1 = (m : ℝ) / k + 1 := by
      field_simp; ring
    rw [e, Gamma_nat_eq_factorial, Gamma_one, one_rpow, mul_one] at key
    exact key
  · have : k = 1 := le_antisymm h hk
    subst this
    simp [Gamma_nat_eq_factorial]

lemma P5_pow_bound {p w : ℝ} (hp : 0 ≤ p) (hw : 0 ≤ w) :
    (1 + w) ^ p ≤ (2 : ℝ) ^ p * (1 + w ^ p) := by
  have h2 : (0 : ℝ) ≤ 2 ^ p := by positivity
  have hwp : 0 ≤ w ^ p := by positivity
  rcases le_total w 1 with h | h
  · calc (1 + w) ^ p ≤ 2 ^ p := rpow_le_rpow (by linarith) (by linarith) hp
      _ ≤ 2 ^ p * (1 + w ^ p) := by nlinarith
  · calc (1 + w) ^ p ≤ (2 * w) ^ p := rpow_le_rpow (by linarith) (by linarith) hp
      _ = 2 ^ p * w ^ p := mul_rpow (by norm_num) hw
      _ ≤ 2 ^ p * (1 + w ^ p) := by nlinarith

lemma P5_integrableOn {p : ℝ} (hp : 0 ≤ p) :
    IntegrableOn (fun w : ℝ => exp (-w) * (1 + w ^ p)) (Ioi 0) := by
  have h1 := integrableOn_exp_neg_Ioi 0
  have h2 := GammaIntegral_convergent (s := p + 1) (by linarith)
  simp only [add_sub_cancel_right] at h2
  have := h1.add h2
  refine this.congr_fun (fun w _ => ?_) measurableSet_Ioi
  simp only [Pi.add_apply]; ring

lemma P5_integral {p : ℝ} (hp : 0 ≤ p) :
    ∫ w in Ioi (0 : ℝ), exp (-w) * (1 + w ^ p) = 1 + Gamma (p + 1) := by
  have h1 := integrableOn_exp_neg_Ioi 0
  have h2 := GammaIntegral_convergent (s := p + 1) (by linarith)
  simp only [add_sub_cancel_right] at h2
  have e : (fun w : ℝ => exp (-w) * (1 + w ^ p)) = fun w => exp (-w) + exp (-w) * w ^ p := by
    funext w; ring
  rw [e, integral_add h1 h2, integral_exp_neg_Ioi_zero, Gamma_eq_integral (by linarith),
    add_sub_cancel_right]

/-- **P5.** The `w`-integral of the shape bound. -/
theorem P5_integral_shape {k : ℕ} (hk : 1 ≤ k) {κ s : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hs : 1 ≤ s) :
    ∃ C E : ℝ, 0 ≤ C ∧ 0 ≤ E ∧ ∀ n : ℕ,
      ∫ w in Ioi (0 : ℝ), Real.exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n ≤
        C * E ^ n * ((n ! : ℕ) : ℝ) ^ (max s (1 + 1 / (k : ℝ))) := by
  refine ⟨2, 4 * κ⁻¹, by norm_num, by positivity, fun n => ?_⟩
  set M := max s (1 + 1 / (k : ℝ)) with hM
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hκi : 1 ≤ κ⁻¹ := one_le_inv_iff₀.mpr ⟨hκ, hκ1⟩
  -- coefficients
  set a : ℕ → ℝ := fun j => ((j ! : ℕ) : ℝ) ^ s * (((n - j) ! : ℕ) : ℝ) * (κ⁻¹ ^ n * 2 ^ n)
    with ha
  have ha0 : ∀ j, 0 ≤ a j := fun j => by positivity
  set g : ℕ → ℝ → ℝ := fun j w => a j * (exp (-w) * (1 + w ^ (((n - j : ℕ) : ℝ) / k))) with hg
  have hgi : ∀ j ∈ Finset.range (n + 1), Integrable (g j) (volume.restrict (Ioi 0)) :=
    fun j _ => (P5_integrableOn (by positivity)).const_mul _
  -- pointwise bound
  have hpt : ∀ w ∈ Ioi (0 : ℝ), exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n ≤
      ∑ j ∈ Finset.range (n + 1), g j w := by
    intro w hw
    have hw0 : (0 : ℝ) ≤ w := le_of_lt hw
    rw [shape, Finset.mul_sum]
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    set m := n - j
    have hρ : (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) ^ m = κ⁻¹ ^ m * (1 + w) ^ ((m : ℝ) / k) := by
      rw [mul_pow, ← rpow_mul_natCast (by linarith)]
      congr 2; ring
    have hmn : m ≤ n := Nat.sub_le n j
    have hp0 : (0 : ℝ) ≤ (m : ℝ) / k := by positivity
    have hpn : (m : ℝ) / k ≤ n := by
      rw [div_le_iff₀ hkpos]
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have h2 : (2 : ℝ) ^ ((m : ℝ) / k) ≤ 2 ^ n := by
      rw [← rpow_natCast]; exact rpow_le_rpow_of_exponent_le (by norm_num) hpn
    have hκm : κ⁻¹ ^ m ≤ κ⁻¹ ^ n := pow_le_pow_right₀ hκi hmn
    have hb := P5_pow_bound hp0 hw0
    have hq : 0 ≤ 1 + w ^ ((m : ℝ) / k) := by positivity
    have hρb : κ⁻¹ ^ m * (1 + w) ^ ((m : ℝ) / k) ≤
        (κ⁻¹ ^ n * 2 ^ n) * (1 + w ^ ((m : ℝ) / k)) := by
      calc κ⁻¹ ^ m * (1 + w) ^ ((m : ℝ) / k)
          ≤ κ⁻¹ ^ n * (2 ^ ((m : ℝ) / k) * (1 + w ^ ((m : ℝ) / k))) :=
            mul_le_mul hκm hb (by positivity) (by positivity)
        _ ≤ κ⁻¹ ^ n * (2 ^ n * (1 + w ^ ((m : ℝ) / k))) := by gcongr
        _ = _ := by ring
    rw [hρ]
    simp only [hg, ha]
    have hc : 0 ≤ exp (-w) * (((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ)) := by positivity
    calc exp (-w) * (((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ) *
          (κ⁻¹ ^ m * (1 + w) ^ ((m : ℝ) / k)))
        = (exp (-w) * (((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ))) *
          (κ⁻¹ ^ m * (1 + w) ^ ((m : ℝ) / k)) := by ring
      _ ≤ (exp (-w) * (((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ))) *
          ((κ⁻¹ ^ n * 2 ^ n) * (1 + w ^ ((m : ℝ) / k))) := mul_le_mul_of_nonneg_left hρb hc
      _ = _ := by ring
  have hf0 : ∀ w ∈ Ioi (0 : ℝ), 0 ≤ exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n := by
    intro w hw
    have : (0 : ℝ) ≤ κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k) := by
      have : (0 : ℝ) ≤ 1 + w := by linarith [le_of_lt (show (0:ℝ) < w from hw)]
      positivity
    unfold shape
    positivity
  have hmono : ∫ w in Ioi (0 : ℝ), exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n ≤
      ∫ w in Ioi (0 : ℝ), ∑ j ∈ Finset.range (n + 1), g j w := by
    refine integral_mono_of_nonneg ?_ (integrable_finsetSum _ hgi) ?_
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hf0)
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hpt)
  refine hmono.trans ?_
  rw [integral_finsetSum _ hgi]
  -- each term
  have hterm : ∀ j ∈ Finset.range (n + 1), ∫ w in Ioi (0 : ℝ), g j w ≤
      2 * (κ⁻¹ ^ n * 2 ^ n) * ((n ! : ℕ) : ℝ) ^ M := by
    intro j hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    simp only [hg]
    rw [integral_const_mul, P5_integral (by positivity)]
    set m := n - j
    have hG := P5_gamma_le hk m
    have hm1 : (1 : ℝ) ≤ ((m ! : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero m)
    have hj1 : (1 : ℝ) ≤ ((j ! : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero j)
    have hmk : (1 : ℝ) ≤ ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k) := one_le_rpow hm1 (by positivity)
    have hsum : 1 + Gamma ((m : ℝ) / k + 1) ≤ 2 * ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k) := by linarith
    have hfac : ((j ! : ℕ) : ℝ) ^ s * (((m ! : ℕ) : ℝ) * ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k)) ≤
        ((n ! : ℕ) : ℝ) ^ M := by
      have e : ((m ! : ℕ) : ℝ) * ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k) =
          ((m ! : ℕ) : ℝ) ^ (1 + 1 / (k : ℝ)) := by
        rw [rpow_add (by linarith), rpow_one]
      rw [e]
      have h1 : ((j ! : ℕ) : ℝ) ^ s ≤ ((j ! : ℕ) : ℝ) ^ M :=
        rpow_le_rpow_of_exponent_le hj1 (le_max_left _ _)
      have h2 : ((m ! : ℕ) : ℝ) ^ (1 + 1 / (k : ℝ)) ≤ ((m ! : ℕ) : ℝ) ^ M :=
        rpow_le_rpow_of_exponent_le hm1 (le_max_right _ _)
      have hdvd : j ! * m ! ≤ n ! :=
        Nat.le_of_dvd (Nat.factorial_pos n) (Nat.factorial_mul_factorial_dvd_factorial hjn)
      have hM0 : 0 ≤ M := le_trans (by linarith) (le_max_left s _)
      calc ((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ) ^ (1 + 1 / (k : ℝ))
          ≤ ((j ! : ℕ) : ℝ) ^ M * ((m ! : ℕ) : ℝ) ^ M :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (((j ! * m ! : ℕ)) : ℝ) ^ M := by
            rw [Nat.cast_mul, mul_rpow (by positivity) (by positivity)]
        _ ≤ ((n ! : ℕ) : ℝ) ^ M :=
            rpow_le_rpow (by positivity) (by exact_mod_cast hdvd) hM0
    have hA : 0 ≤ κ⁻¹ ^ n * 2 ^ n := by positivity
    simp only [ha]
    calc ((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ) * (κ⁻¹ ^ n * 2 ^ n) *
          (1 + Gamma ((m : ℝ) / k + 1))
        ≤ ((j ! : ℕ) : ℝ) ^ s * ((m ! : ℕ) : ℝ) * (κ⁻¹ ^ n * 2 ^ n) *
          (2 * ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = 2 * (κ⁻¹ ^ n * 2 ^ n) *
          (((j ! : ℕ) : ℝ) ^ s * (((m ! : ℕ) : ℝ) * ((m ! : ℕ) : ℝ) ^ ((1 : ℝ) / k))) := by ring
      _ ≤ 2 * (κ⁻¹ ^ n * 2 ^ n) * ((n ! : ℕ) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_left hfac (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hn2 : ((n + 1 : ℕ) : ℝ) ≤ 2 ^ n := by
    have := Nat.lt_two_pow_self (n := n)
    exact_mod_cast this
  have hP : 0 ≤ 2 * (κ⁻¹ ^ n * 2 ^ n) * ((n ! : ℕ) : ℝ) ^ M := by positivity
  calc ((n + 1 : ℕ) : ℝ) * (2 * (κ⁻¹ ^ n * 2 ^ n) * ((n ! : ℕ) : ℝ) ^ M)
      ≤ 2 ^ n * (2 * (κ⁻¹ ^ n * 2 ^ n) * ((n ! : ℕ) : ℝ) ^ M) :=
        mul_le_mul_of_nonneg_right hn2 hP
    _ = 2 * (4 * κ⁻¹) ^ n * ((n ! : ℕ) : ℝ) ^ M := by
        rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]; ring

end GevreyEdge
