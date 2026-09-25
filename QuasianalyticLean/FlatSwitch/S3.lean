import QuasianalyticLean.FlatSwitch.Defs

/-!
# Doubly exponential switch, component S3: the supremum over the edge distance

With `Y = y^{-γ}`, `a = 1+1/γ` and `L = log(e+n)`, `y^{-(1+γ)n} = (Y^a)^n`, and
`(Y^a)^n e^{-(θ/2)e^{cY}} ≤ K^n (L^a)^n` (`S3_key`): for `Y ≤ 2L/c` directly; for
`Y > 2L/c`, `u = e^{cY/2} ≥ e+n ≥ n`, so `e^{-(θ/2)e^{cY}} ≤ (e^{-θu/2})^n`,
`Y^a ≤ (2a/c)^a u` and `u e^{-θu/2} ≤ 2/θ`.
-/

open Set Real
open scoped Nat

noncomputable section

namespace FlatSwitch

theorem S3_key {c θ a : ℝ} (hc : 0 < c) (hθ : 0 < θ) (ha : 0 < a) (n : ℕ) {Y : ℝ}
    (hY : 0 < Y) :
    (Y ^ a) ^ n * Real.exp (-(θ / 2) * Real.exp (c * Y)) ≤
      ((2 * a / c) ^ a * (2 / θ) + (2 / c) ^ a) ^ n * (Real.log (Real.exp 1 + n) ^ a) ^ n := by
  set L := Real.log (Real.exp 1 + n) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity)]
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hK1 : 0 ≤ (2 * a / c) ^ a * (2 / θ) := by positivity
  have hK2 : 0 ≤ (2 / c) ^ a := by positivity
  rcases le_or_gt Y (2 / c * L) with h | h
  · calc (Y ^ a) ^ n * Real.exp (-(θ / 2) * Real.exp (c * Y))
          ≤ (Y ^ a) ^ n * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [Real.exp_le_one_iff]
            have : 0 < Real.exp (c * Y) := Real.exp_pos _
            nlinarith
      _ = (Y ^ a) ^ n := mul_one _
      _ ≤ ((2 / c) ^ a * L ^ a) ^ n := by
            apply pow_le_pow_left₀ (by positivity)
            rw [← Real.mul_rpow (by positivity) (by linarith)]
            exact Real.rpow_le_rpow hY.le h ha.le
      _ ≤ (((2 * a / c) ^ a * (2 / θ) + (2 / c) ^ a) * L ^ a) ^ n := by
            apply pow_le_pow_left₀ (by positivity)
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := mul_pow _ _ _
  · set u := Real.exp (c * Y / 2) with hudef
    have hu0 : 0 < u := Real.exp_pos _
    have hu : Real.exp (c * Y) = u * u := by
      rw [hudef, ← Real.exp_add]; ring_nf
    have hLu : L < c * Y / 2 := by
      have h2 : c * (2 / c * L) = 2 * L := by field_simp
      nlinarith
    have hun : (n : ℝ) ≤ u := by
      have : Real.exp L = Real.exp 1 + n := Real.exp_log (by positivity)
      have h3 : Real.exp L ≤ u := Real.exp_le_exp.mpr hLu.le
      have : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
      linarith
    have hYa : Y ^ a ≤ (2 * a / c) ^ a * u := by
      have h1 : Y ≤ (2 * a / c) * Real.exp (c * Y / (2 * a)) := by
        have := Real.add_one_le_exp (c * Y / (2 * a))
        have h4 : (2 * a / c) * (c * Y / (2 * a)) = Y := by field_simp
        have : (2 * a / c) * (c * Y / (2 * a)) ≤ (2 * a / c) * Real.exp (c * Y / (2 * a)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
      calc Y ^ a ≤ ((2 * a / c) * Real.exp (c * Y / (2 * a))) ^ a :=
            Real.rpow_le_rpow hY.le h1 ha.le
        _ = (2 * a / c) ^ a * u := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.exp_mul, hudef]
            congr 2
            field_simp
    have hexp : Real.exp (-(θ / 2) * Real.exp (c * Y)) ≤ Real.exp (-(θ / 2) * u) ^ n := by
      rw [← Real.exp_nat_mul, Real.exp_le_exp, hu]
      have : θ / 2 * u * n ≤ θ / 2 * u * u :=
        mul_le_mul_of_nonneg_left hun (by positivity)
      nlinarith
    have hue : u * Real.exp (-(θ / 2) * u) ≤ 2 / θ := by
      have h5 := Real.add_one_le_exp (θ / 2 * u)
      have h6 : Real.exp (θ / 2 * u) * Real.exp (-(θ / 2) * u) = 1 := by
        rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
      have h7 : 0 < Real.exp (-(θ / 2) * u) := Real.exp_pos _
      have h8 : θ / 2 * u * Real.exp (-(θ / 2) * u) ≤ 1 := by nlinarith
      rw [le_div_iff₀ hθ]
      nlinarith
    have hLa : 1 ≤ (L ^ a) ^ n := one_le_pow₀ (Real.one_le_rpow hL1 ha.le)
    calc (Y ^ a) ^ n * Real.exp (-(θ / 2) * Real.exp (c * Y))
          ≤ (Y ^ a) ^ n * Real.exp (-(θ / 2) * u) ^ n :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
      _ = (Y ^ a * Real.exp (-(θ / 2) * u)) ^ n := (mul_pow _ _ _).symm
      _ ≤ ((2 * a / c) ^ a * (2 / θ)) ^ n := by
            apply pow_le_pow_left₀ (by positivity)
            calc Y ^ a * Real.exp (-(θ / 2) * u)
                ≤ (2 * a / c) ^ a * u * Real.exp (-(θ / 2) * u) :=
                  mul_le_mul_of_nonneg_right hYa (by positivity)
              _ = (2 * a / c) ^ a * (u * Real.exp (-(θ / 2) * u)) := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left hue (by positivity)
      _ ≤ ((2 * a / c) ^ a * (2 / θ) + (2 / c) ^ a) ^ n :=
            pow_le_pow_left₀ (by positivity) (by linarith) n
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hLa

theorem S3_sup {c γ θ κ : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hθ : 0 < θ) (hκ : 0 < κ) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      n ! * Real.exp (-(θ / 2) * Real.exp (c * y ^ (-γ))) / (κ * y ^ (1 + γ)) ^ n ≤
        C * A ^ n * classM γ n := by
  set a := 1 + 1 / γ with hadef
  have ha : 0 < a := by positivity
  set K := (2 * a / c) ^ a * (2 / θ) + (2 / c) ^ a with hKdef
  have hK : 0 < K := by positivity
  refine ⟨1, K / κ, one_pos, div_pos hK hκ, fun n y hy _ => ?_⟩
  set Y := y ^ (-γ) with hYdef
  have hY : 0 < Y := Real.rpow_pos_of_pos hy _
  have hkey := S3_key hc hθ ha n hY
  set L := Real.log (Real.exp 1 + n) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg (by
    have : (0:ℝ) ≤ n := Nat.cast_nonneg n
    have := Real.add_one_le_exp 1
    linarith)
  have hYa : Y ^ a = (y ^ (1 + γ))⁻¹ := by
    rw [hYdef, ← Real.rpow_mul hy.le, ← Real.rpow_neg hy.le]
    congr 1
    rw [hadef]; field_simp; ring
  have hM : classM γ n = n ! * (L ^ a) ^ n := by
    unfold classM
    rw [← hLdef, ← hadef, Real.rpow_mul hL0, Real.rpow_natCast]
  rw [hM]
  rw [hYa] at hkey
  have hyp : 0 < y ^ (1 + γ) := Real.rpow_pos_of_pos hy _
  have hfac : (0:ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  have e1 : (n ! : ℝ) * Real.exp (-(θ / 2) * Real.exp (c * Y)) / (κ * y ^ (1 + γ)) ^ n =
      n ! * (κ⁻¹) ^ n * (((y ^ (1 + γ))⁻¹) ^ n * Real.exp (-(θ / 2) * Real.exp (c * Y))) := by
    rw [mul_pow, inv_pow, inv_pow]; field_simp
  have e2 : 1 * (K / κ) ^ n * (n ! * (L ^ a) ^ n) =
      n ! * (κ⁻¹) ^ n * (K ^ n * (L ^ a) ^ n) := by
    rw [div_pow, inv_pow]; field_simp
  rw [e1, e2]
  exact mul_le_mul_of_nonneg_left hkey (by positivity)

end FlatSwitch
