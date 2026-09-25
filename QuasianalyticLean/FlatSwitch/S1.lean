import QuasianalyticLean.FlatSwitch.Defs

/-!
# Doubly exponential switch, component S1: the switch is small on shrinking discs

On `D(y, κ y^{1+γ})` with `0 < y ≤ 1`, write `z = y(1+ε)` with `|ε| ≤ κ y^γ ≤ κ`. Then
`c z^{-γ} = c y^{-γ}(1+ε)^{-γ}`: its imaginary part is `O(cγκ)`, so `φ(z) = exp(c z^{-γ})` has
argument `< π/4` for small κ, and `|φ(z)| ≥ φ(y) e^{-O(cγκ)}`; hence
`Re(-θ φ(z)) ≤ -θ φ(y)/2`.
-/

open Set Real
open scoped Nat

noncomputable section

namespace FlatSwitch

theorem S1_disc {c γ θ : ℝ} (hc : 0 < c) (hγ : 0 < γ) (hθ : 0 < θ) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1 / 2 ∧ ∀ y : ℝ, 0 < y → y ≤ 1 → ∀ z : ℂ,
      ‖z - y‖ ≤ κ * y ^ (1 + γ) →
        ‖switchC c γ θ z‖ ≤ Real.exp (-(θ / 2) * Real.exp (c * y ^ (-γ))) := by
  set K : ℝ := 12 * c * γ + 3 * γ + 2 with hKdef
  have hcγ : 0 < c * γ := mul_pos hc hγ
  have hK : 0 < K := by positivity
  have hK2 : 1 / K ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hK (by norm_num)]; nlinarith
  refine ⟨1 / K, by positivity, hK2, ?_⟩
  intro y hy hy1 z hz
  have hyγ : y ^ γ ≤ 1 := Real.rpow_le_one hy.le hy1 hγ.le
  have hyγpos : 0 < y ^ γ := Real.rpow_pos_of_pos hy γ
  have hY : (y : ℂ) ≠ 0 := by exact_mod_cast hy.ne'
  set ε : ℂ := z / y - 1 with hε
  have hz_eq : z = (y : ℂ) * (1 + ε) := by rw [hε]; field_simp; ring
  have hεn : ‖ε‖ ≤ 1 / K * y ^ γ := by
    have : ε = (z - y) / y := by rw [hε]; field_simp
    rw [this, norm_div, Complex.norm_real, Real.norm_of_nonneg hy.le, div_le_iff₀ hy]
    calc ‖z - y‖ ≤ 1 / K * y ^ (1 + γ) := hz
      _ = 1 / K * y ^ γ * y := by rw [Real.rpow_add hy, Real.rpow_one]; ring
  have hK0 : 0 ≤ 1 / K := by positivity
  have hεK : ‖ε‖ ≤ 1 / K := hεn.trans (by nlinarith)
  have hε2 : ‖ε‖ ≤ 1 / 2 := hεK.trans hK2
  have h1ε : (1 + ε) ≠ 0 := by
    intro h
    have : ε = -1 := by linear_combination h
    rw [this] at hε2; norm_num at hε2
  set L := Complex.log (1 + ε) with hLdef
  have hL : ‖L‖ ≤ 3 / 2 * ‖ε‖ := Complex.norm_log_one_add_half_le_self hε2
  have hγL : ‖L * (-(γ : ℂ))‖ ≤ 1 := by
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hγ.le]
    calc ‖L‖ * γ ≤ 3 / 2 * (1 / K) * γ := by gcongr; nlinarith
      _ = (3 / 2 * γ) / K := by ring
      _ ≤ 1 := by rw [div_le_one hK]; nlinarith
  set w := Complex.exp (L * (-(γ : ℂ))) - 1 with hwdef
  have hw : ‖w‖ ≤ 3 * γ * ‖ε‖ := by
    have h1 := Complex.norm_exp_sub_one_le hγL
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg hγ.le] at h1
    nlinarith
  set A : ℝ := c * y ^ (-γ) with hAdef
  have hA : 0 < A := by positivity
  have hcz : (c : ℂ) * z ^ (-(γ : ℂ)) = (A : ℂ) + A * w := by
    have hz0 : z ≠ 0 := by rw [hz_eq]; exact mul_ne_zero hY h1ε
    rw [Complex.cpow_def_of_ne_zero hz0, hz_eq, Complex.log_ofReal_mul hy h1ε, ← hLdef,
      add_mul, Complex.exp_add, hAdef, Real.rpow_def_of_pos hy, hwdef]
    push_cast
    ring
  set u : ℂ := (A : ℂ) * w with hudef
  have hu : ‖u‖ ≤ 1 / 4 := by
    rw [hudef, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA.le]
    have hyy : y ^ (-γ) * y ^ γ = 1 := by
      rw [Real.rpow_neg hy.le, inv_mul_cancel₀ hyγpos.ne']
    have hypos' : 0 < y ^ (-γ) := Real.rpow_pos_of_pos hy _
    calc A * ‖w‖ ≤ A * (3 * γ * (1 / K * y ^ γ)) := by gcongr; nlinarith [norm_nonneg ε]
      _ = 3 * (c * γ) / K * (y ^ (-γ) * y ^ γ) := by rw [hAdef]; ring
      _ = 3 * (c * γ) / K := by rw [hyy, mul_one]
      _ ≤ 1 / 4 := by rw [div_le_iff₀ hK]; nlinarith
  have hre : 1 / 2 ≤ (Complex.exp u).re := by
    have h1 := Complex.norm_exp_sub_one_le (hu.trans (by norm_num))
    have h2 := (abs_le.mp (Complex.abs_re_le_norm (Complex.exp u - 1))).1
    rw [Complex.sub_re, Complex.one_re] at h2
    linarith
  unfold switchC
  rw [hcz, Complex.norm_exp, Complex.exp_add, ← Complex.ofReal_exp]
  have : (-(θ : ℂ) * (↑(Real.exp A) * Complex.exp u)) = ((-θ * Real.exp A : ℝ) : ℂ) * Complex.exp u := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul, Real.exp_le_exp]
  have hEA : 0 < θ * Real.exp A := by positivity
  nlinarith

end FlatSwitch
