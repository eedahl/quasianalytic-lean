import QuasianalyticLean.GevreyEdge.Defs

/-!
# P2: derivative bounds for `ψ_w` and `h_w`

Complex-analytic proof: `h_w` is the restriction of the holomorphic function
`z ↦ (1 + zᵏ w / c)^(-1-1/k)`, which is bounded by `2^(1+1/k)` on every disc of radius
`κ (1+w)^{-1/k}` about a point of `[0, ∞)`; Cauchy's estimate gives the bound for `h_w`, and
`ψ_w' = h_w` gives the bound for `ψ_w`.
-/

open Set Real Filter Topology MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

/-- `‖(1+u)^n - 1‖ ≤ (1+‖u‖)^n - 1`. -/
lemma P2_norm_one_add_pow_sub_one_le (u : ℂ) :
    ∀ n : ℕ, ‖(1 + u) ^ n - 1‖ ≤ (1 + ‖u‖) ^ n - 1
  | 0 => by simp
  | n + 1 => by
    have ih := P2_norm_one_add_pow_sub_one_le u n
    have h1 : ‖1 + u‖ ≤ 1 + ‖u‖ := by
      calc ‖1 + u‖ ≤ ‖(1 : ℂ)‖ + ‖u‖ := norm_add_le _ _
        _ = 1 + ‖u‖ := by simp
    have : (1 + u) ^ (n + 1) - 1 = (1 + u) * ((1 + u) ^ n - 1) + u := by ring
    rw [this]
    calc ‖(1 + u) * ((1 + u) ^ n - 1) + u‖ ≤ ‖1 + u‖ * ‖(1 + u) ^ n - 1‖ + ‖u‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
      _ ≤ (1 + ‖u‖) * ((1 + ‖u‖) ^ n - 1) + ‖u‖ := by
          gcongr
      _ = (1 + ‖u‖) ^ (n + 1) - 1 := by ring

/-- The uniform radius for the model function `(1 + zᵏ)`. -/
def P2r0 (k : ℕ) : ℝ := min (1 / 4) (Real.log 2 / (4 * k))

lemma P2r0_pos {k : ℕ} (hk : 1 ≤ k) : 0 < P2r0 k := by
  have : (0 : ℝ) < k := by exact_mod_cast hk
  unfold P2r0
  exact lt_min (by norm_num) (div_pos (Real.log_pos (by norm_num)) (by positivity))

/-- Geometry: on the closed disc of radius `P2r0 k` about a point of `[0,∞)`,
`Re (1 + zᵏ) ≥ 1/2`. -/
lemma P2_key_re {k : ℕ} (hk : 1 ≤ k) (z : ℂ) (s : ℝ) (hs : 0 ≤ s)
    (hz : ‖z - s‖ ≤ P2r0 k) : 1 / 2 ≤ (1 + z ^ k).re := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hr1 : P2r0 k ≤ 1 / 4 := min_le_left _ _
  have hr2 : P2r0 k ≤ Real.log 2 / (4 * k) := min_le_right _ _
  rw [Complex.add_re, Complex.one_re]
  rcases le_or_gt s (1 / 4) with hs4 | hs4
  · -- small `s`: `‖z‖ ≤ 1/2`
    have hzn : ‖z‖ ≤ 1 / 2 := by
      calc ‖z‖ = ‖(z - s) + (s : ℂ)‖ := by ring_nf
        _ ≤ ‖z - s‖ + ‖(s : ℂ)‖ := norm_add_le _ _
        _ ≤ 1 / 4 + 1 / 4 := by
          gcongr
          · exact hz.trans hr1
          · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs]; exact hs4
        _ = 1 / 2 := by norm_num
    have hzk : ‖z ^ k‖ ≤ 1 / 2 := by
      rw [norm_pow]
      calc ‖z‖ ^ k ≤ (1 / 2) ^ k := pow_le_pow_left₀ (norm_nonneg _) hzn k
        _ ≤ (1 / 2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
        _ = 1 / 2 := by norm_num
    have := Complex.abs_re_le_norm (z ^ k)
    have := neg_abs_le (z ^ k).re
    linarith
  · -- large `s`: write `z = s (1 + u)` with `‖u‖ ≤ log 2 / k`
    have hs0 : 0 < s := by linarith
    set u : ℂ := (z - s) / s with hu
    have hzu : z = (s : ℂ) * (1 + u) := by
      have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      rw [hu]; field_simp; ring
    have hun : ‖u‖ ≤ Real.log 2 / k := by
      rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0, div_le_iff₀ hs0]
      calc ‖z - s‖ ≤ Real.log 2 / (4 * k) := hz.trans hr2
        _ = Real.log 2 / k * (1 / 4) := by field_simp
        _ ≤ Real.log 2 / k * s := by
          gcongr
    have hpow : (1 + ‖u‖) ^ k ≤ 2 := by
      calc (1 + ‖u‖) ^ k ≤ (Real.exp ‖u‖) ^ k := by
            gcongr
            linarith [Real.add_one_le_exp ‖u‖]
        _ = Real.exp (k * ‖u‖) := by rw [← Real.exp_nat_mul]
        _ ≤ Real.exp (Real.log 2) := by
            gcongr
            rw [le_div_iff₀ hkpos] at hun
            linarith
        _ = 2 := Real.exp_log (by norm_num)
    have hre : 0 ≤ ((1 + u) ^ k).re := by
      have h1 := P2_norm_one_add_pow_sub_one_le u k
      have h2 := Complex.abs_re_le_norm ((1 + u) ^ k - 1)
      have h3 := neg_abs_le ((1 + u) ^ k - 1).re
      rw [Complex.sub_re, Complex.one_re] at h2 h3
      linarith
    have : (z ^ k).re = s ^ k * ((1 + u) ^ k).re := by
      rw [hzu, mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rw [this]
    have : 0 ≤ s ^ k * ((1 + u) ^ k).re := mul_nonneg (pow_nonneg hs0.le k) hre
    linarith

/-- Real part of the real restriction of a holomorphic function commutes with `iteratedDeriv`. -/
lemma P2_iteratedDeriv_re {F : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V) (hF : AnalyticOnNhd ℂ F V) :
    ∀ m : ℕ, ∀ x : ℝ, (x : ℂ) ∈ V →
      iteratedDeriv m (fun t : ℝ => (F t).re) x = (iteratedDeriv m F x).re := by
  have hW : IsOpen ((fun t : ℝ => (t : ℂ)) ⁻¹' V) := hV.preimage Complex.continuous_ofReal
  intro m
  induction m with
  | zero => intro x _; simp
  | succ m ih =>
    intro x hx
    have hev : iteratedDeriv m (fun t : ℝ => (F t).re) =ᶠ[𝓝 x]
        fun t : ℝ => (iteratedDeriv m F t).re := by
      filter_upwards [hW.mem_nhds (show x ∈ (fun t : ℝ => (t : ℂ)) ⁻¹' V from hx)] with t ht
      exact ih t ht
    rw [iteratedDeriv_succ, hev.deriv_eq]
    have hd : HasDerivAt (iteratedDeriv m F) (iteratedDeriv (m + 1) F x) x := by
      rw [iteratedDeriv_succ]
      rw [iteratedDeriv_eq_iterate]
      exact ((hF.iterated_deriv m) x hx).differentiableAt.hasDerivAt
    exact hd.real_of_complex.deriv

/-- `ψ_w' = h_w` on `(0, ∞)`. -/
lemma P2_hasDerivAt_psi {k : ℕ} (hk : 1 ≤ k) {c w : ℝ} (hc : 0 < c) (hw0 : 0 ≤ w) {t : ℝ}
    (ht : 0 < t) : HasDerivAt (ψ k c w) (hw k c w t) t := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hB : 0 < 1 + t ^ (j + 1) * w / c := by positivity
  have hBd : HasDerivAt (fun y => 1 + y ^ (j + 1) * w / c)
      (((j + 1 : ℕ) : ℝ) * t ^ j * w / c) t := by
    have := (((hasDerivAt_pow (j + 1) t).mul_const w).div_const c).const_add 1
    simpa using this
  have h2 : HasDerivAt (fun y => y * (1 + y ^ (j + 1) * w / c) ^ (-(1 : ℝ) / ((j + 1 : ℕ) : ℝ)))
      _ t := (hasDerivAt_id' t).mul
    (hBd.rpow_const (p := -(1 : ℝ) / ((j + 1 : ℕ) : ℝ)) (Or.inl hB.ne'))
  unfold ψ hw
  refine h2.congr_deriv ?_
  set B := 1 + t ^ (j + 1) * w / c with hBdef
  have hk0 : ((j + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have e1 : B ^ (-(1 : ℝ) / ((j + 1 : ℕ) : ℝ)) =
      B ^ (-1 - (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) * B := by
    rw [← Real.rpow_add_one hB.ne']; congr 1; ring
  have e2 : B ^ (-(1 : ℝ) / ((j + 1 : ℕ) : ℝ) - 1) =
      B ^ (-1 - (1 : ℝ) / ((j + 1 : ℕ) : ℝ)) := by
    congr 1; ring
  rw [e1, e2]
  set q := B ^ (-1 - (1 : ℝ) / ((j + 1 : ℕ) : ℝ))
  rw [hBdef]
  field_simp
  ring

/-- Cauchy estimate for `h_w` at a point `y ≥ 0`, on any disc of radius `ρ` with
`(w/c)^{1/k} ρ ≤ P2r0 k`. -/
lemma P2_hw_bound {k : ℕ} (hk : 1 ≤ k) {c w : ℝ} (hc : 0 < c) (hw0 : 0 ≤ w) {y : ℝ}
    (hy : 0 ≤ y) {ρ : ℝ} (hρ : 0 < ρ) (hρr : (w / c) ^ (1 / (k : ℝ)) * ρ ≤ P2r0 k) (m : ℕ) :
    |iteratedDeriv m (hw k c w) y| ≤
      (1 / 2 : ℝ) ^ (-1 - 1 / (k : ℝ)) * (m ! : ℕ) * (ρ⁻¹) ^ m := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  set l := (w / c) ^ (1 / (k : ℝ)) with hl
  have hl0 : 0 ≤ l := Real.rpow_nonneg (div_nonneg hw0 hc.le) _
  have hlk : (l : ℂ) ^ k = ((w / c : ℝ) : ℂ) := by
    rw [← Complex.ofReal_pow, hl, one_div,
      Real.rpow_inv_natCast_pow (div_nonneg hw0 hc.le) (by omega)]
  set M : ℝ := (1 / 2 : ℝ) ^ (-1 - 1 / (k : ℝ)) with hM
  have hexp : (-1 - 1 / (k : ℝ)) ≤ 0 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  let F : ℂ → ℂ := fun z => (1 + z ^ k * w / c) ^ (((-1 - 1 / (k : ℝ)) : ℝ) : ℂ)
  let V : Set ℂ := {z : ℂ | 0 < (1 + z ^ k * w / c).re}
  have hV : IsOpen V := isOpen_lt continuous_const (by fun_prop)
  have hFd : DifferentiableOn ℂ F V := fun z hz =>
    (DifferentiableAt.cpow_const (f := fun z : ℂ => 1 + z ^ k * w / c) (by fun_prop)
      (Complex.mem_slitPlane_iff.2 (Or.inl hz))).differentiableWithinAt
  have hball : ∀ z ∈ Metric.closedBall (y : ℂ) ρ, 1 / 2 ≤ (1 + z ^ k * w / c).re := by
    intro z hz
    have e : z ^ k * w / c = ((l : ℂ) * z) ^ k := by
      rw [mul_pow, hlk]; push_cast; ring
    rw [e]
    apply P2_key_re hk _ (l * y) (mul_nonneg hl0 hy)
    rw [Complex.ofReal_mul, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hl0]
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    calc l * ‖z - y‖ ≤ l * ρ := mul_le_mul_of_nonneg_left hz hl0
      _ ≤ P2r0 k := hρr
  have hyV : (y : ℂ) ∈ V := by
    have := hball y (Metric.mem_closedBall_self hρ.le)
    exact lt_of_lt_of_le (by norm_num) this
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le m hρ (f := F) (c := (y : ℂ))
    (C := M)
    (DifferentiableOn.diffContOnCl (hFd.mono (by
      rw [closure_ball _ hρ.ne']
      intro z hz
      have := hball z hz
      exact lt_of_lt_of_le (by norm_num) this)))
    (by
      intro z hz
      have hz' := hball z (Metric.sphere_subset_closedBall hz)
      simp only [F]
      rw [Complex.norm_cpow_real]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num)
        (hz'.trans (Complex.re_le_norm _)) hexp)
  have hW : IsOpen ((fun t : ℝ => (t : ℂ)) ⁻¹' V) := hV.preimage Complex.continuous_ofReal
  have hev : hw k c w =ᶠ[𝓝 y] fun t : ℝ => (F t).re := by
    filter_upwards [hW.mem_nhds (show y ∈ (fun t : ℝ => (t : ℂ)) ⁻¹' V from hyV)] with t ht
    have e : (1 + (t : ℂ) ^ k * w / c) = ((1 + t ^ k * w / c : ℝ) : ℂ) := by push_cast; ring
    have ht' : 0 < (1 + (t : ℂ) ^ k * w / c).re := ht
    rw [e, Complex.ofReal_re] at ht'
    simp only [F]
    rw [e, ← Complex.ofReal_cpow ht'.le, Complex.ofReal_re]
    rfl
  rw [hev.iteratedDeriv_eq, P2_iteratedDeriv_re hV (hFd.analyticOnNhd hV) m y hyV]
  refine (Complex.abs_re_le_norm _).trans (hC.trans (le_of_eq ?_))
  rw [inv_pow, div_eq_mul_inv]
  ring

/-- **P2.** Derivative bounds for the inner map and the weight, uniform in `y ∈ (0, δ)`. -/
theorem P2_psi_hw_bounds {k : ℕ} (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ κ M : ℝ, 0 < κ ∧ κ ≤ 1 ∧ 1 ≤ M ∧ ∀ w : ℝ, 0 ≤ w → ∀ y ∈ Ioo 0 δ,
      ContDiffAt ℝ ∞ (ψ k c w) y ∧ ContDiffAt ℝ ∞ (hw k c w) y ∧
      ψ k c w y ∈ Ioo 0 δ ∧
      (∀ m : ℕ, 1 ≤ m → |iteratedDeriv m (ψ k c w) y| ≤
          M * (m ! : ℕ) * ((κ * (1 + w) ^ (-(1 : ℝ) / k))⁻¹) ^ (m - 1)) ∧
      (∀ m : ℕ, |iteratedDeriv m (hw k c w) y| ≤
          M * (m ! : ℕ) * ((κ * (1 + w) ^ (-(1 : ℝ) / k))⁻¹) ^ m) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hr0 := P2r0_pos hk
  have hκ : 0 < min 1 (P2r0 k * c ^ (1 / (k : ℝ))) :=
    lt_min one_pos (mul_pos hr0 (Real.rpow_pos_of_pos hc _))
  have hexp : (-1 - 1 / (k : ℝ)) ≤ 0 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  refine ⟨min 1 (P2r0 k * c ^ (1 / (k : ℝ))), (1 / 2 : ℝ) ^ (-1 - 1 / (k : ℝ)), hκ,
    min_le_left _ _, Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by norm_num) (by norm_num) hexp,
    ?_⟩
  intro w hw0 y hy
  set κ := min 1 (P2r0 k * c ^ (1 / (k : ℝ))) with hκdef
  set M : ℝ := (1 / 2 : ℝ) ^ (-1 - 1 / (k : ℝ)) with hM
  have hB : ∀ t : ℝ, 0 ≤ t → 1 ≤ 1 + t ^ k * w / c := fun t ht => by
    have : 0 ≤ t ^ k * w / c := by positivity
    linarith
  set ρ := κ * (1 + w) ^ (-(1 : ℝ) / k) with hρdef
  have hρ : 0 < ρ := mul_pos hκ (Real.rpow_pos_of_pos (by linarith) _)
  have hρr : (w / c) ^ (1 / (k : ℝ)) * ρ ≤ P2r0 k := by
    have h1 : (w / c) ^ (1 / (k : ℝ)) * c ^ (1 / (k : ℝ)) = w ^ (1 / (k : ℝ)) := by
      rw [← Real.mul_rpow (div_nonneg hw0 hc.le) hc.le, div_mul_cancel₀ _ hc.ne']
    have h2 : w ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k) ≤ 1 := by
      calc w ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k)
          ≤ (1 + w) ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hw0 (by linarith) (by positivity))
              (Real.rpow_nonneg (by linarith) _)
        _ = 1 := by
            rw [← Real.rpow_add (by linarith), show (1 : ℝ) / k + -(1 : ℝ) / k = 0 by ring,
              Real.rpow_zero]
    have hn1 : 0 ≤ (w / c) ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k) :=
      mul_nonneg (Real.rpow_nonneg (div_nonneg hw0 hc.le) _) (Real.rpow_nonneg (by linarith) _)
    calc (w / c) ^ (1 / (k : ℝ)) * ρ
        = κ * ((w / c) ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k)) := by rw [hρdef]; ring
      _ ≤ (P2r0 k * c ^ (1 / (k : ℝ))) *
          ((w / c) ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hn1
      _ = P2r0 k * (((w / c) ^ (1 / (k : ℝ)) * c ^ (1 / (k : ℝ))) *
          (1 + w) ^ (-(1 : ℝ) / k)) := by ring
      _ = P2r0 k * (w ^ (1 / (k : ℝ)) * (1 + w) ^ (-(1 : ℝ) / k)) := by rw [h1]
      _ ≤ P2r0 k * 1 := mul_le_mul_of_nonneg_left h2 hr0.le
      _ = P2r0 k := mul_one _
  have hhw : ∀ m : ℕ, |iteratedDeriv m (hw k c w) y| ≤ M * (m ! : ℕ) * (ρ⁻¹) ^ m :=
    P2_hw_bound hk hc hw0 hy.1.le hρ hρr
  have hBy := hB y hy.1.le
  have hBc : ContDiffAt ℝ ∞ (fun t : ℝ => 1 + t ^ k * w / c) y := by fun_prop
  refine ⟨?_, ?_, ?_, ?_, hhw⟩
  · unfold ψ
    exact contDiffAt_id.mul (hBc.rpow_const_of_ne (by linarith))
  · unfold hw
    exact hBc.rpow_const_of_ne (by linarith)
  · have hp : (1 + y ^ k * w / c) ^ (-(1 : ℝ) / k) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hBy
        (by rw [neg_div]; have : 0 ≤ 1 / (k : ℝ) := by positivity
            linarith)
    have hp0 : 0 < (1 + y ^ k * w / c) ^ (-(1 : ℝ) / k) := Real.rpow_pos_of_pos (by linarith) _
    unfold ψ
    exact ⟨mul_pos hy.1 hp0, lt_of_le_of_lt (mul_le_of_le_one_right hy.1.le hp) hy.2⟩
  · intro m hm
    obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
    have hev : deriv (ψ k c w) =ᶠ[𝓝 y] hw k c w := by
      filter_upwards [Ioi_mem_nhds hy.1] with t ht
      exact (P2_hasDerivAt_psi hk hc hw0 ht).deriv
    rw [iteratedDeriv_succ', hev.iteratedDeriv_eq, Nat.add_sub_cancel]
    refine (hhw n).trans ?_
    have hX : 0 ≤ (ρ⁻¹) ^ n := pow_nonneg (inv_nonneg.2 hρ.le) n
    have hM0 : 0 ≤ M := Real.rpow_nonneg (by norm_num) _
    have hf : ((n ! : ℕ) : ℝ) ≤ (((n + 1) ! : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hM0) hX

end GevreyEdge
