import QuasianalyticLean.GevreyEdge.Defs

/-!
# P4: differentiation of `Brep` under the integral sign
-/

open Set Real Filter Topology MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

lemma integrableOn_exp_neg_mul_pow (j : ℕ) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) * w ^ j) (Ioi 0) := by
  have := Real.GammaIntegral_convergent (s := (j : ℝ) + 1) (by positivity)
  refine this.congr_fun (fun w _ => ?_) measurableSet_Ioi
  simp only [add_sub_cancel_right, Real.rpow_natCast]

lemma integrableOn_exp_neg_mul_one_add_pow (m : ℕ) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) * (1 + w) ^ m) (Ioi 0) := by
  have h : (fun w : ℝ => Real.exp (-w) * (1 + w) ^ m) =
      fun w => ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (Real.exp (-w) * w ^ j) := by
    funext w
    rw [add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h]
  exact integrable_finsetSum _ (fun j _ => (integrableOn_exp_neg_mul_pow j).const_mul _)

lemma integrableOn_exp_neg_mul_rho_pow {k : ℕ} (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ) (m : ℕ) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) * (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) ^ m) (Ioi 0) := by
  refine ((integrableOn_exp_neg_mul_one_add_pow m).const_mul (κ⁻¹ ^ m)).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun w : ℝ =>
      Real.exp (-w) * (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) ^ m).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall (fun w hw => ?_)
    have hw0 : 0 ≤ w := le_of_lt hw
    have h1 : (1 + w) ^ ((1 : ℝ) / k) ≤ 1 + w := by
      calc (1 + w) ^ ((1 : ℝ) / k) ≤ (1 + w) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by
              rw [div_le_one (by positivity)]; exact_mod_cast hk)
        _ = 1 + w := Real.rpow_one _
    have h0 : 0 ≤ (1 + w) ^ ((1 : ℝ) / k) := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_pow]
    calc Real.exp (-w) * (κ⁻¹ ^ m * ((1 + w) ^ ((1 : ℝ) / k)) ^ m)
        ≤ Real.exp (-w) * (κ⁻¹ ^ m * (1 + w) ^ m) := by gcongr
      _ = κ⁻¹ ^ m * (Real.exp (-w) * (1 + w) ^ m) := by ring

lemma integrableOn_exp_neg_mul_shape {k : ℕ} (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ) (s : ℝ)
    (n : ℕ) :
    IntegrableOn (fun w : ℝ => Real.exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n)
      (Ioi 0) := by
  have h : (fun w : ℝ => Real.exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n) =
      fun w => ∑ j ∈ Finset.range (n + 1), (((j ! : ℕ) : ℝ) ^ s * (((n - j) ! : ℕ) : ℝ)) *
        (Real.exp (-w) * (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) ^ (n - j)) := by
    funext w
    rw [shape, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [h]
  exact integrable_finsetSum _
    (fun j _ => (integrableOn_exp_neg_mul_rho_pow hk hκ (n - j)).const_mul _)

lemma hasDerivAt_iteratedDeriv_of_contDiffAt {f : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U)
    (hf : ∀ y ∈ U, ContDiffAt ℝ ∞ f y) (n : ℕ) {y : ℝ} (hy : y ∈ U) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f y) y := by
  have hfo : ContDiffOn ℝ ∞ f U := fun x hx => (hf x hx).contDiffWithinAt
  have hd : DifferentiableOn ℝ (iteratedDerivWithin n f U) U :=
    hfo.differentiableOn_iteratedDerivWithin (by exact_mod_cast ENat.natCast_lt_top n) hU.uniqueDiffOn
  have hd' : DifferentiableAt ℝ (iteratedDeriv n f) y := by
    have := (hd y hy).differentiableAt (hU.mem_nhds hy)
    exact this.congr_of_eventuallyEq (Filter.eventually_of_mem (hU.mem_nhds hy)
      (fun x hx => (iteratedDerivWithin_of_isOpen hU hx).symm))
  rw [iteratedDeriv_succ]
  exact hd'.hasDerivAt

/-- Measurability in `w` of the `y`-derivatives of the integrand. -/
lemma aestronglyMeasurable_iteratedDeriv_integrand {k : ℕ} {c δ : ℝ} (hc : 0 < c)
    {b : ℝ → ℝ} (hbc : ContDiffOn ℝ ∞ b (Ioo 0 δ))
    (hsm : ∀ w : ℝ, 0 ≤ w → ∀ y ∈ Ioo 0 δ, ContDiffAt ℝ ∞ (integrand k c b w) y) :
    ∀ n : ℕ, ∀ y ∈ Ioo 0 δ, AEStronglyMeasurable
      (fun w => iteratedDeriv n (integrand k c b w) y) (volume.restrict (Ioi 0)) := by
  intro n
  induction n with
  | zero =>
    intro y hy
    simp only [iteratedDeriv_zero]
    have hbase : ∀ w : ℝ, 0 ≤ w → 1 ≤ 1 + y ^ k * w / c := fun w hw => by
      have : 0 ≤ y ^ k * w / c := div_nonneg (mul_nonneg (pow_nonneg hy.1.le _) hw) hc.le
      linarith
    have hψ : ContinuousOn (fun w => ψ k c w y) (Ioi 0) := by
      unfold ψ
      exact continuousOn_const.mul (ContinuousOn.rpow_const (by fun_prop)
        (fun w hw => Or.inl (by linarith [hbase w (le_of_lt hw)] : (0:ℝ) < _).ne'))
    have hh : ContinuousOn (fun w => hw k c w y) (Ioi 0) := by
      unfold hw
      exact ContinuousOn.rpow_const (by fun_prop)
        (fun w hw => Or.inl (by linarith [hbase w (le_of_lt hw)] : (0:ℝ) < _).ne')
    have hmaps : MapsTo (fun w => ψ k c w y) (Ioi 0) (Ioo 0 δ) := by
      intro w hw
      have hb1 := hbase w (le_of_lt hw)
      have hr0 : 0 < (1 + y ^ k * w / c) ^ (-(1 : ℝ) / k) := Real.rpow_pos_of_pos (by linarith) _
      have hr1 : (1 + y ^ k * w / c) ^ (-(1 : ℝ) / k) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hb1
          (div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg k))
      simp only [ψ, mem_Ioo]
      constructor
      · exact mul_pos hy.1 hr0
      · calc y * (1 + y ^ k * w / c) ^ (-(1 : ℝ) / k) ≤ y := mul_le_of_le_one_right hy.1.le hr1
          _ < δ := hy.2
    have hcont : ContinuousOn (fun w => integrand k c b w y) (Ioi 0) :=
      (hbc.continuousOn.comp hψ hmaps).mul hh
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  | succ n ih =>
    intro y hy
    set ε := δ - y with hε
    have hεpos : 0 < ε := by simp only [hε]; linarith [hy.2]
    let h : ℕ → ℝ := fun j => ε / ((j : ℝ) + 2)
    have hpos : ∀ j, 0 < h j := fun j => div_pos hεpos (by positivity)
    have hlt : ∀ j, h j < ε := fun j => by
      show ε / ((j : ℝ) + 2) < ε
      rw [div_lt_iff₀ (by positivity)]
      have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      nlinarith
    have hmem : ∀ j, y + h j ∈ Ioo 0 δ := fun j =>
      ⟨by linarith [hy.1, hpos j], by linarith [hlt j]⟩
    have htend : Tendsto h atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall (fun j => (hpos j).ne')⟩
      exact Tendsto.div_atTop tendsto_const_nhds
        (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun j w => (h j)⁻¹ * (iteratedDeriv n (integrand k c b w) (y + h j) -
        iteratedDeriv n (integrand k c b w) y)) (fun j => ?_) ?_
    · exact ((ih _ (hmem j)).sub (ih y hy)).const_mul _
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall (fun w hw => ?_)
      have hd := hasDerivAt_iteratedDeriv_of_contDiffAt isOpen_Ioo
        (fun x hx => hsm w (le_of_lt hw) x hx) n hy
      exact hd.tendsto_slope_zero.comp htend

/-- **P4.** Differentiation under the integral sign. If every `y`-derivative of the integrand is
dominated by `e^{w}·G_n(w)` with `∫ e^{-w}·e^{w}G_n`... stated concretely with the shape bound. -/
theorem P4_iteratedDeriv_Brep {k : ℕ} (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    {b : ℝ → ℝ} (hbc : ContDiffOn ℝ ∞ b (Ioo 0 δ))
    {κ B E s : ℝ} (hκ : 0 < κ) (hB : 0 ≤ B) (hE : 0 ≤ E)
    (hsm : ∀ w : ℝ, 0 ≤ w → ∀ y ∈ Ioo 0 δ, ContDiffAt ℝ ∞ (integrand k c b w) y)
    (hbound : ∀ n : ℕ, ∀ w : ℝ, 0 ≤ w → ∀ y ∈ Ioo 0 δ,
      |iteratedDeriv n (integrand k c b w) y| ≤ B * E ^ n * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n) :
    ContDiffOn ℝ ∞ (Brep k c b) (Ioo 0 δ) ∧ ∀ n : ℕ, ∀ y ∈ Ioo 0 δ,
      |iteratedDeriv n (Brep k c b) y| ≤ |(c * k)⁻¹| * B * E ^ n *
        ∫ w in Ioi (0 : ℝ), Real.exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n := by
  set U := Ioo (0 : ℝ) δ with hU_def
  have hU : IsOpen U := isOpen_Ioo
  let I : ℕ → ℝ → ℝ := fun n y =>
    ∫ w in Ioi (0 : ℝ), Real.exp (-w) * iteratedDeriv n (integrand k c b w) y
  let G : ℕ → ℝ → ℝ := fun n w =>
    Real.exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n
  have hGint : ∀ n, Integrable (fun w => B * E ^ n * G n w) (volume.restrict (Ioi 0)) :=
    fun n => (integrableOn_exp_neg_mul_shape hk hκ s n).const_mul _
  have hmeas' : ∀ n, ∀ y ∈ U, AEStronglyMeasurable
      (fun w => Real.exp (-w) * iteratedDeriv n (integrand k c b w) y)
      (volume.restrict (Ioi 0)) := fun n y hy =>
    (Real.continuous_exp.comp continuous_neg).aestronglyMeasurable.mul
      (aestronglyMeasurable_iteratedDeriv_integrand hc hbc hsm n y hy)
  have hbnd : ∀ n, ∀ w : ℝ, 0 < w → ∀ y ∈ U,
      ‖Real.exp (-w) * iteratedDeriv n (integrand k c b w) y‖ ≤ B * E ^ n * G n w := by
    intro n w hw y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-w) * |iteratedDeriv n (integrand k c b w) y|
        ≤ Real.exp (-w) * (B * E ^ n * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n) :=
          mul_le_mul_of_nonneg_left (hbound n w hw.le y hy) (Real.exp_pos _).le
      _ = B * E ^ n * G n w := by simp only [G]; ring
  have hbnd' : ∀ n, ∀ y ∈ U, ∀ᵐ w ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖Real.exp (-w) * iteratedDeriv n (integrand k c b w) y‖ ≤ B * E ^ n * G n w := by
    intro n y hy
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall (fun w hw => hbnd n w hw y hy)
  have hint : ∀ n, ∀ y ∈ U, Integrable
      (fun w => Real.exp (-w) * iteratedDeriv n (integrand k c b w) y)
      (volume.restrict (Ioi 0)) :=
    fun n y hy => (hGint n).mono' (hmeas' n y hy) (hbnd' n y hy)
  have hderiv : ∀ n, ∀ y ∈ U, HasDerivAt (I n) (I (n + 1) y) y := by
    intro n y hy
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Ioi 0))
      (F := fun x w => Real.exp (-w) * iteratedDeriv n (integrand k c b w) x)
      (F' := fun x w => Real.exp (-w) * iteratedDeriv (n + 1) (integrand k c b w) x)
      (x₀ := y) (bound := fun w => B * E ^ (n + 1) * G (n + 1) w) (hU.mem_nhds hy)
      (Filter.eventually_of_mem (hU.mem_nhds hy) (fun x hx => hmeas' n x hx)) (hint n y hy)
      (hmeas' (n + 1) y hy) ?_ (hGint (n + 1)) ?_
    · exact this.2
    · rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall (fun w hw x hx => hbnd (n + 1) w hw x hx)
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall (fun w hw x hx => ?_)
      exact (hasDerivAt_iteratedDeriv_of_contDiffAt hU
        (fun z hz => hsm w (le_of_lt hw) z hz) n hx).const_mul _
  have hiter : ∀ n, ∀ y ∈ U, iteratedDeriv n (Brep k c b) y = (c * k)⁻¹ * I n y := by
    intro n
    induction n with
    | zero => intro y _; simp [Brep, I]
    | succ n ih =>
      intro y hy
      rw [iteratedDeriv_succ]
      have heq : iteratedDeriv n (Brep k c b) =ᶠ[𝓝 y] fun x => (c * k)⁻¹ * I n x :=
        Filter.eventually_of_mem (hU.mem_nhds hy) ih
      rw [heq.deriv_eq]
      exact ((hderiv n y hy).const_mul _).deriv
  refine ⟨?_, ?_⟩
  · apply contDiffOn_of_differentiableOn_deriv
    intro m _ y hy
    have h1 : DifferentiableAt ℝ (iteratedDeriv m (Brep k c b)) y := by
      have heq : iteratedDeriv m (Brep k c b) =ᶠ[𝓝 y] fun x => (c * k)⁻¹ * I m x :=
        Filter.eventually_of_mem (hU.mem_nhds hy) (hiter m)
      exact (((hderiv m y hy).const_mul _).differentiableAt).congr_of_eventuallyEq heq
    have heq2 : iteratedDerivWithin m (Brep k c b) U =ᶠ[𝓝 y] iteratedDeriv m (Brep k c b) :=
      Filter.eventually_of_mem (hU.mem_nhds hy) (fun x hx => iteratedDerivWithin_of_isOpen hU hx)
    exact (h1.congr_of_eventuallyEq heq2).differentiableWithinAt
  · intro n y hy
    rw [hiter n y hy, abs_mul]
    have hI : |I n y| ≤ ∫ w in Ioi (0 : ℝ), B * E ^ n * G n w := by
      rw [← Real.norm_eq_abs]
      exact norm_integral_le_of_norm_le (hGint n) (hbnd' n y hy)
    rw [integral_const_mul] at hI
    calc |(c * k)⁻¹| * |I n y| ≤ |(c * k)⁻¹| * (B * E ^ n * ∫ w in Ioi (0 : ℝ), G n w) :=
          mul_le_mul_of_nonneg_left hI (abs_nonneg _)
      _ = _ := by simp only [G]; ring

end GevreyEdge
