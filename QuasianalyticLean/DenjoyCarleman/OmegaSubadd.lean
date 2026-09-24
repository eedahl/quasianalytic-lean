import QuasianalyticLean.DenjoyCarleman.WeightSeq

/-!
# Subadditivity of `ω_β(t) = t / log(e + t)^β`

For `0 ≤ β ≤ 1`, `ω_β` is monotone and concave on `[0, ∞)`. With `L = log(e + t)`,
`ω_β' = L^{-β} (1 - β t / ((e + t) L)) ≥ 0` and
`ω_β'' = β L^{-β} (t (β + 1 - L) - 2 e L) / ((e + t) L)^2 ≤ 0`. Concavity and `ω_β(0) = 0` give
`ω_β(s + t) ≤ ω_β(s) + ω_β(t)`, hence `ω_β(‖x + y‖) ≤ ω_β(‖x‖) + ω_β(‖y‖)` in any seminormed group.
-/

open Set Real

noncomputable section

namespace DenjoyCarleman

/-- The first derivative of `ω_β` on `[0, ∞)`. -/
def omegaBDeriv (β t : ℝ) : ℝ :=
  Real.log (Real.exp 1 + t) ^ (-β) *
    (1 - β * t / ((Real.exp 1 + t) * Real.log (Real.exp 1 + t)))

/-- The second derivative of `ω_β` on `[0, ∞)`. -/
def omegaBDeriv2 (β t : ℝ) : ℝ :=
  β * Real.log (Real.exp 1 + t) ^ (-β) *
    (t * (β + 1 - Real.log (Real.exp 1 + t)) - 2 * Real.exp 1 * Real.log (Real.exp 1 + t)) /
      ((Real.exp 1 + t) * Real.log (Real.exp 1 + t)) ^ 2

lemma hasDerivAt_log_e_add {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun x => Real.log (Real.exp 1 + x)) (1 / (Real.exp 1 + t)) t := by
  have h : HasDerivAt (fun x => Real.exp 1 + x) 1 t := (hasDerivAt_id t).const_add _
  simpa [one_div] using h.log (by positivity)

lemma hasDerivAt_omegaB (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (omegaB β) (omegaBDeriv β t) t := by
  have hL0 := log_e_add_pos ht
  have hL := (hasDerivAt_log_e_add ht).rpow_const (p := β) (Or.inl hL0.ne')
  have hP : Real.log (Real.exp 1 + t) ^ β ≠ 0 := (Real.rpow_pos_of_pos hL0 _).ne'
  have h := (hasDerivAt_id t).div hL hP
  refine h.congr_deriv ?_
  unfold omegaBDeriv
  have he : 0 < Real.exp 1 + t := by positivity
  rw [Real.rpow_sub_one hL0.ne', Real.rpow_neg hL0.le]
  simp only [id]
  field_simp

lemma hasDerivAt_omegaBDeriv (β : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (omegaBDeriv β) (omegaBDeriv2 β t) t := by
  have hL0 := log_e_add_pos ht
  have he : 0 < Real.exp 1 + t := by positivity
  have hlog := hasDerivAt_log_e_add ht
  have hP := hlog.rpow_const (p := -β) (Or.inl hL0.ne')
  have hA : HasDerivAt (fun x => (Real.exp 1 + x) * Real.log (Real.exp 1 + x))
      (1 * Real.log (Real.exp 1 + t) + (Real.exp 1 + t) * (1 / (Real.exp 1 + t))) t :=
    ((hasDerivAt_id t).const_add _).mul hlog
  have hB : HasDerivAt (fun x => β * x) (β * 1) t := (hasDerivAt_id t).const_mul β
  have hQ := (hasDerivAt_const t (1 : ℝ)).sub (hB.div hA (by positivity))
  have h := hP.mul hQ
  refine h.congr_deriv ?_
  unfold omegaBDeriv2
  rw [Real.rpow_sub_one hL0.ne']
  simp only [Pi.sub_apply, Pi.div_apply]
  field_simp
  ring

lemma omegaBDeriv_nonneg {β : ℝ} (hβ : β ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ omegaBDeriv β t := by
  have hL1 := one_le_log_e_add ht
  have he : 0 < Real.exp 1 + t := by positivity
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
  unfold omegaBDeriv
  refine mul_nonneg (Real.rpow_nonneg (by linarith) _) ?_
  rw [sub_nonneg, div_le_one (by positivity)]
  have : β * t ≤ t := by nlinarith
  nlinarith

lemma omegaBDeriv2_nonpos {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) {t : ℝ} (ht : 0 ≤ t) :
    omegaBDeriv2 β t ≤ 0 := by
  set L := Real.log (Real.exp 1 + t) with hLdef
  have hL1 : 1 ≤ L := one_le_log_e_add ht
  have key : t * (β + 1 - L) - 2 * Real.exp 1 * L ≤ 0 := by
    have he1 : 1 < Real.exp 1 := by
      have := Real.add_one_lt_exp (x := 1) one_ne_zero; linarith
    rcases le_or_gt 2 L with h2 | h2
    · nlinarith
    · have hlt : Real.exp 1 + t < Real.exp 2 := by
        rw [← Real.log_lt_iff_lt_exp (by positivity)]; exact h2
      have hexp2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      have he3 : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
      -- `t < e² - e < 2e ≤ 2eL` and `β + 1 - L ≤ 1`
      have : t < 2 * Real.exp 1 := by nlinarith
      nlinarith
  unfold omegaBDeriv2
  rw [← hLdef]
  refine div_nonpos_of_nonpos_of_nonneg ?_ (sq_nonneg _)
  exact mul_nonpos_of_nonneg_of_nonpos
    (mul_nonneg hβ0 (Real.rpow_nonneg (by linarith) _)) key

lemma nonneg_of_mem_interior_Ici {x : ℝ} (hx : x ∈ interior (Ici (0 : ℝ))) : 0 ≤ x := by
  rw [interior_Ici] at hx; exact le_of_lt hx

-- `hβ0` is not needed for monotonicity; it is kept for a uniform interface.
set_option linter.unusedVariables false in
theorem omegaB_monotoneOn {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) :
    MonotoneOn (omegaB β) (Set.Ici 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
    (fun x hx => (hasDerivAt_omegaB β hx).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_omegaB β (nonneg_of_mem_interior_Ici hx)).differentiableAt
      |>.differentiableWithinAt) (fun x hx => ?_)
  have hx0 := nonneg_of_mem_interior_Ici hx
  rw [(hasDerivAt_omegaB β hx0).deriv]
  exact omegaBDeriv_nonneg hβ hx0

theorem omegaB_concaveOn {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) :
    ConcaveOn ℝ (Set.Ici 0) (omegaB β) := by
  have hanti : AntitoneOn (omegaBDeriv β) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      (fun x hx => (hasDerivAt_omegaBDeriv β hx).continuousAt.continuousWithinAt)
      (fun x hx => (hasDerivAt_omegaBDeriv β (nonneg_of_mem_interior_Ici hx)).differentiableAt
        |>.differentiableWithinAt) (fun x hx => ?_)
    have hx0 := nonneg_of_mem_interior_Ici hx
    rw [(hasDerivAt_omegaBDeriv β hx0).deriv]
    exact omegaBDeriv2_nonpos hβ0 hβ hx0
  refine AntitoneOn.concaveOn_of_deriv (convex_Ici 0)
    (fun x hx => (hasDerivAt_omegaB β hx).continuousAt.continuousWithinAt)
    (fun x hx => (hasDerivAt_omegaB β (nonneg_of_mem_interior_Ici hx)).differentiableAt
      |>.differentiableWithinAt) ?_
  intro x hx y hy hxy
  rw [(hasDerivAt_omegaB β (nonneg_of_mem_interior_Ici hx)).deriv,
    (hasDerivAt_omegaB β (nonneg_of_mem_interior_Ici hy)).deriv]
  exact hanti (nonneg_of_mem_interior_Ici hx) (nonneg_of_mem_interior_Ici hy) hxy

lemma omegaB_zero (β : ℝ) : omegaB β 0 = 0 := by simp [omegaB]

/-- For a concave `ω` on `[0, ∞)` with `ω 0 = 0`: `(s / u) ω(u) ≤ ω(s)` for `0 ≤ s ≤ u`, `0 < u`. -/
lemma omegaB_ge_ratio {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) {s u : ℝ} (hs : 0 ≤ s) (hsu : s ≤ u)
    (hu : 0 < u) : s / u * omegaB β u ≤ omegaB β s := by
  have h := (omegaB_concaveOn hβ0 hβ).2 (show u ∈ Ici (0 : ℝ) from le_of_lt hu)
    (Set.mem_Ici.2 le_rfl) (div_nonneg hs hu.le)
    (show 0 ≤ 1 - s / u by rw [sub_nonneg, div_le_one hu]; exact hsu) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, omegaB_zero] at h
  rwa [div_mul_cancel₀ s hu.ne'] at h

theorem omegaB_subadd {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    omegaB β (s + t) ≤ omegaB β s + omegaB β t := by
  rcases (add_nonneg hs ht).eq_or_lt with h | h
  · have hs0 : s = 0 := by linarith
    have ht0 : t = 0 := by linarith
    simp [hs0, ht0, omegaB_zero]
  have h1 := omegaB_ge_ratio hβ0 hβ hs (by linarith) h
  have h2 := omegaB_ge_ratio hβ0 hβ ht (by linarith) h
  have : s / (s + t) * omegaB β (s + t) + t / (s + t) * omegaB β (s + t) = omegaB β (s + t) := by
    field_simp
  linarith

/-- Subadditivity on vectors of any real normed space: ω(‖x + y‖) ≤ ω(‖x‖) + ω(‖y‖). -/
theorem omegaB_norm_subadd {β : ℝ} (hβ0 : 0 ≤ β) (hβ : β ≤ 1) {E : Type*}
    [SeminormedAddCommGroup E] (x y : E) :
    omegaB β ‖x + y‖ ≤ omegaB β ‖x‖ + omegaB β ‖y‖ :=
  (omegaB_monotoneOn hβ0 hβ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (norm_add_le x y)).trans (omegaB_subadd hβ0 hβ (norm_nonneg _) (norm_nonneg _))

end DenjoyCarleman
