import QuasianalyticLean.DenjoyCarleman.IdentityInterface

/-!
# Identity theorem in quasianalytic Denjoy–Carleman classes: proof

Reduction to the one-variable uniqueness theorem `DenjoyCarleman.uniqueness` along segments.
-/

open Set Real Filter Topology
open scoped ContDiff Nat

noncomputable section

namespace DenjoyCarleman

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated derivatives along a line. -/
theorem iteratedDeriv_line {F : E → ℝ} {U : Set E} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (x v : E) {s : ℝ} (hs : x + s • v ∈ U) (n : ℕ) :
    iteratedDeriv n (fun t : ℝ => F (x + t • v)) s =
      iteratedFDeriv ℝ n F (x + s • v) (fun _ => v) := by
  set G : E → ℝ := fun z => F (x + z) with hG
  set W : Set E := (fun z => x + z) ⁻¹' U with hW
  have hWo : IsOpen W := hU.preimage (continuous_const.add continuous_id)
  have hGc : ContDiffOn ℝ ∞ G W :=
    hF.comp (contDiff_const.add contDiff_id).contDiffOn (fun z hz => hz)
  set L : ℝ →L[ℝ] E := (ContinuousLinearMap.id ℝ ℝ).smulRight v with hL
  have hLs : ∀ t : ℝ, L t = t • v := fun t => by simp [hL]
  have hfun : (fun t : ℝ => F (x + t • v)) = G ∘ L := by
    funext t; simp [hG, hLs]
  have hSo : IsOpen (L ⁻¹' W) := hWo.preimage L.continuous
  have hsS : L s ∈ W := by simpa [hW, hLs] using hs
  have key := ContinuousLinearMap.iteratedFDerivWithin_comp_right L hGc hWo.uniqueDiffOn
    hSo.uniqueDiffOn hsS (i := n) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen n hSo (show s ∈ L ⁻¹' W from hsS),
    iteratedFDerivWithin_of_isOpen n hWo hsS] at key
  rw [iteratedDeriv_eq_iteratedFDeriv, hfun, key]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, hLs, one_smul]
  rw [hG, iteratedFDeriv_comp_add_left]


/-- Rescaling preserves log-convexity. -/
theorem logConvex_rescale {M : ℕ → ℝ} (hM : LogConvexSeq M) {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    LogConvexSeq (fun n => C * c ^ n * M n) := by
  have hr : ∀ n, C * c ^ (n + 1) * M (n + 1) / (C * c ^ n * M n) = c * (M (n + 1) / M n) := by
    intro n
    have := hM.pos n
    field_simp
    ring
  refine ⟨fun n => by have := hM.pos n; positivity, fun n => ?_⟩
  rw [hr, hr]
  exact mul_le_mul_of_nonneg_left (hM.ratio_mono n) hc.le

/-- Rescaling preserves quasianalyticity. -/
theorem quasianalytic_rescale {M : ℕ → ℝ} (hM : LogConvexSeq M) (hQ : Quasianalytic M)
    {C c : ℝ} (hC : 0 < C) (hc : 0 < c) :
    Quasianalytic (fun n => C * c ^ n * M n) := by
  have hr : (fun n => C * c ^ n * M n / (C * c ^ (n + 1) * M (n + 1))) =
      fun n => c⁻¹ * (M n / M (n + 1)) := by
    funext n
    have := hM.pos n
    have := hM.pos (n + 1)
    field_simp
    ring
  unfold Quasianalytic
  rw [hr, summable_mul_left_iff (inv_ne_zero hc.ne')]
  exact hQ

/-- A function vanishing near `y` has vanishing iterated derivatives at `y`. -/
theorem iteratedFDeriv_eq_zero_of_eventually {F : E → ℝ} {y : E} (h : F =ᶠ[𝓝 y] 0) (n : ℕ) :
    iteratedFDeriv ℝ n F y = 0 := by
  rw [(h.iteratedFDeriv ℝ n).eq_of_nhds]
  show iteratedFDeriv ℝ n (fun _ => (0 : ℝ)) y = 0
  simp

theorem eq_zero_of_iteratedFDeriv_zero {F : E → ℝ} {y : E} (h : iteratedFDeriv ℝ 0 F y = 0) :
    F y = 0 := by
  have := congrArg (fun m => m (fun _ => (0 : E))) h
  simpa [iteratedFDeriv_zero_apply] using this

theorem identity_theorem {M : ℕ → ℝ} (hM : LogConvexSeq M) (hQ : Quasianalytic M)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → ℝ} {U V : Set E} (hU : IsOpen U) (hUc : IsConnected U) (hF : InClass M F U)
    (hV : IsOpen V) (hVne : V.Nonempty) (hVU : V ⊆ U) (hzero : ∀ x ∈ V, F x = 0) :
    ∀ x ∈ U, F x = 0 := by
  set Z : Set E := {x | x ∈ U ∧ ∀ n : ℕ, iteratedFDeriv ℝ n F x = 0} with hZ
  -- vanishing on an open set gives flatness there
  have flat_of_open : ∀ W : Set E, IsOpen W → (∀ y ∈ W, F y = 0) →
      ∀ y ∈ W, ∀ n : ℕ, iteratedFDeriv ℝ n F y = 0 := by
    intro W hW h0 y hy n
    apply iteratedFDeriv_eq_zero_of_eventually _ n
    filter_upwards [hW.mem_nhds hy] with z hz using h0 z hz
  -- Z is open
  have hZo : IsOpen Z := by
    rw [Metric.isOpen_iff]
    rintro x ⟨hxU, hxflat⟩
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hxU
    set r := ε / 2 with hr
    have hr0 : 0 < r := by positivity
    have hK : Metric.closedBall x r ⊆ U :=
      (Metric.closedBall_subset_ball (by linarith)).trans hεU
    obtain ⟨C, A, hC, hA, hbd⟩ := hF.2 _ hK (isCompact_closedBall x r)
    have hball0 : ∀ y ∈ Metric.ball x r, F y = 0 := by
      intro y hy
      set v := y - x with hv
      have hvr : ‖v‖ < r := by rw [hv, ← dist_eq_norm]; exact hy
      rcases eq_or_ne v 0 with h0 | h0
      · have : y = x := sub_eq_zero.1 h0
        subst this
        exact eq_zero_of_iteratedFDeriv_zero (hxflat 0)
      have hvpos : 0 < ‖v‖ := norm_pos_iff.2 h0
      have hc : 0 < A * ‖v‖ := mul_pos hA hvpos
      set S : Set ℝ := {s | x + s • v ∈ U} with hS
      have hSo : IsOpen S := hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
      have hseg : ∀ s ∈ Icc (0 : ℝ) 1, x + s • v ∈ Metric.closedBall x r := by
        intro s hs
        rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg hs.1]
        nlinarith [hs.2, norm_nonneg v]
      have hIS : Icc (0 : ℝ) 1 ⊆ S := fun s hs => hK (hseg s hs)
      have hgc : ContDiffOn ℝ ∞ (fun t : ℝ => F (x + t • v)) S :=
        hF.1.comp (contDiff_const.add (contDiff_id.smul contDiff_const)).contDiffOn
          (fun t ht => ht)
      have hgbd : ∀ n : ℕ, ∀ s ∈ Icc (0 : ℝ) 1,
          |iteratedDeriv n (fun t : ℝ => F (x + t • v)) s| ≤ C * (A * ‖v‖) ^ n * M n := by
        intro n s hs
        rw [iteratedDeriv_line hU hF.1 x v (hIS hs) n, ← Real.norm_eq_abs]
        calc ‖iteratedFDeriv ℝ n F (x + s • v) (fun _ => v)‖
            ≤ ‖iteratedFDeriv ℝ n F (x + s • v)‖ * ∏ _i : Fin n, ‖v‖ :=
              ContinuousMultilinearMap.le_opNorm _ _
          _ = ‖iteratedFDeriv ℝ n F (x + s • v)‖ * ‖v‖ ^ n := by simp
          _ ≤ C * A ^ n * M n * ‖v‖ ^ n :=
              mul_le_mul_of_nonneg_right (hbd n _ (hseg s hs)) (by positivity)
          _ = C * (A * ‖v‖) ^ n * M n := by ring
      have hflat0 : ∀ n : ℕ, iteratedDeriv n (fun t : ℝ => F (x + t • v)) 0 = 0 := by
        intro n
        rw [iteratedDeriv_line hU hF.1 x v (hIS ⟨le_rfl, zero_le_one⟩) n]
        simp [hxflat n]
      have := uniqueness (logConvex_rescale hM hC hc) (quasianalytic_rescale hM hQ hC hc)
        hSo hIS hgc hgbd ⟨le_rfl, zero_le_one⟩ hflat0 1 ⟨zero_le_one, le_rfl⟩
      simpa [hv] using this
    refine ⟨r, hr0, fun y hy => ⟨hK (Metric.ball_subset_closedBall hy), ?_⟩⟩
    exact flat_of_open _ Metric.isOpen_ball hball0 y hy
  -- Z is relatively closed
  have hZc : closure Z ∩ U ⊆ Z := by
    rintro x ⟨hxc, hxU⟩
    refine ⟨hxU, fun n => ?_⟩
    have hcont : ContinuousAt (iteratedFDeriv ℝ n F) x :=
      (hF.1.contDiffAt (hU.mem_nhds hxU)).continuousAt_iteratedFDeriv (by exact_mod_cast le_top)
    have := hcont.continuousWithinAt.mem_closure (s := Z) (t := {0}) hxc
      (fun z hz => hz.2 n)
    simpa using this
  -- Z is nonempty
  have hZne : (U ∩ Z).Nonempty := by
    obtain ⟨y, hy⟩ := hVne
    exact ⟨y, hVU hy, hVU hy, flat_of_open V hV hzero y hy⟩
  have hUZ : U ⊆ Z := hUc.isPreconnected.subset_of_closure_inter_subset hZo hZne hZc
  intro x hx
  exact eq_zero_of_iteratedFDeriv_zero ((hUZ hx).2 0)

end DenjoyCarleman
