import QuasianalyticLean.FlatSwitch.Flat1
import QuasianalyticLean.FlatSwitch.Flat2

/-!
# Flat functions in the `ω_β` class are doubly exponentially small

A smooth `f` vanishing on `(-∞, 0]` with `|f⁽ⁿ⁾| ≤ C Aⁿ n! log(e+n)^{βn}` on `(0, δ)` satisfies
`|f(y)| ≤ C e · exp(-exp(c' y^{-1/β}))` near `0`. Hence no switch `≥ e^{-c/y^k}` near its edge
lies in the class, and a doubly exponential switch `e^{-θ exp(c y^{-γ})}`
with `γ < 1/β` does not either; compare `switch_in_omega_class` for `γ ≥ 1/(β−1)`.
-/

open Set Real Filter Topology
open scoped Nat ContDiff

noncomputable section

namespace FlatSwitch

/-- Membership in the `ω_β` class on `(0, δ)`. -/
def InOmegaClass (β δ : ℝ) (f : ℝ → ℝ) : Prop :=
  ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n : ℕ, ∀ t ∈ Ioo 0 δ,
    |iteratedDeriv n f t| ≤ C * A ^ n * ((n ! : ℝ) * Real.log (Real.exp 1 + n) ^ (β * n))

theorem flat_small {f : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ t ≤ 0, f t = 0) (hM : InOmegaClass β δ f) :
    ∃ C y₀ c' : ℝ, 0 < y₀ ∧ 0 < c' ∧ ∀ y ∈ Ioo 0 y₀,
      |f y| ≤ C * Real.exp (-Real.exp (c' * y ^ (-(1 / β)))) := by
  obtain ⟨C, A, hC, hA, hb⟩ := hM
  obtain ⟨y₁, c', hy₁, hc', henv⟩ := F2_envelope hA hβ
  refine ⟨C * Real.exp 1, min y₁ δ, c', lt_min hy₁ hδ, hc', fun y hy => ?_⟩
  have hy0 : 0 < y := hy.1
  obtain ⟨n, hn⟩ := henv y ⟨hy0, hy.2.trans_le (min_le_left _ _)⟩
  have hB : ∀ t ∈ Ioo 0 y, |iteratedDeriv n f t| ≤
      C * A ^ n * ((n ! : ℝ) * Real.log (Real.exp 1 + n) ^ (β * n)) :=
    fun t ht => hb n t ⟨ht.1, ht.2.trans (hy.2.trans_le (min_le_right _ _))⟩
  have h1 := F1_taylor hf h0 hy0 n hB
  have hfac : (0 : ℝ) < n ! := by exact_mod_cast Nat.factorial_pos n
  calc |f y| ≤ C * A ^ n * ((n ! : ℝ) * Real.log (Real.exp 1 + n) ^ (β * n)) * y ^ n / n ! := h1
    _ = C * ((A * y) ^ n * Real.log (Real.exp 1 + n) ^ (β * n)) := by
        rw [mul_pow]; field_simp
    _ ≤ C * (Real.exp 1 * Real.exp (-Real.exp (c' * y ^ (-(1 / β))))) := by gcongr
    _ = C * Real.exp 1 * Real.exp (-Real.exp (c' * y ^ (-(1 / β)))) := by ring

/-- A lower bound `exp(-G(y^{-1/β}))` on a flat member of the class is impossible when `G`
grows slower than every `exp(c' v)`. -/
theorem flat_contra {f : ℝ → ℝ} {β δ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ t ≤ 0, f t = 0) (hM : InOmegaClass β δ f) {G : ℝ → ℝ}
    (hlow : ∀ y ∈ Ioo 0 δ, Real.exp (-G (y ^ (-(1 / β)))) ≤ f y)
    (hG : ∀ c' : ℝ, 0 < c' → ∀ D : ℝ, ∀ᶠ v in atTop, D + G v < Real.exp (c' * v)) : False := by
  obtain ⟨C, y₀, c', hy₀, hc', hsmall⟩ := flat_small hβ hδ hf h0 hM
  have hT : Tendsto (fun y : ℝ => y ^ (-(1 / β))) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos (by positivity))
  have hev : ∀ᶠ y in 𝓝[>] (0 : ℝ), y ∈ Ioo 0 (min y₀ δ) :=
    Ioo_mem_nhdsGT (lt_min hy₀ hδ)
  obtain ⟨y, hy, hv⟩ := (hev.and (hT.eventually (hG c' hc' (Real.log C)))).exists
  set v := y ^ (-(1 / β))
  have h1 := hlow y ⟨hy.1, hy.2.trans_le (min_le_right _ _)⟩
  have h2 := hsmall y ⟨hy.1, hy.2.trans_le (min_le_left _ _)⟩
  have h3 : Real.exp (-G v) ≤ C * Real.exp (-Real.exp (c' * v)) :=
    h1.trans ((le_abs_self _).trans h2)
  have hC : 0 < C := by
    by_contra hC; replace hC := le_of_not_gt hC
    have : C * Real.exp (-Real.exp (c' * v)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hC (Real.exp_pos _).le
    linarith [Real.exp_pos (-G v)]
  have h4 := Real.log_le_log (Real.exp_pos _) h3
  rw [Real.log_exp, Real.log_mul hC.ne' (Real.exp_pos _).ne', Real.log_exp] at h4
  linarith

/-- No switch bounded below by `e^{-c/y^k}` near its edge lies in the `ω_β` class. -/
theorem no_gevrey_switch {f : ℝ → ℝ} {β δ c k : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hc : 0 < c)
    (hk : 0 < k) (hf : ContDiff ℝ ∞ f) (h0 : ∀ t ≤ 0, f t = 0)
    (hlow : ∀ y ∈ Ioo 0 δ, Real.exp (-c / y ^ k) ≤ f y) : ¬ InOmegaClass β δ f := by
  intro hM
  refine flat_contra hβ hδ hf h0 hM (G := fun v => c * v ^ (k * β)) (fun y hy => ?_) ?_
  · convert hlow y hy using 2
    rw [← Real.rpow_mul hy.1.le, show -(1 / β) * (k * β) = -k by field_simp,
      Real.rpow_neg hy.1.le]
    ring
  · intro c' hc' D
    have hO := (isLittleO_rpow_exp_pos_mul_atTop (k * β) hc').bound
      (show (0 : ℝ) < 1 / (2 * c) by positivity)
    have hE : ∀ᶠ v in atTop, 2 * (|D| + 1) ≤ Real.exp (c' * v) :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc')).eventually_ge_atTop _
    filter_upwards [hO, hE, eventually_gt_atTop 0] with v hv hv2 hv0
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hv0 _),
      abs_of_pos (Real.exp_pos _)] at hv
    have : c * v ^ (k * β) ≤ Real.exp (c' * v) / 2 := by
      calc c * v ^ (k * β) ≤ c * (1 / (2 * c) * Real.exp (c' * v)) := by gcongr
        _ = _ := by field_simp
    linarith [le_abs_self D]

/-- Nor does a doubly exponential switch `e^{-θ exp(c y^{-γ})}` with `γ < 1/β`. -/
theorem no_slow_double_switch {f : ℝ → ℝ} {β δ c γ θ : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    (hc : 0 < c) (hγ : 0 < γ) (hγβ : γ < 1 / β) (hθ : 0 < θ) (hf : ContDiff ℝ ∞ f)
    (h0 : ∀ t ≤ 0, f t = 0)
    (hlow : ∀ y ∈ Ioo 0 δ, Real.exp (-θ * Real.exp (c * y ^ (-γ))) ≤ f y) :
    ¬ InOmegaClass β δ f := by
  intro hM
  refine flat_contra hβ hδ hf h0 hM (G := fun v => θ * Real.exp (c * v ^ (γ * β)))
    (fun y hy => ?_) ?_
  · convert hlow y hy using 2
    rw [← Real.rpow_mul hy.1.le, show -(1 / β) * (γ * β) = -γ by field_simp]
    ring
  · intro c' hc' D
    have hq : γ * β - 1 < 0 := by
      have := mul_lt_mul_of_pos_right hγβ hβ
      rw [one_div_mul_cancel hβ.ne'] at this; linarith
    have hT := tendsto_rpow_neg_atTop (show 0 < -(γ * β - 1) by linarith)
    rw [neg_neg] at hT
    have hsmall : ∀ᶠ v in atTop, v ^ (γ * β - 1) < c' / (2 * c) :=
      hT.eventually (gt_mem_nhds (by positivity))
    have hlin : ∀ᶠ v in atTop, 2 * (Real.log θ + Real.log 2) ≤ c' * v :=
      (tendsto_id.const_mul_atTop hc').eventually_ge_atTop _
    have hE : ∀ᶠ v in atTop, 2 * (|D| + 1) ≤ Real.exp (c' * v) :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hc')).eventually_ge_atTop _
    filter_upwards [hsmall, hlin, hE, eventually_gt_atTop 0] with v hv hl hv2 hv0
    have hpow : v ^ (γ * β) = v ^ (γ * β - 1) * v := by
      rw [← Real.rpow_add_one hv0.ne']; ring_nf
    have hcv : c * v ^ (γ * β) ≤ c' * v / 2 := by
      rw [hpow]
      calc c * (v ^ (γ * β - 1) * v) ≤ c * (c' / (2 * c) * v) := by gcongr
        _ = _ := by field_simp
    have : θ * Real.exp (c * v ^ (γ * β)) ≤ Real.exp (c' * v) / 2 := by
      calc θ * Real.exp (c * v ^ (γ * β))
          = Real.exp (Real.log θ + c * v ^ (γ * β)) := by
            rw [Real.exp_add, Real.exp_log hθ]
        _ ≤ Real.exp (c' * v - Real.log 2) := Real.exp_le_exp.mpr (by linarith)
        _ = Real.exp (c' * v) / 2 := by
            rw [Real.exp_sub, Real.exp_log (by norm_num)]
    linarith [le_abs_self D]

end FlatSwitch
