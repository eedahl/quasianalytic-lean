import QuasianalyticLean.FlatSwitch.Defs

/-!
# Doubly exponential switch, component S2: Cauchy's estimate, transferred to the real switch

On a closed disc about `y > 0` of radius `r < y` the extension `switchC` is holomorphic
(the disc lies in `Re z > 0`), it agrees with `switchR` on the real axis, and Cauchy's
estimate bounds the `n`-th derivative by `n! B / rⁿ`.
-/

open Set Real Filter Topology
open scoped Nat

noncomputable section

namespace FlatSwitch

theorem S2_cauchy {c γ θ : ℝ} {y r B : ℝ} (hy : 0 < y) (hr : 0 < r) (hry : r < y)
    (hB : ∀ z : ℂ, ‖z - y‖ ≤ r → ‖switchC c γ θ z‖ ≤ B) (n : ℕ) :
    |iteratedDeriv n (switchR c γ θ) y| ≤ n ! * B / r ^ n := by
  have hF_re : ∀ t : ℝ, 0 < t → switchC c γ θ (t : ℂ) = ((switchR c γ θ t : ℝ) : ℂ) := by
    intro t ht
    unfold switchC switchR
    have e : (t : ℂ) ^ (-(γ : ℂ)) = ((t ^ (-γ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow ht.le]; push_cast; rfl
    rw [e]; push_cast; rfl
  let V : Set ℂ := {z : ℂ | 0 < z.re}
  have hV : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hFd : DifferentiableOn ℂ (switchC c γ θ) V := fun z hz => by
    have h1 : DifferentiableAt ℂ (fun z : ℂ => z ^ (-(γ : ℂ))) z :=
      DifferentiableAt.cpow_const (f := fun z : ℂ => z) differentiableAt_id
        (Complex.mem_slitPlane_iff.2 (Or.inl hz))
    unfold switchC
    exact (((h1.const_mul _).cexp.const_mul _).cexp).differentiableWithinAt
  have hball : ∀ z ∈ Metric.closedBall (y : ℂ) r, z ∈ V := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 := Complex.abs_re_le_norm (z - y)
    rw [Complex.sub_re, Complex.ofReal_re] at h1
    show 0 < z.re
    have := neg_abs_le (z.re - y)
    linarith
  have hyV : (y : ℂ) ∈ V := hball y (Metric.mem_closedBall_self hr.le)
  have hC := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr
    (f := switchC c γ θ) (c := (y : ℂ)) (C := B)
    (DifferentiableOn.diffContOnCl (hFd.mono (by
      rw [closure_ball _ hr.ne']
      exact hball)))
    (fun z hz => hB z (by
      have := Metric.sphere_subset_closedBall hz
      rwa [Metric.mem_closedBall, dist_eq_norm] at this))
  have hW : IsOpen ((fun t : ℝ => (t : ℂ)) ⁻¹' V) := hV.preimage Complex.continuous_ofReal
  have hev : switchR c γ θ =ᶠ[𝓝 y] fun t : ℝ => (switchC c γ θ t).re := by
    filter_upwards [hW.mem_nhds (show y ∈ (fun t : ℝ => (t : ℂ)) ⁻¹' V from hyV)] with t ht
    have ht' : 0 < t := by simpa [V] using ht
    rw [hF_re t ht', Complex.ofReal_re]
  have hre : ∀ m : ℕ, ∀ x : ℝ, (x : ℂ) ∈ V →
      iteratedDeriv m (fun t : ℝ => (switchC c γ θ t).re) x =
        (iteratedDeriv m (switchC c γ θ) x).re := by
    have hF := hFd.analyticOnNhd hV
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      have hev : iteratedDeriv m (fun t : ℝ => (switchC c γ θ t).re) =ᶠ[𝓝 x]
          fun t : ℝ => (iteratedDeriv m (switchC c γ θ) t).re := by
        filter_upwards [hW.mem_nhds (show x ∈ (fun t : ℝ => (t : ℂ)) ⁻¹' V from hx)] with t ht
        exact ih t ht
      rw [iteratedDeriv_succ, hev.deriv_eq]
      have hd : HasDerivAt (iteratedDeriv m (switchC c γ θ))
          (iteratedDeriv (m + 1) (switchC c γ θ) x) x := by
        rw [iteratedDeriv_succ, iteratedDeriv_eq_iterate]
        exact ((hF.iterated_deriv m) x hx).differentiableAt.hasDerivAt
      exact hd.real_of_complex.deriv
  rw [hev.iteratedDeriv_eq, hre n y hyV]
  refine (Complex.abs_re_le_norm _).trans (hC.trans (le_of_eq ?_))
  ring

end FlatSwitch
