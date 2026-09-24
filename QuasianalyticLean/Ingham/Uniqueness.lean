import QuasianalyticLean.Ingham.I2
import QuasianalyticLean.Ingham.I3
import QuasianalyticLean.Ingham.I4
import QuasianalyticLean.DenjoyCarleman.Uniqueness

/-!
# Ingham uniqueness at the quasianalytic threshold

An uncertainty principle: if `‖𝓕 f ξ‖ ≤ C e^{-τ ω_β(|ξ|)}` with `ω_β(t) = t / log(e + t)^β` and
`0 < β ≤ 1`, then `f` cannot vanish on an open interval unless `f = 0`. Fourier decay bounds the
derivatives of `f` by the weight sequence of `ω_β`, which is quasianalytic for `β ≤ 1`, and the
Denjoy–Carleman theorem finishes.
-/

open Set Real MeasureTheory Filter Topology
open scoped FourierTransform ContDiff

noncomputable section

namespace Ingham

open DenjoyCarleman

theorem ingham_uniqueness {f : ℝ → ℂ} (hc : Continuous f) (hi : Integrable f)
    {τ β C : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (hβ : β ≤ 1)
    (hdec : ∀ ξ : ℝ, ‖𝓕 f ξ‖ ≤ C * Real.exp (-τ * omegaB β |ξ|))
    {a b : ℝ} (hab : a < b) (hzero : ∀ x ∈ Ioo a b, f x = 0) : f = 0 := by
  obtain ⟨hs, hbd⟩ := I2_smooth_bound hc hi hτ hβ0 hdec
  obtain ⟨K, hK, hKb⟩ := I1_integral_le hτ hβ0
  set C' := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  set N : ℕ → ℝ := fun n => (C' * K) * (2 * π) ^ n * weightSeq τ β (n + 2) with hN
  obtain ⟨hNlc, hNq⟩ := I3_shifted (K := C' * K) (A := 2 * π) hτ hβ0 hβ
    (mul_pos hC'pos hK) (by positivity)
  have hbd' : ∀ n x, ‖iteratedDeriv n f x‖ ≤ N n := by
    intro n x
    have hI : 0 ≤ ∫ ξ : ℝ, |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) :=
      integral_nonneg fun ξ => by positivity
    calc ‖iteratedDeriv n f x‖
        ≤ C * (2 * π) ^ n * ∫ ξ : ℝ, |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) := hbd n x
      _ ≤ C' * (2 * π) ^ n * ∫ ξ : ℝ, |ξ| ^ n * Real.exp (-τ * omegaB β |ξ|) := by
          gcongr; exact le_max_left _ _
      _ ≤ C' * (2 * π) ^ n * (K * weightSeq τ β (n + 2)) := by gcongr; exact hKb n
      _ = N n := by simp only [hN]; ring
  set x₀ := (a + b) / 2 with hx₀
  have hx₀m : x₀ ∈ Ioo a b := ⟨by linarith, by linarith⟩
  have hev : f =ᶠ[𝓝 x₀] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hx₀m.1 hx₀m.2) hzero
  have hflat : ∀ n, iteratedDeriv n f x₀ = 0 := by
    intro n
    rw [hev.iteratedDeriv_eq n]
    simp
  obtain ⟨hre, him⟩ := I4_contDiff_re_im hs
  -- a real function `g` with `|g⁽ⁿ⁾| ≤ ‖f⁽ⁿ⁾‖`, flat at `x₀`, vanishes everywhere
  have key : ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g →
      (∀ n x, |iteratedDeriv n g x| ≤ ‖iteratedDeriv n f x‖) →
      (∀ n, iteratedDeriv n g x₀ = 0) → ∀ x, g x = 0 := by
    intro g hg hgb hg0 x
    have hmem : x ∈ Icc (min x₀ x) (max x₀ x) := ⟨min_le_right _ _, le_max_right _ _⟩
    have hx₀mem : x₀ ∈ Icc (min x₀ x) (max x₀ x) := ⟨min_le_left _ _, le_max_left _ _⟩
    exact uniqueness hNlc hNq isOpen_univ (subset_univ _) hg.contDiffOn
      (fun n y _ => (hgb n y).trans (hbd' n y)) hx₀mem hg0 x hmem
  have gre := key (fun y => (f y).re) hre
    (fun n x => by rw [(I4_re_im hs n x).1]; exact Complex.abs_re_le_norm _)
    (fun n => by rw [(I4_re_im hs n x₀).1, hflat n]; simp)
  have gim := key (fun y => (f y).im) him
    (fun n x => by rw [(I4_re_im hs n x).2]; exact Complex.abs_im_le_norm _)
    (fun n => by rw [(I4_re_im hs n x₀).2, hflat n]; simp)
  funext x
  exact Complex.ext (by simpa using gre x) (by simpa using gim x)

end Ingham
