import QuasianalyticLean.GevreyEdge.Interfaces

/-!
# The Gevrey edge factorisation

If `b` is Gevrey of order `s ≥ 1` on `(0, δ)`, then
`B(y) = y^{-(k+1)} e^{c/yᵏ} ∫₀^y e^{-c/uᵏ} b(u) du` is Gevrey of order `max(s, 1 + 1/k)` on `(0, δ)`.
Assembled from the components `P1`–`P5` of `Interfaces.lean`.
-/

open Set Real Filter Topology MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

theorem theoremD {k : ℕ} (hk : 1 ≤ k) {c δ s : ℝ} (hc : 0 < c) (hδ : 0 < δ) (hs : 1 ≤ s)
    {b : ℝ → ℝ} (hb : GevreyBound s δ b) :
    GevreyBound (max s (1 + 1 / (k : ℝ))) δ (Bedge k c b) := by
  obtain ⟨hbsmooth, Cb, Ab, hCb, hAb, hbb⟩ := hb
  set A := max Ab 1 with hAdef
  have hA1 : 1 ≤ A := le_max_right _ _
  have hbbA : ∀ j : ℕ, ∀ x ∈ Ioo 0 δ, |iteratedDeriv j b x| ≤ Cb * A ^ j * ((j ! : ℕ) : ℝ) ^ s := by
    intro j x hx
    refine (hbb j x hx).trans ?_
    gcongr
    exact le_max_left _ _
  obtain ⟨κ, M, hκ, hκ1, hM1, hP2⟩ := P2_psi_hw_bounds hk hc hδ
  have hM0 : 0 ≤ M := by linarith
  -- pointwise bound on the integrand, from P1 applied with r = κ (1+w)^{-1/k}
  have hint : ∀ n : ℕ, ∀ w : ℝ, 0 ≤ w → ∀ y ∈ Ioo 0 δ,
      |iteratedDeriv n (integrand k c b w) y| ≤
        (Cb * M) * (16 * A * M) ^ n * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n := by
    intro n w hw0 y hy
    obtain ⟨hψs, hhs, hψmem, hψb, hhb⟩ := hP2 w hw0 y hy
    set r := κ * (1 + w) ^ (-(1 : ℝ) / k) with hr
    have hpow_pos : 0 < (1 + w) ^ (-(1 : ℝ) / k) := Real.rpow_pos_of_pos (by linarith) _
    have hr0 : 0 < r := mul_pos hκ hpow_pos
    have hpow_le : (1 + w) ^ (-(1 : ℝ) / k) ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith)
      have : (0 : ℝ) < k := by exact_mod_cast hk
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num) this.le
    have hr1 : r ≤ 1 := by
      calc r = κ * (1 + w) ^ (-(1 : ℝ) / k) := rfl
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    have hrinv : r⁻¹ = κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k) := by
      rw [hr, mul_inv, ← Real.rpow_neg (by linarith)]
      congr 2
      ring
    have := P1_comp_mul_bound (g := b) (f := ψ k c w) (h := hw k c w) (U := Ioo 0 δ) isOpen_Ioo
      (y := y) (C := Cb) (A := A) (K := M) (H := M) (r := r) hs hr0 hr1 hA1 hM1 hCb hM0
      hbsmooth hbbA hψs hψmem hψb hhs hhb n
    have hfun : integrand k c b w = fun x => b (ψ k c w x) * hw k c w x := rfl
    rw [hfun]
    calc _ ≤ Cb * M * (16 * A * M) ^ n * shape s r⁻¹ n := this
      _ = _ := by rw [hrinv]
  have hsm : ∀ w : ℝ, 0 ≤ w → ∀ y ∈ Ioo 0 δ, ContDiffAt ℝ ∞ (integrand k c b w) y := by
    intro w hw0 y hy
    obtain ⟨hψs, hhs, hψmem, -, -⟩ := hP2 w hw0 y hy
    have hbat : ContDiffAt ℝ ∞ b (ψ k c w y) :=
      hbsmooth.contDiffAt (isOpen_Ioo.mem_nhds hψmem)
    exact (hbat.comp y hψs).mul hhs
  have hB0 : 0 ≤ Cb * M := mul_nonneg hCb hM0
  have hE0 : 0 ≤ 16 * A * M := by positivity
  obtain ⟨hBrep_smooth, hBrep_bound⟩ :=
    P4_iteratedDeriv_Brep hk hc hδ hbsmooth hκ hB0 hE0 hsm hint
  obtain ⟨C5, E5, hC5, hE5, hP5⟩ := P5_integral_shape hk hκ hκ1 hs
  -- transfer from Brep to Bedge on the open interval
  have heq : EqOn (Bedge k c b) (Brep k c b) (Ioo 0 δ) :=
    P3_representation hk hc hδ hbsmooth.continuousOn
      ⟨Cb, fun x hx => by simpa using hbbA 0 x hx⟩
  refine ⟨hBrep_smooth.congr heq, |(c * k)⁻¹| * (Cb * M) * C5, 16 * A * M * E5,
    by positivity, by positivity, fun n y hy => ?_⟩
  have hev : Bedge k c b =ᶠ[𝓝 y] Brep k c b :=
    Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hy) heq
  rw [hev.iteratedDeriv_eq n]
  calc |iteratedDeriv n (Brep k c b) y|
      ≤ |(c * k)⁻¹| * (Cb * M) * (16 * A * M) ^ n *
          ∫ w in Ioi (0 : ℝ), Real.exp (-w) * shape s (κ⁻¹ * (1 + w) ^ ((1 : ℝ) / k)) n :=
        hBrep_bound n y hy
    _ ≤ |(c * k)⁻¹| * (Cb * M) * (16 * A * M) ^ n *
          (C5 * E5 ^ n * ((n ! : ℕ) : ℝ) ^ (max s (1 + 1 / (k : ℝ)))) := by
        gcongr
        exact hP5 n
    _ = |(c * k)⁻¹| * (Cb * M) * C5 * (16 * A * M * E5) ^ n *
          ((n ! : ℕ) : ℝ) ^ (max s (1 + 1 / (k : ℝ))) := by
        rw [mul_pow]; ring

end GevreyEdge
