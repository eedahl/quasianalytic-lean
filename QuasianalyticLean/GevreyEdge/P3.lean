import QuasianalyticLean.GevreyEdge.Defs

/-!
# Theorem D, component P3: the representation `Bedge = Brep` (change of variables)

We substitute `w = φ(u) = c/uᵏ - c/yᵏ`, which maps `(0, y)` bijectively onto `(0, ∞)`, with inverse
`u = ψ_w(y)`. No integrability hypotheses are needed: the one-dimensional change of variables
formula `integral_image_eq_integral_abs_deriv_smul` is an identity of Bochner integrals.
-/

open Set Real Filter Topology MeasureTheory
open scoped ContDiff Nat

noncomputable section

namespace GevreyEdge

/-- The substitution map `φ(u) = c/uᵏ - c/yᵏ`. -/
private def phi (k : ℕ) (c y u : ℝ) : ℝ := c * (u ^ k)⁻¹ - c / y ^ k

private lemma phi_hasDerivAt (k : ℕ) (c y : ℝ) {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt (phi k c y) (c * (-((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2)) u := by
  have h1 : HasDerivAt (fun u : ℝ => u ^ k) ((k : ℝ) * u ^ (k - 1)) u := hasDerivAt_pow k u
  have h2 := (h1.inv (pow_ne_zero k hu)).const_mul c
  exact h2.sub_const (c / y ^ k)

/-- Key algebraic identity: `1 + yᵏ φ(u)/c = (y/u)ᵏ`. -/
private lemma one_add_phi {k : ℕ} {c y u : ℝ} (hc : 0 < c) (hy : 0 < y) (hu : 0 < u) :
    1 + y ^ k * phi k c y u / c = (y / u) ^ k := by
  unfold phi
  have : y ^ k ≠ 0 := pow_ne_zero _ hy.ne'
  have : u ^ k ≠ 0 := pow_ne_zero _ hu.ne'
  rw [div_pow]
  field_simp
  ring

private lemma psi_phi {k : ℕ} (hk : 1 ≤ k) {c y u : ℝ} (hc : 0 < c) (hy : 0 < y) (hu : 0 < u) :
    ψ k c (phi k c y u) y = u := by
  unfold ψ
  rw [one_add_phi hc hy hu, ← Real.rpow_natCast_mul (div_pos hy hu).le]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have : (k : ℝ) * (-(1 : ℝ) / k) = -1 := by field_simp
  rw [this, Real.rpow_neg_one]
  field_simp

private lemma hw_phi {k : ℕ} (hk : 1 ≤ k) {c y u : ℝ} (hc : 0 < c) (hy : 0 < y) (hu : 0 < u) :
    hw k c (phi k c y u) y = ((y / u) ^ (k + 1))⁻¹ := by
  unfold hw
  rw [one_add_phi hc hy hu, ← Real.rpow_natCast_mul (div_pos hy hu).le]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have : (k : ℝ) * (-1 - (1 : ℝ) / k) = -((k + 1 : ℕ) : ℝ) := by push_cast; field_simp; ring
  rw [this, Real.rpow_neg (div_pos hy hu).le, Real.rpow_natCast]

private lemma phi_injOn {k : ℕ} (hk : 1 ≤ k) {c y : ℝ} (hc : 0 < c) :
    InjOn (phi k c y) (Ioo 0 y) := by
  intro u hu v hv h
  unfold phi at h
  have h' : (u ^ k)⁻¹ = (v ^ k)⁻¹ := by
    have := sub_left_injective h
    exact mul_left_cancel₀ hc.ne' this
  have := inv_injective h'
  exact (pow_left_inj₀ hu.1.le hv.1.le (by omega)).1 this

private lemma phi_image {k : ℕ} (hk : 1 ≤ k) {c y : ℝ} (hc : 0 < c) (hy : 0 < y) :
    phi k c y '' Ioo 0 y = Ioi 0 := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    simp only [mem_Ioi, phi]
    have h1 : u ^ k < y ^ k := pow_lt_pow_left₀ hu.2 hu.1.le (by omega)
    have h2 : (y ^ k)⁻¹ < (u ^ k)⁻¹ := inv_strictAnti₀ (pow_pos hu.1 k) h1
    rw [div_eq_mul_inv]
    nlinarith
  · intro hw0
    simp only [mem_Ioi] at hw0
    set t := 1 + y ^ k * w / c with ht
    have hyk : 0 < y ^ k := pow_pos hy k
    have ht1 : 1 < t := by
      have : 0 < y ^ k * w / c := by positivity
      linarith
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have hneg : -(1 : ℝ) / k < 0 := by
      apply div_neg_of_neg_of_pos (by norm_num); exact_mod_cast (show 0 < k by omega)
    have hs0 : 0 < t ^ (-(1 : ℝ) / k) := Real.rpow_pos_of_pos (by linarith) _
    have hs1 : t ^ (-(1 : ℝ) / k) < 1 := Real.rpow_lt_one_of_one_lt_of_neg ht1 hneg
    refine ⟨ψ k c w y, ⟨?_, ?_⟩, ?_⟩
    · unfold ψ; rw [← ht]; positivity
    · unfold ψ; rw [← ht]; nlinarith
    · unfold ψ phi
      rw [← ht, mul_pow, ← Real.rpow_mul_natCast (by linarith)]
      have : -(1 : ℝ) / k * k = -1 := by field_simp
      rw [this, Real.rpow_neg_one, ht]
      field_simp
      ring

/-- **P3.** The representation. -/
theorem P3_representation {k : ℕ} (hk : 1 ≤ k) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    {b : ℝ → ℝ} (hbc : ContinuousOn b (Ioo 0 δ)) (hbb : ∃ C, ∀ x ∈ Ioo 0 δ, |b x| ≤ C) :
    ∀ y ∈ Ioo 0 δ, Bedge k c b y = Brep k c b y := by
  intro y hy
  have hy0 : 0 < y := hy.1
  have hcv := integral_image_eq_integral_abs_deriv_smul (s := Ioo 0 y) (f := phi k c y)
    (f' := fun u => c * (-((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2)) measurableSet_Ioo
    (fun u hu => (phi_hasDerivAt k c y hu.1.ne').hasDerivWithinAt) (phi_injOn hk hc)
    (fun w => Real.exp (-w) * integrand k c b w y)
  rw [phi_image hk hc hy0] at hcv
  unfold Brep Bedge
  rw [hcv, intervalIntegral.integral_of_le hy0.le, integral_Ioc_eq_integral_Ioo]
  have hpt : ∀ u ∈ Ioo 0 y,
      |c * (-((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2)| •
        (Real.exp (-phi k c y u) * integrand k c b (phi k c y u) y) =
      (c * k * (y ^ (k + 1))⁻¹ * Real.exp (c / y ^ k)) * (Real.exp (-c / u ^ k) * b u) := by
    intro u hu
    have hu0 : 0 < u := hu.1
    unfold integrand
    rw [psi_phi hk hc hy0 hu0, hw_phi hk hc hy0 hu0, smul_eq_mul]
    have habs : |c * (-((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2)| =
        c * ((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2 := by
      rw [show c * (-((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2) =
          -(c * ((k : ℝ) * u ^ (k - 1)) / (u ^ k) ^ 2) by ring, abs_neg,
        abs_of_nonneg (by positivity)]
    have hexp : Real.exp (-phi k c y u) = Real.exp (-c / u ^ k) * Real.exp (c / y ^ k) := by
      rw [← Real.exp_add]; congr 1; unfold phi; ring
    rw [habs, hexp]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, inv_div, div_pow]
    have : u ≠ 0 := hu0.ne'
    have : y ≠ 0 := hy0.ne'
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioo hpt, integral_const_mul]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  field_simp

end GevreyEdge

