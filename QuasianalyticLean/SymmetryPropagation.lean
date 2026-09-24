import Mathlib

/-!
# Theorem B, abstract core: symmetry spreads from a shrinking core

This is the abstract core of an argument that exact rotational symmetry of a Navier–Stokes solution on a
shrinking core spreads to a fixed ball. The PDE input,
unique continuation for the linearised Stokes system (Saut–Temam / Fabre, Theorem 1.4), is
**not** formalised. It enters as the hypothesis `hUC`: vanishing on a nonempty open space-time
set forces vanishing on the whole horizontal slab above it. Given that, and continuity, a field
that vanishes on a ball of radius `ρ t > 0` at every time, with no regularity of `ρ`, vanishes on
the whole cylinder. The Baire argument is what removes any assumption on `ρ`.
-/

open Set Metric Filter Topology

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V]

/-- The space-time cylinder `B(1) × (-1, 0)`. -/
def cyl (X : Type*) [NormedAddCommGroup X] : Set (X × ℝ) := ball (0 : X) 1 ×ˢ Ioo (-1 : ℝ) 0

omit [NormedSpace ℝ X] in
/-- Time slices are continuous on closed subintervals of `(-1, 0)`. -/
lemma continuousOn_slice (F : X → ℝ → V)
    (hcont : ContinuousOn (fun p : X × ℝ => F p.1 p.2) (cyl X))
    {x : X} (hx : x ∈ ball (0 : X) 1) {s : Set ℝ} (hs : s ⊆ Ioo (-1 : ℝ) 0) :
    ContinuousOn (fun t => F x t) s := by
  have hmap : MapsTo (fun t : ℝ => (x, t)) s (cyl X) := fun t ht => ⟨hx, hs ht⟩
  exact hcont.comp (continuousOn_const.prodMk continuousOn_id) hmap

theorem symmetry_propagates (F : X → ℝ → V)
    (hcont : ContinuousOn (fun p : X × ℝ => F p.1 p.2) (cyl X))
    (ρ : ℝ → ℝ) (hρ : ∀ t ∈ Ioo (-1 : ℝ) 0, 0 < ρ t)
    (hcore : ∀ t ∈ Ioo (-1 : ℝ) 0, ∀ x ∈ ball (0 : X) (ρ t), F x t = 0)
    (hUC : ∀ O : Set (X × ℝ), IsOpen O → O ⊆ cyl X → (∀ p ∈ O, F p.1 p.2 = 0) →
      ∀ t, (∃ x, (x, t) ∈ O) → ∀ x ∈ ball (0 : X) 1, F x t = 0) :
    ∀ t ∈ Ioo (-1 : ℝ) 0, ∀ x ∈ ball (0 : X) 1, F x t = 0 := by
  -- Step 1 (density): every nonempty open subinterval of (-1, 0) contains a good time.
  have dense : ∀ a b : ℝ, -1 < a → a < b → b < 0 →
      ∃ t ∈ Ioo a b, ∀ x ∈ ball (0 : X) 1, F x t = 0 := by
    intro a b ha hab hb
    have hIcc : Icc a b ⊆ Ioo (-1 : ℝ) 0 := fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩
    -- radii 1/(n+1)
    let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
    have hr_pos : ∀ n, 0 < r n := fun n => by positivity
    have hr_le : ∀ n, r n ≤ 1 := fun n => by
      simp only [r]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    -- the closed sets C n
    let C : ℕ → Set ℝ := fun n => ⋂ x ∈ ball (0 : X) (r n), (Icc a b ∩ (fun t => F x t) ⁻¹' {0})
    have hC_closed : ∀ n, IsClosed (C n) := by
      intro n
      refine isClosed_biInter fun x hx => ?_
      have hx1 : x ∈ ball (0 : X) 1 := ball_subset_ball (hr_le n) hx
      exact (continuousOn_slice F hcont hx1 hIcc).preimage_isClosed_of_isClosed isClosed_Icc
        isClosed_singleton
    -- the countable closed cover of ℝ
    let A : ℕ → Set ℝ := fun n => if n = 0 then Iic a else if n = 1 then Ici b else C (n - 2)
    have hA_closed : ∀ n, IsClosed (A n) := by
      intro n; simp only [A]; split_ifs
      · exact isClosed_Iic
      · exact isClosed_Ici
      · exact hC_closed _
    have hA_cover : ⋃ n, A n = univ := by
      refine eq_univ_of_forall fun t => ?_
      simp only [mem_iUnion]
      by_cases hta : t ≤ a
      · exact ⟨0, by simp [A, hta]⟩
      by_cases htb : b ≤ t
      · exact ⟨1, by simp [A, htb]⟩
      push Not at hta htb
      have htI : t ∈ Ioo (-1 : ℝ) 0 := ⟨by linarith, by linarith⟩
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (hρ t htI)
      refine ⟨n + 2, ?_⟩
      simp only [A, show n + 2 ≠ 0 by omega, show n + 2 ≠ 1 by omega, ite_false,
        show n + 2 - 2 = n by omega]
      simp only [C, mem_iInter]
      intro x hx
      refine ⟨⟨hta.le, htb.le⟩, ?_⟩
      exact hcore t htI x (ball_subset_ball hn.le hx)
    -- Baire: the interiors are dense, so one of them meets (a, b)
    have hdense := dense_iUnion_interior_of_closed hA_closed hA_cover
    obtain ⟨t0, ht0ab, ht0U⟩ := hdense.inter_open_nonempty (Ioo a b) isOpen_Ioo
      (nonempty_Ioo.mpr hab)
    simp only [mem_iUnion] at ht0U
    obtain ⟨m, hm⟩ := ht0U
    -- m is not 0 or 1, since those interiors avoid (a, b)
    have hm2 : 2 ≤ m := by
      by_contra hlt
      push Not at hlt
      interval_cases m
      · simp only [A, ite_true, interior_Iic] at hm; exact absurd ht0ab.1 (not_lt.mpr hm.le)
      · simp only [A, show (1:ℕ) ≠ 0 by omega, ite_false, ite_true, interior_Ici] at hm
        exact absurd ht0ab.2 (not_lt.mpr hm.le)
    have hAm : A m = C (m - 2) := by
      simp only [A, show m ≠ 0 by omega, show m ≠ 1 by omega, ite_false]
    rw [hAm] at hm
    -- J := interior (C (m-2)) ∩ (a, b) is open, nonempty, and F vanishes on ball × J
    set J := interior (C (m - 2)) ∩ Ioo a b with hJ
    have hJopen : IsOpen J := isOpen_interior.inter isOpen_Ioo
    have hJsub : J ⊆ C (m - 2) := fun t ht => interior_subset ht.1
    let O : Set (X × ℝ) := ball (0 : X) (r (m - 2)) ×ˢ J
    have hOopen : IsOpen O := isOpen_ball.prod hJopen
    have hOcyl : O ⊆ cyl X := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      exact ⟨ball_subset_ball (hr_le _) hx, hIcc ⟨ht.2.1.le, ht.2.2.le⟩⟩
    have hOzero : ∀ p ∈ O, F p.1 p.2 = 0 := by
      rintro ⟨x, t⟩ ⟨hx, ht⟩
      have := hJsub ht
      simp only [C, mem_iInter] at this
      exact (this x hx).2
    refine ⟨t0, ht0ab, hUC O hOopen hOcyl hOzero t0 ⟨0, ?_⟩⟩
    exact ⟨mem_ball_self (hr_pos _), hm, ht0ab⟩
  -- Step 2 (continuity): a slice that vanishes at a dense set of times vanishes everywhere.
  intro t0 ht0 x hx
  by_contra hne
  have hcts : ContinuousAt (fun t => F x t) t0 :=
    (continuousOn_slice F hcont hx subset_rfl).continuousAt (isOpen_Ioo.mem_nhds ht0)
  have hpos : 0 < ‖F x t0‖ := norm_pos_iff.mpr hne
  obtain ⟨δ, hδ, hδball⟩ := Metric.continuousAt_iff.mp hcts _ hpos
  -- choose a good time within δ of t0, strictly inside (-1, 0)
  set a := max (t0 - δ) ((t0 - 1) / 2) with ha
  set b := min (t0 + δ) (t0 / 2) with hb
  have ha1 : -1 < a := lt_of_lt_of_le (by linarith [ht0.1]) (le_max_right _ _)
  have hb0 : b < 0 := lt_of_le_of_lt (min_le_right _ _) (by linarith [ht0.2])
  have hat : a < t0 := max_lt (by linarith) (by linarith [ht0.1])
  have htb : t0 < b := lt_min (by linarith) (by linarith [ht0.2])
  obtain ⟨t, htab, htgood⟩ := dense a b ha1 (hat.trans htb) hb0
  have hdist : dist t t0 < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor
    · linarith [htab.1, le_max_left (t0 - δ) ((t0 - 1) / 2)]
    · linarith [htab.2, min_le_left (t0 + δ) (t0 / 2)]
  have := hδball hdist
  rw [htgood x hx, dist_comm, dist_zero_right] at this
  exact lt_irrefl _ this
