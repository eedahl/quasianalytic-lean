import QuasianalyticLean.DenjoyCarleman.Defs

/-!
# Weight sequences of `ω_β(t) = t / log(e + t)^β`

`M_k = sup_{s ≥ 1} s^k e^{-τ ω_β(s)}`. The shifted sequence `k ↦ M_{k+1}` is log-convex, and it is
quasianalytic exactly when `β ≤ 1`: two-sided bounds `(c k log(e+k)^β)^k ≤ M_k ≤ (C k log(e+k)^β)^k`
(the upper one for `β ≤ 1`) reduce the question to `Σ 1 / (n log(e+n)^β)`.
-/

open Set Real Filter Topology
open scoped Nat

noncomputable section

namespace DenjoyCarleman

/-- The weight `ω_β(t) = t / log(e + t)^β`. -/
def omegaB (β t : ℝ) : ℝ := t / Real.log (Real.exp 1 + t) ^ β

/-- `M_k = sup_{s ≥ 1} s^k e^{-τ ω_β(s)}`. -/
def weightSeq (τ β : ℝ) (k : ℕ) : ℝ := ⨆ s : Ici (1 : ℝ), (s : ℝ) ^ k * Real.exp (-τ * omegaB β s)

lemma one_le_log_e_add {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Real.log (Real.exp 1 + x) := by
  rw [Real.le_log_iff_exp_le (by positivity)]; linarith

lemma log_e_add_pos {x : ℝ} (hx : 0 ≤ x) : 0 < Real.log (Real.exp 1 + x) :=
  lt_of_lt_of_le one_pos (one_le_log_e_add hx)

lemma omegaB_nonneg (β : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ omegaB β t :=
  div_nonneg ht (Real.rpow_nonneg (log_e_add_pos ht).le _)

/-- Crude explicit bound: `s^k e^{-τ ω_β(s)} ≤ (2k)! / (τ a)^{2k}`. -/
lemma term_bound {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) :
    ∃ B, ∀ s : ℝ, 1 ≤ s → s ^ k * Real.exp (-τ * omegaB β s) ≤ B := by
  set a : ℝ := 1 / (2 * (2 * β) ^ β) with ha
  have hc : 0 < (2 * β) ^ β := Real.rpow_pos_of_pos (by linarith) _
  have ha0 : 0 < a := by positivity
  refine ⟨(2 * k)! / (τ * a) ^ (2 * k), fun s hs => ?_⟩
  have hs0 : 0 ≤ s := by linarith
  set L := Real.log (Real.exp 1 + s) with hL
  have hL0 : 0 < L := log_e_add_pos hs0
  -- `L^β ≤ 2 √s (2β)^β`
  have hε : (0:ℝ) < 1 / (2 * β) := by positivity
  have h1 : L ≤ (Real.exp 1 + s) ^ (1 / (2 * β)) / (1 / (2 * β)) :=
    Real.log_le_rpow_div (by positivity) hε
  have he3 : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  have h2 : L ^ β ≤ ((Real.exp 1 + s) ^ (1 / (2 * β)) / (1 / (2 * β))) ^ β :=
    Real.rpow_le_rpow hL0.le h1 hβ0.le
  have h3 : ((Real.exp 1 + s) ^ (1 / (2 * β)) / (1 / (2 * β))) ^ β
      = (Real.exp 1 + s) ^ (1 / 2 : ℝ) * (2 * β) ^ β := by
    rw [Real.div_rpow (by positivity) hε.le, ← Real.rpow_mul (by positivity)]
    rw [show 1 / (2 * β) * β = 1 / 2 by field_simp, one_div (2 * β),
      Real.inv_rpow (by positivity), div_inv_eq_mul]
  have h4 : (Real.exp 1 + s) ^ (1 / 2 : ℝ) ≤ (4 * s) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h5 : (4 * s) ^ (1 / 2 : ℝ) = 2 * s ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by norm_num) hs0]
    congr 1
    rw [show (4:ℝ) = 2 ^ (2:ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  set u := s ^ (1 / 2 : ℝ) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos (by linarith) _
  have huu : u ^ 2 = s := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul hs0]; norm_num
  have hu2 : u ^ (2 * k) = s ^ k := by
    rw [pow_mul, huu]
  have hLβ : L ^ β ≤ 2 * u * (2 * β) ^ β := by
    calc L ^ β ≤ _ := h2
      _ = _ := h3
      _ ≤ (4 * s) ^ (1 / 2 : ℝ) * (2 * β) ^ β := by gcongr
      _ = 2 * u * (2 * β) ^ β := by rw [h5]
  have hLβpos : 0 < L ^ β := Real.rpow_pos_of_pos hL0 _
  -- `ω ≥ a u`
  have hω : a * u ≤ omegaB β s := by
    unfold omegaB
    rw [← hL, le_div_iff₀ hLβpos]
    calc a * u * L ^ β ≤ a * u * (2 * u * (2 * β) ^ β) := by gcongr
      _ = s := by rw [ha]; field_simp; nlinarith [huu]
  have hexp : (τ * a * u) ^ (2 * k) / (2 * k)! ≤ Real.exp (τ * omegaB β s) := by
    calc (τ * a * u) ^ (2 * k) / (2 * k)! ≤ Real.exp (τ * a * u) :=
          Real.pow_div_factorial_le_exp (x := τ * a * u) (by positivity) (2 * k)
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hω hτ.le
  have hfac : (0:ℝ) < (2 * k)! := by exact_mod_cast Nat.factorial_pos _
  rw [neg_mul, Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  rw [mul_pow, hu2] at hexp
  rw [div_le_iff₀ hfac] at hexp
  linarith [hexp]


instance : Nonempty (Ici (1 : ℝ)) := ⟨⟨1, Set.mem_Ici.mpr le_rfl⟩⟩

lemma weightSeq_bddAbove {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) :
    BddAbove (range fun s : Ici (1 : ℝ) => (s : ℝ) ^ k * Real.exp (-τ * omegaB β s)) := by
  obtain ⟨B, hB⟩ := term_bound hτ hβ0 k
  exact ⟨B, by rintro _ ⟨s, rfl⟩; exact hB s s.2⟩

lemma le_weightSeq {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) {s : ℝ} (hs : 1 ≤ s) :
    s ^ k * Real.exp (-τ * omegaB β s) ≤ weightSeq τ β k :=
  le_ciSup (f := fun s : Ici (1 : ℝ) => (s : ℝ) ^ k * Real.exp (-τ * omegaB β s))
    (weightSeq_bddAbove hτ hβ0 k) ⟨s, hs⟩

lemma weightSeq_le {τ β B : ℝ} (k : ℕ)
    (h : ∀ s : ℝ, 1 ≤ s → s ^ k * Real.exp (-τ * omegaB β s) ≤ B) : weightSeq τ β k ≤ B :=
  ciSup_le fun s => h s s.2

lemma weightSeq_pos {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) : 0 < weightSeq τ β k :=
  lt_of_lt_of_le (by positivity) (le_weightSeq hτ hβ0 k (le_refl (1 : ℝ)))

lemma weightSeq_sq_le {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) :
    weightSeq τ β (k + 1) ^ 2 ≤ weightSeq τ β k * weightSeq τ β (k + 2) := by
  have h0 := weightSeq_pos hτ hβ0 k
  have h2 := weightSeq_pos hτ hβ0 (k + 2)
  have hle : weightSeq τ β (k + 1) ≤ √(weightSeq τ β k * weightSeq τ β (k + 2)) := by
    apply weightSeq_le
    intro s hs
    have hs0 : 0 ≤ s := by linarith
    rw [Real.le_sqrt (by positivity) (by positivity)]
    have e : (s ^ (k + 1) * Real.exp (-τ * omegaB β s)) ^ 2
        = (s ^ k * Real.exp (-τ * omegaB β s)) * (s ^ (k + 2) * Real.exp (-τ * omegaB β s)) := by
      ring
    rw [e]
    exact mul_le_mul (le_weightSeq hτ hβ0 k hs) (le_weightSeq hτ hβ0 (k + 2) hs)
      (by positivity) h0.le
  calc weightSeq τ β (k + 1) ^ 2 ≤ (√(weightSeq τ β k * weightSeq τ β (k + 2))) ^ 2 := by
        gcongr; exact (weightSeq_pos hτ hβ0 _).le
    _ = _ := Real.sq_sqrt (by positivity)

theorem weightSeq_logConvex {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (hβ : β ≤ 2) :
    LogConvexSeq (fun k => weightSeq τ β (k + 1)) where
  pos n := weightSeq_pos hτ hβ0 _
  ratio_mono n := by
    have h1 := weightSeq_pos hτ hβ0 (n + 1)
    have h2 := weightSeq_pos hτ hβ0 (n + 2)
    rw [div_le_div_iff₀ h1 h2]
    have := weightSeq_sq_le hτ hβ0 (n + 1)
    simp only [show n + 1 + 1 = n + 2 by ring, show n + 1 + 2 = n + 3 by ring] at this ⊢
    nlinarith [this]

/-- The ratios `r k = M_k / M_{k+1}`. -/
def wRatio (τ β : ℝ) (k : ℕ) : ℝ := weightSeq τ β k / weightSeq τ β (k + 1)

lemma wRatio_pos {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) : 0 < wRatio τ β k :=
  div_pos (weightSeq_pos hτ hβ0 _) (weightSeq_pos hτ hβ0 _)

lemma wRatio_succ_le {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k : ℕ) :
    wRatio τ β (k + 1) ≤ wRatio τ β k := by
  unfold wRatio
  have h0 := weightSeq_pos hτ hβ0 k
  have h1 := weightSeq_pos hτ hβ0 (k + 1)
  have h2 := weightSeq_pos hτ hβ0 (k + 2)
  rw [div_le_div_iff₀ h2 h1]
  have := weightSeq_sq_le hτ hβ0 k
  nlinarith [this]

lemma wRatio_antitone {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) : Antitone (wRatio τ β) :=
  antitone_nat_of_succ_le (wRatio_succ_le hτ hβ0)

/-- `M_k / M_{k+m} ≤ r_k ^ m`. -/
lemma div_le_wRatio_pow {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (k m : ℕ) :
    weightSeq τ β k / weightSeq τ β (k + m) ≤ wRatio τ β k ^ m := by
  induction m with
  | zero => simp [div_self (weightSeq_pos hτ hβ0 k).ne']
  | succ m ih =>
    have e : weightSeq τ β k / weightSeq τ β (k + (m + 1))
        = weightSeq τ β k / weightSeq τ β (k + m) * wRatio τ β (k + m) := by
      unfold wRatio
      have := (weightSeq_pos hτ hβ0 (k + m)).ne'
      rw [show k + m + 1 = k + (m + 1) by ring]
      field_simp
    rw [e, pow_succ]
    exact mul_le_mul ih (wRatio_antitone hτ hβ0 (by omega)) (wRatio_pos hτ hβ0 _).le
      (by positivity [(wRatio_pos hτ hβ0 k).le])

/-- `r_m ^ m ≤ M_1 / M_{m+1}`. -/
lemma wRatio_pow_le {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (m : ℕ) :
    wRatio τ β m ^ m ≤ weightSeq τ β 1 / weightSeq τ β (m + 1) := by
  induction m with
  | zero => simp [div_self (weightSeq_pos hτ hβ0 1).ne']
  | succ m ih =>
    have e : weightSeq τ β 1 / weightSeq τ β (m + 1 + 1)
        = weightSeq τ β 1 / weightSeq τ β (m + 1) * wRatio τ β (m + 1) := by
      unfold wRatio
      have := (weightSeq_pos hτ hβ0 (m + 1)).ne'
      field_simp
    rw [e, pow_succ]
    have hr := wRatio_succ_le hτ hβ0 m
    have hr0 := (wRatio_pos hτ hβ0 (m + 1)).le
    exact mul_le_mul_of_nonneg_right
      ((pow_le_pow_left₀ hr0 hr m).trans ih) hr0


/-- Lower bound `M_k ≥ (k ℓ_k^β e^{-τ})^k`, `ℓ_k = log(e + k)`. -/
lemma weightSeq_lower {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) {k : ℕ} (hk : 1 ≤ k) :
    ((k : ℝ) * Real.log (Real.exp 1 + k) ^ β * Real.exp (-τ)) ^ k ≤ weightSeq τ β k := by
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set ℓ := Real.log (Real.exp 1 + k) with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log_e_add (by linarith)
  have hℓβ : 1 ≤ ℓ ^ β := Real.one_le_rpow hℓ1 hβ0.le
  set s : ℝ := k * ℓ ^ β with hs
  have hks : (k : ℝ) ≤ s := by nlinarith
  have hs1 : 1 ≤ s := hk0.trans hks
  have hLs : ℓ ≤ Real.log (Real.exp 1 + s) :=
    Real.log_le_log (by positivity) (by linarith)
  have hLsβ : ℓ ^ β ≤ Real.log (Real.exp 1 + s) ^ β :=
    Real.rpow_le_rpow (by linarith) hLs hβ0.le
  have hω : omegaB β s ≤ k := by
    unfold omegaB
    rw [div_le_iff₀ (by linarith)]
    calc s = k * ℓ ^ β := rfl
      _ ≤ _ := by gcongr
  refine le_trans ?_ (le_weightSeq hτ hβ0 k hs1)
  rw [mul_pow, ← Real.exp_nat_mul]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Upper bound for `β ≤ 1`: `M_k ≤ (K k ℓ_k^β)^k`. -/
lemma weightSeq_upper {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (hβ : β ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    weightSeq τ β k ≤ (max 1 (8 / τ) ^ 2 * k * Real.log (Real.exp 1 + k) ^ β) ^ k := by
  set x := max 1 (8 / τ) with hx
  have hx1 : 1 ≤ x := le_max_left _ _
  have hτx : 8 ≤ τ * x := by
    have : 8 / τ ≤ x := le_max_right _ _
    rw [div_le_iff₀ hτ] at this; linarith
  set K := x ^ 2 with hK
  have hK1 : 1 ≤ K := by nlinarith
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set ℓ := Real.log (Real.exp 1 + k) with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log_e_add (by linarith)
  have hℓβ : 1 ≤ ℓ ^ β := Real.one_le_rpow hℓ1 hβ0.le
  have hℓβle : ℓ ^ β ≤ ℓ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hℓ1 hβ
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have hℓle : ℓ ≤ Real.exp 1 + k := by
    have := Real.log_le_sub_one_of_pos (show 0 < Real.exp 1 + k by positivity)
    linarith
  set S : ℝ := K * k * ℓ ^ β with hS
  have hS1 : 1 ≤ S := by
    have : 1 ≤ K * k := by nlinarith
    nlinarith
  -- `log(e+S) ≤ (log K + 2) ℓ`
  set ℓS := Real.log (Real.exp 1 + S) with hℓS
  have hℓS1 : 1 ≤ ℓS := one_le_log_e_add (by linarith)
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hlogK' : Real.log K + 2 ≤ 2 * x := by
    have : Real.log K = 2 * Real.log x := by rw [hK, Real.log_pow]; norm_num
    have := Real.log_le_sub_one_of_pos (show 0 < x by linarith)
    linarith
  have hℓS : ℓS ≤ (Real.log K + 2) * ℓ := by
    have h1 : Real.exp 1 + S ≤ K * (Real.exp 1 + k) ^ 2 := by
      have : S ≤ K * k * (Real.exp 1 + k) := by
        rw [hS]; gcongr; linarith
      have h3 : 1 * Real.exp 1 * 1 ≤ K * Real.exp 1 * (Real.exp 1 + k) := by
        gcongr; linarith
      have h4 : K * (Real.exp 1 + k) ^ 2 = K * k * (Real.exp 1 + k)
          + K * Real.exp 1 * (Real.exp 1 + k) := by ring
      linarith
    have h2 : ℓS ≤ Real.log K + 2 * ℓ := by
      calc ℓS ≤ Real.log (K * (Real.exp 1 + k) ^ 2) :=
            Real.log_le_log (by positivity) h1
        _ = Real.log K + 2 * ℓ := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow (Real.exp 1 + (k : ℝ)) 2, ← hℓ]
            push_cast; ring
    nlinarith
  have hℓSβ : ℓS ^ β ≤ (Real.log K + 2) * ℓ ^ β := by
    calc ℓS ^ β ≤ ((Real.log K + 2) * ℓ) ^ β := Real.rpow_le_rpow (by linarith) hℓS hβ0.le
      _ = (Real.log K + 2) ^ β * ℓ ^ β := Real.mul_rpow (by linarith) (by linarith)
      _ ≤ (Real.log K + 2) * ℓ ^ β := by
          gcongr
          simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ Real.log K + 2) hβ
  apply weightSeq_le
  intro s hs
  have hs0 : 0 ≤ s := by linarith
  have hω0 := omegaB_nonneg β hs0
  rcases le_total s S with hsS | hSs
  · calc s ^ k * Real.exp (-τ * omegaB β s) ≤ s ^ k * 1 := by
          gcongr; rw [Real.exp_le_one_iff]; nlinarith
      _ ≤ S ^ k := by rw [mul_one]; gcongr
  · set r := s / S with hr
    have hS0 : 0 < S := by linarith
    have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hS0]; linarith
    have hsr : s = r * S := by rw [hr]; field_simp
    have hlogr : 0 ≤ Real.log r := Real.log_nonneg hr1
    -- `log r (1 + log r) ≤ 4 r`
    have hsq : Real.log r * (1 + Real.log r) ≤ 4 * r := by
      have hq0 : 0 < √r := Real.sqrt_pos.mpr (by linarith)
      have hq : Real.log r ≤ 2 * √r - 2 := by
        have := Real.log_le_sub_one_of_pos hq0
        rw [Real.log_sqrt (by linarith)] at this
        linarith
      have hqq : √r * √r = r := Real.mul_self_sqrt (by linarith)
      nlinarith
    -- `log(e+s)^β ≤ (log K + 2) ℓ^β (1 + log r)`
    have hLs : Real.log (Real.exp 1 + s) ≤ ℓS * (1 + Real.log r) := by
      have : Real.exp 1 + s ≤ r * (Real.exp 1 + S) := by rw [hsr]; nlinarith
      calc Real.log (Real.exp 1 + s) ≤ Real.log (r * (Real.exp 1 + S)) :=
            Real.log_le_log (by positivity) this
        _ = Real.log r + ℓS := Real.log_mul (by positivity) (by positivity)
        _ ≤ _ := by nlinarith
    have hLsβ : Real.log (Real.exp 1 + s) ^ β ≤ (Real.log K + 2) * ℓ ^ β * (1 + Real.log r) := by
      calc Real.log (Real.exp 1 + s) ^ β ≤ (ℓS * (1 + Real.log r)) ^ β :=
            Real.rpow_le_rpow (log_e_add_pos hs0).le hLs hβ0.le
        _ = ℓS ^ β * (1 + Real.log r) ^ β := Real.mul_rpow (by linarith) (by linarith)
        _ ≤ ((Real.log K + 2) * ℓ ^ β) * (1 + Real.log r) := by
            gcongr
            simpa using Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ) ≤ 1 + Real.log r) hβ
    have hD0 : 0 < Real.log (Real.exp 1 + s) ^ β := Real.rpow_pos_of_pos (log_e_add_pos hs0) _
    -- `k log r ≤ τ ω(s)`
    have hkey : k * Real.log r ≤ τ * omegaB β s := by
      unfold omegaB
      rw [mul_div_assoc', le_div_iff₀ hD0]
      have hA : (Real.log K + 2) * (Real.log r * (1 + Real.log r)) ≤ τ * K * r := by
        have : τ * K = (τ * x) * x := by rw [hK]; ring
        rw [this]
        calc (Real.log K + 2) * (Real.log r * (1 + Real.log r)) ≤ (2 * x) * (4 * r) := by
              gcongr
          _ = 8 * x * r := by ring
          _ ≤ _ := by gcongr
      calc (k : ℝ) * Real.log r * Real.log (Real.exp 1 + s) ^ β
          ≤ k * Real.log r * ((Real.log K + 2) * ℓ ^ β * (1 + Real.log r)) := by gcongr
        _ = (k * ℓ ^ β) * ((Real.log K + 2) * (Real.log r * (1 + Real.log r))) := by ring
        _ ≤ (k * ℓ ^ β) * (τ * K * r) := by gcongr
        _ = τ * s := by rw [hsr, hS]; ring
    have hrk : r ^ k ≤ Real.exp (τ * omegaB β s) := by
      calc r ^ k = Real.exp (k * Real.log r) := by
            rw [← Real.log_pow, Real.exp_log (by positivity)]
        _ ≤ _ := Real.exp_le_exp.mpr hkey
    rw [hsr, mul_pow, neg_mul, Real.exp_neg, ← hsr]
    have hE := Real.exp_pos (τ * omegaB β s)
    calc r ^ k * S ^ k * (Real.exp (τ * omegaB β s))⁻¹
        = S ^ k * (r ^ k / Real.exp (τ * omegaB β s)) := by ring
      _ ≤ S ^ k * 1 := by
          gcongr
          rw [div_le_one hE]; exact hrk
      _ = S ^ k := mul_one _


/-! ### The comparison series `Σ 1 / (n log(e+n)^β)` -/

lemma logSeries_antitone (β : ℝ) (hβ0 : 0 ≤ β) :
    ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → 1 / ((n : ℝ) * Real.log (Real.exp 1 + n) ^ β)
      ≤ 1 / ((m : ℝ) * Real.log (Real.exp 1 + m) ^ β) := by
  intro m n hm hmn
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hmn' : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have h1 := log_e_add_pos hm'.le
  apply one_div_le_one_div_of_le (by positivity)
  gcongr

lemma summable_logSeries {β : ℝ} (hβ : 1 < β) :
    Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log (Real.exp 1 + n) ^ β)) := by
  have hβ0 : 0 ≤ β := by linarith
  rw [← summable_condensed_iff_of_nonneg (fun n => by
    have := log_e_add_pos (Nat.cast_nonneg (α := ℝ) n); positivity) (logSeries_antitone β hβ0)]
  rw [← summable_nat_add_iff 1]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hp : Summable (fun n : ℕ => (Real.log 2 ^ β)⁻¹ * (1 / ((n + 1 : ℕ) : ℝ) ^ β)) :=
    ((summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_rpow.mpr hβ)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hp
  · have := log_e_add_pos (Nat.cast_nonneg (α := ℝ) (2 ^ (n + 1))); positivity
  · have h2 : (0 : ℝ) < 2 ^ (n + 1) := by positivity
    have hL : ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤ Real.log (Real.exp 1 + (2 : ℝ) ^ (n + 1)) := by
      rw [← Real.log_pow]
      exact Real.log_le_log (by positivity) (by linarith [Real.exp_pos 1])
    have hLpos : 0 < ((n + 1 : ℕ) : ℝ) * Real.log 2 := by positivity
    push_cast
    rw [show (2 : ℝ) ^ (n + 1) * (1 / ((2 : ℝ) ^ (n + 1) *
        Real.log (Real.exp 1 + 2 ^ (n + 1)) ^ β))
        = 1 / Real.log (Real.exp 1 + 2 ^ (n + 1)) ^ β by field_simp]
    push_cast at hL hLpos
    calc 1 / Real.log (Real.exp 1 + 2 ^ (n + 1)) ^ β ≤ 1 / (((n : ℝ) + 1) * Real.log 2) ^ β :=
          one_div_le_one_div_of_le (Real.rpow_pos_of_pos hLpos _)
            (Real.rpow_le_rpow hLpos.le hL hβ0)
      _ = _ := by
          rw [Real.mul_rpow (by positivity) hl2.le]
          field_simp

lemma not_summable_logSeries :
    ¬ Summable (fun n : ℕ => 1 / ((n : ℝ) * Real.log (Real.exp 1 + n))) := by
  have e : (fun n : ℕ => 1 / ((n : ℝ) * Real.log (Real.exp 1 + n)))
      = (fun n : ℕ => 1 / ((n : ℝ) * Real.log (Real.exp 1 + n) ^ (1 : ℝ))) := by
    simp
  rw [e, ← summable_condensed_iff_of_nonneg (fun n => by
    have := log_e_add_pos (Nat.cast_nonneg (α := ℝ) n); positivity)
    (logSeries_antitone 1 zero_le_one)]
  intro h
  apply Real.not_summable_one_div_natCast
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hLpos := log_e_add_pos h2.le
  have hl2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hL : Real.log (Real.exp 1 + (2 : ℝ) ^ n) ≤ (n + 2 : ℝ) := by
    have he3 : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h4 : Real.exp 1 + (2 : ℝ) ^ n ≤ 2 ^ (n + 2) := by
      have : (1 : ℝ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
      rw [pow_add]; nlinarith
    calc Real.log (Real.exp 1 + (2 : ℝ) ^ n) ≤ Real.log (2 ^ (n + 2)) :=
          Real.log_le_log (by positivity) h4
      _ = (n + 2 : ℝ) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      _ ≤ (n + 2 : ℝ) * 1 := by gcongr
      _ = _ := mul_one _
  push_cast
  rw [Real.rpow_one, show (2 : ℝ) ^ n * (1 / ((2 : ℝ) ^ n * Real.log (Real.exp 1 + 2 ^ n)))
      = 1 / Real.log (Real.exp 1 + 2 ^ n) by field_simp]
  exact one_div_le_one_div_of_le hLpos hL


/-! ### Two-sided bounds on the ratios `M_k / M_{k+1}` -/

/-- For `β ≤ 1`: `M_k / M_{k+1} ≥ c / (k log(e+k))`. -/
lemma wRatio_lower {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (hβ : β ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    Real.exp (-τ) / (16 * (max 1 (8 / τ) ^ 2) ^ 2) *
      (1 / ((k : ℝ) * Real.log (Real.exp 1 + k))) ≤ wRatio τ β k := by
  set K := max 1 (8 / τ) ^ 2 with hK
  have hK1 : 1 ≤ K := one_le_pow₀ (le_max_left _ _)
  set E := Real.exp (-τ) with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hk0 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set ℓ := Real.log (Real.exp 1 + k) with hℓ
  have hℓ1 : 1 ≤ ℓ := one_le_log_e_add (by linarith)
  set ℓβ := ℓ ^ β with hℓβdef
  have hℓβ1 : 1 ≤ ℓβ := Real.one_le_rpow hℓ1 hβ0.le
  have hℓβle : ℓβ ≤ ℓ := by
    simpa using Real.rpow_le_rpow_of_exponent_le hℓ1 hβ
  set ℓ2 := Real.log (Real.exp 1 + ((k + k : ℕ) : ℝ)) with hℓ2
  have hℓ2le : ℓ2 ≤ 2 * ℓ := by
    have h1 : ℓ2 ≤ Real.log 2 + ℓ := by
      rw [hℓ2, hℓ, ← Real.log_mul (by norm_num) (by positivity)]
      apply Real.log_le_log (by positivity)
      push_cast; linarith [Real.exp_pos 1]
    have : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
    linarith
  have hℓ2pos : 0 < ℓ2 := log_e_add_pos (by positivity)
  have hℓ2β : ℓ2 ^ β ≤ 2 * ℓβ := by
    calc ℓ2 ^ β ≤ (2 * ℓ) ^ β := Real.rpow_le_rpow hℓ2pos.le hℓ2le hβ0.le
      _ = 2 ^ β * ℓβ := Real.mul_rpow (by norm_num) (by linarith)
      _ ≤ 2 * ℓβ := by
          gcongr
          simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hβ
  set y := E / (16 * K ^ 2) * (1 / ((k : ℝ) * ℓ)) with hy
  have hy0 : 0 ≤ y := by positivity
  have hr0 := (wRatio_pos hτ hβ0 k).le
  have hkne : k ≠ 0 := by omega
  rw [← pow_le_pow_iff_left₀ hy0 hr0 hkne]
  refine le_trans ?_ (div_le_wRatio_pow hτ hβ0 k k)
  have hMk := weightSeq_lower hτ hβ0 hk
  have hM2k := weightSeq_upper hτ hβ0 hβ (show 1 ≤ k + k by omega)
  have hM2pos := weightSeq_pos hτ hβ0 (k + k)
  rw [le_div_iff₀ hM2pos]
  refine le_trans (mul_le_mul_of_nonneg_left hM2k (by positivity)) (le_trans ?_ hMk)
  rw [← hK, ← hℓ2, ← hE, ← hℓ, ← hℓβdef, pow_add, ← mul_pow, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  have hcast : ((k + k : ℕ) : ℝ) = 2 * k := by push_cast; ring
  rw [hcast]
  calc y * ((K * (2 * k) * ℓ2 ^ β) * (K * (2 * k) * ℓ2 ^ β))
      ≤ y * ((K * (2 * k) * (2 * ℓβ)) * (K * (2 * k) * (2 * ℓβ))) := by gcongr
    _ = k * ℓβ * E * (ℓβ / ℓ) := by rw [hy]; field_simp; ring
    _ ≤ k * ℓβ * E * 1 := by
        gcongr
        rw [div_le_one (by linarith)]; exact hℓβle
    _ = k * ℓβ * E := mul_one _

/-- `M_k / M_{k+1} ≤ C / ((k+1) log(e+k+1)^β)`. -/
lemma wRatio_upper {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) {k : ℕ} (hk : 1 ≤ k) :
    wRatio τ β k ≤ (Real.exp τ ^ 2 * max 1 (weightSeq τ β 1)) *
      (1 / (((k + 1 : ℕ) : ℝ) * Real.log (Real.exp 1 + ((k + 1 : ℕ) : ℝ)) ^ β)) := by
  set E := Real.exp τ with hE
  have hE1 : 1 ≤ E := Real.one_le_exp hτ.le
  set m := max 1 (weightSeq τ β 1) with hm
  have hm1 : 1 ≤ m := le_max_left _ _
  have hM1m : weightSeq τ β 1 ≤ m := le_max_right _ _
  have hM1 := weightSeq_pos hτ hβ0 1
  set C := E ^ 2 * m with hC
  have hk1 : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ k + 1)
  set ℓ := Real.log (Real.exp 1 + ((k + 1 : ℕ) : ℝ)) with hℓ
  have hℓβ1 : 1 ≤ ℓ ^ β := Real.one_le_rpow (one_le_log_e_add (by linarith)) hβ0.le
  set y := ((k + 1 : ℕ) : ℝ) * ℓ ^ β with hy
  have hy1 : 1 ≤ y := by nlinarith
  have hy0 : 0 < y := by linarith
  rw [← div_eq_mul_one_div]
  have hr0 := (wRatio_pos hτ hβ0 k).le
  have hkne : k ≠ 0 := by omega
  rw [← pow_le_pow_iff_left₀ hr0 (by positivity) hkne]
  refine le_trans (wRatio_pow_le hτ hβ0 k) ?_
  have hlow := weightSeq_lower hτ hβ0 (show 1 ≤ k + 1 by omega)
  rw [← hℓ, ← hy, Real.exp_neg, ← hE] at hlow
  have hEk : E ^ (k + 1) ≤ E ^ (2 * k) := pow_le_pow_right₀ hE1 (by omega)
  have hmk : m ≤ m ^ k := le_self_pow₀ hm1 hkne
  have key : weightSeq τ β 1 * E ^ (k + 1) ≤ C ^ k * y := by
    rw [hC, mul_pow, ← pow_mul, mul_comm 2 k]
    calc weightSeq τ β 1 * E ^ (k + 1) ≤ m ^ k * E ^ (2 * k) := by
          gcongr; exact hM1m.trans hmk
      _ = E ^ (k * 2) * m ^ k * 1 := by rw [mul_comm 2 k]; ring
      _ ≤ E ^ (k * 2) * m ^ k * y := by gcongr
  have hlowpos : 0 < (y * E⁻¹) ^ (k + 1) := by positivity
  calc weightSeq τ β 1 / weightSeq τ β (k + 1) ≤ weightSeq τ β 1 / (y * E⁻¹) ^ (k + 1) :=
        div_le_div_of_nonneg_left hM1.le hlowpos hlow
    _ = weightSeq τ β 1 * E ^ (k + 1) / (y ^ k * y) := by
        rw [mul_pow, inv_pow, pow_succ]; field_simp
    _ ≤ C ^ k * y / (y ^ k * y) := by gcongr
    _ = (C / y) ^ k := by rw [div_pow]; field_simp

/-! ### Main theorems -/

theorem weightSeq_quasianalytic {τ β : ℝ} (hτ : 0 < τ) (hβ0 : 0 < β) (hβ : β ≤ 1) :
    Quasianalytic (fun k => weightSeq τ β (k + 1)) := by
  unfold Quasianalytic
  intro hsum
  have hs : Summable (fun n : ℕ => wRatio τ β (n + 1)) := hsum
  set c := Real.exp (-τ) / (16 * (max 1 (8 / τ) ^ 2) ^ 2) with hc
  have hc0 : 0 < c := by positivity
  have h1 : Summable (fun n : ℕ => c *
      (1 / (((n + 1 : ℕ) : ℝ) * Real.log (Real.exp 1 + ((n + 1 : ℕ) : ℝ))))) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hs
    · have := log_e_add_pos (Nat.cast_nonneg (α := ℝ) (n + 1)); positivity
    · exact wRatio_lower hτ hβ0 hβ (by omega)
  rw [summable_mul_left_iff hc0.ne'] at h1
  exact not_summable_logSeries ((summable_nat_add_iff 1).mp h1)

theorem weightSeq_not_quasianalytic {τ β : ℝ} (hτ : 0 < τ) (hβ1 : 1 < β) (hβ : β ≤ 2) :
    ¬ Quasianalytic (fun k => weightSeq τ β (k + 1)) := by
  have hβ0 : 0 < β := by linarith
  unfold Quasianalytic
  rw [not_not]
  show Summable (fun n : ℕ => wRatio τ β (n + 1))
  have h2 := ((summable_nat_add_iff 2).mpr (summable_logSeries hβ1)).mul_left
    (Real.exp τ ^ 2 * max 1 (weightSeq τ β 1))
  refine Summable.of_nonneg_of_le (fun n => (wRatio_pos hτ hβ0 _).le) (fun n => ?_) h2
  exact wRatio_upper hτ hβ0 (k := n + 1) (by omega)

end DenjoyCarleman
