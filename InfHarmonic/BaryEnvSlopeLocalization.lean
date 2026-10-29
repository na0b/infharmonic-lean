module

public import InfHarmonic.SubquadraticGrowth

@[expose] public section
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 2 of Lemma 5.2, the localization workhorse: on a compact set `S` of
admissible triples `(x, t, s)` the subquadratic growth of `f` makes every slope
functional `Γ(A; x)` a finite supremum, confines the near-minimizing slopes to a
ball of radius `Λ₀`, and confines the maximizing positions for every such slope to
one ball of radius `M`, on which the supremum is therefore attained. -/
theorem BaryEnvSlopeLocalization (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f)
    (S : Set (F × ℝ × ℝ)) (hSc : IsCompact S) (hSne : S.Nonempty)
    (hSadm : ∀ p ∈ S, 0 < p.2.2 ∧ p.2.1 ∈ I) :
    ∃ Λ₀ M : ℝ, 0 ≤ Λ₀ ∧ 0 < M ∧
      (∀ p ∈ S, ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}) ∧
      (∀ p ∈ S, ∀ A : F,
          sSup {w : ℝ | ∃ y : F,
              w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
            ≤ sSup {w : ℝ | ∃ y : F,
              w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
                - inner ℝ (0 : F) (y - p.1)} + 1 →
          ‖A‖ ≤ Λ₀) ∧
      (∀ p ∈ S, ∀ A : F, ‖A‖ ≤ Λ₀ + 1 →
          sSup {w : ℝ | ∃ y : F,
              w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
            = sSup ((fun y : F => f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
                - inner ℝ A (y - p.1)) '' closedBall (0 : F) M) ∧
          (∃ y₀ : F, ‖y₀‖ ≤ M ∧
            sSup {w : ℝ | ∃ y : F,
                w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
              = f (toLp 2 (y₀, p.2.1)) - ‖y₀‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y₀ - p.1)) ∧
          (∀ y : F,
            sSup {w : ℝ | ∃ y' : F,
                w = f (toLp 2 (y', p.2.1)) - ‖y'‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y' - p.1)}
              = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1) →
            ‖y‖ ≤ M)) := by
  -- R₀ = max over S of |x|
  obtain ⟨pR, hpR, hmaxR⟩ := hSc.exists_isMaxOn hSne
    (f := fun p : F × ℝ × ℝ => ‖p.1‖) (by fun_prop)
  obtain ⟨R₀, hR₀def⟩ : ∃ r : ℝ, r = ‖pR.1‖ := ⟨_, rfl⟩
  have hR₀ : ∀ p ∈ S, ‖p.1‖ ≤ R₀ := by
    intro p hp; rw [hR₀def]; exact isMaxOn_iff.mp hmaxR p hp
  have hR₀0 : 0 ≤ R₀ := by rw [hR₀def]; positivity
  -- s_max = max over S of s, s_min = min over S of s
  obtain ⟨pA, hpA, hmaxS⟩ := hSc.exists_isMaxOn hSne
    (f := fun p : F × ℝ × ℝ => p.2.2) (by fun_prop)
  obtain ⟨smax, hsmaxdef⟩ : ∃ r : ℝ, r = pA.2.2 := ⟨_, rfl⟩
  have hsmax : ∀ p ∈ S, p.2.2 ≤ smax := by
    intro p hp; rw [hsmaxdef]; exact isMaxOn_iff.mp hmaxS p hp
  have hsmax0 : 0 < smax := by rw [hsmaxdef]; exact (hSadm pA hpA).1
  obtain ⟨pB, hpB, hminS⟩ := hSc.exists_isMinOn hSne
    (f := fun p : F × ℝ × ℝ => p.2.2) (by fun_prop)
  obtain ⟨smin, hsmindef⟩ : ∃ r : ℝ, r = pB.2.2 := ⟨_, rfl⟩
  have hsmin : ∀ p ∈ S, smin ≤ p.2.2 := by
    intro p hp; rw [hsmindef]; exact isMinOn_iff.mp hminS p hp
  have hsmin0 : 0 < smin := by rw [hsmindef]; exact (hSadm pB hpB).1
  -- J, the time projection of S
  obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = (fun p : F × ℝ × ℝ => p.2.1) '' S := ⟨_, rfl⟩
  have hJc : IsCompact J := by rw [hJdef]; exact hSc.image (by fun_prop)
  have hJI : J ⊆ I := by
    rw [hJdef]; rintro σ ⟨p, hp, rfl⟩; exact (hSadm p hp).2
  have hJne : J.Nonempty := by rw [hJdef]; exact hSne.image _
  have hJmem : ∀ p ∈ S, p.2.1 ∈ J := by
    intro p hp; rw [hJdef]; exact ⟨p, hp, rfl⟩
  -- the far bound, from subquadratic growth at ε = 1/(4 s_max)
  obtain ⟨M₀, hM₀0, hM₀⟩ := hgrow J hJI hJc (1 / (4 * smax)) (by positivity)
  have hgfar : ∀ p ∈ S, ∀ y : F, M₀ ≤ ‖y‖ →
      f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) ≤ -(‖y‖ ^ 2 / (4 * smax)) := by
    intro p hp y hy
    have hs0 : 0 < p.2.2 := (hSadm p hp).1
    have hsle : p.2.2 ≤ smax := hsmax p hp
    have habs := hM₀ (toLp 2 (y, p.2.1)) hy (hJmem p hp)
    have hf : f (toLp 2 (y, p.2.1)) ≤ ‖y‖ ^ 2 / (4 * smax) := by
      have := (abs_le.mp habs).2
      rw [div_mul_eq_mul_div, one_mul] at this
      exact this
    have h1 : ‖y‖ ^ 2 / (4 * smax) ≤ ‖y‖ ^ 2 / (4 * p.2.2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h2 : ‖y‖ ^ 2 / (4 * p.2.2) - ‖y‖ ^ 2 / (2 * p.2.2)
        = -(‖y‖ ^ 2 / (4 * p.2.2)) := by field_simp; ring
    have h3 : ‖y‖ ^ 2 / (4 * smax) ≤ ‖y‖ ^ 2 / (4 * p.2.2) := h1
    have h4 : -(‖y‖ ^ 2 / (4 * p.2.2)) ≤ -(‖y‖ ^ 2 / (4 * smax)) := by linarith
    linarith
  -- the near bound: |f| is bounded on a compact space-time box
  obtain ⟨q₀, hq₀, hmaxN⟩ := ((isCompact_closedBall (0 : F) (M₀ + R₀ + 1)).prod hJc).exists_isMaxOn
    ⟨(0, hJne.choose), ⟨mem_closedBall_zero_iff.mpr (by simp only [norm_zero]; positivity), hJne.choose_spec⟩⟩
    (f := fun q : F × ℝ => |f (toLp 2 q)|)
    (((hcont.comp (by fun_prop : Continuous (fun q : F × ℝ => (toLp 2 q : WithLp 2 (F × ℝ)))).continuousOn
        (fun q hq => hJI hq.2)).abs))
  obtain ⟨N₀, hN₀def⟩ : ∃ r : ℝ, r = |f (toLp 2 q₀)| := ⟨_, rfl⟩
  have hN₀ : ∀ q ∈ closedBall (0 : F) (M₀ + R₀ + 1) ×ˢ J, |f (toLp 2 q)| ≤ N₀ := by
    intro q hq; rw [hN₀def]; exact isMaxOn_iff.mp hmaxN q hq
  have hN₀0 : 0 ≤ N₀ := by rw [hN₀def]; positivity
  obtain ⟨N₁, hN₁def⟩ : ∃ r : ℝ, r = N₀ + (M₀ + R₀ + 1) ^ 2 / (2 * smin) := ⟨_, rfl⟩
  have hN₁0 : 0 ≤ N₁ := by rw [hN₁def]; positivity
  have hgnear : ∀ p ∈ S, ∀ y : F, ‖y‖ ≤ M₀ + R₀ + 1 →
      |f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)| ≤ N₁ := by
    intro p hp y hy
    have hs0 : 0 < p.2.2 := (hSadm p hp).1
    have hfb : |f (toLp 2 (y, p.2.1))| ≤ N₀ :=
      hN₀ (y, p.2.1) ⟨mem_closedBall_zero_iff.mpr hy, hJmem p hp⟩
    have hq : ‖y‖ ^ 2 / (2 * p.2.2) ≤ (M₀ + R₀ + 1) ^ 2 / (2 * smin) := by
      have h1 : (0:ℝ) < 2 * smin := by linarith
      have hnum : ‖y‖ ^ 2 ≤ (M₀ + R₀ + 1) ^ 2 := by nlinarith [norm_nonneg y]
      have hden : 2 * smin ≤ 2 * p.2.2 := by linarith [hsmin p hp]
      gcongr
    have hpos : (0:ℝ) ≤ ‖y‖ ^ 2 / (2 * p.2.2) := by positivity
    rw [abs_le] at hfb ⊢
    rw [hN₁def]
    constructor <;> linarith [hfb.1, hfb.2]
  have hsne : smax ≠ 0 := ne_of_gt hsmax0
  -- completing the square, the load-bearing arithmetic step of (i)
  have hsquare : ∀ ρ a : ℝ, -(ρ ^ 2 / (4 * smax)) + a * ρ ≤ smax * a ^ 2 := by
    intro ρ a
    have h4 : (0:ℝ) < 4 * smax := by linarith
    have hid : smax * a ^ 2 - (-(ρ ^ 2 / (4 * smax)) + a * ρ)
        = (ρ - 2 * smax * a) ^ 2 / (4 * smax) := by field_simp; ring
    linarith [div_nonneg (sq_nonneg (ρ - 2 * smax * a)) h4.le]
  -- the uniform upper bound on competitors
  have hub : ∀ p ∈ S, ∀ A y : F,
      f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)
        ≤ max (N₁ + ‖A‖ * (M₀ + 2 * R₀ + 1)) (smax * ‖A‖ ^ 2 + ‖A‖ * R₀) := by
    intro p hp A y
    have hx : ‖p.1‖ ≤ R₀ := hR₀ p hp
    have hcs : -(inner ℝ A (y - p.1) : ℝ) ≤ ‖A‖ * ‖y - p.1‖ := by
      have := (abs_le.mp (abs_real_inner_le_norm A (y - p.1))).1; linarith
    rcases le_or_gt ‖y‖ (M₀ + R₀ + 1) with hy | hy
    · have h1 : f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) ≤ N₁ :=
        (abs_le.mp (hgnear p hp y hy)).2
      have hyx : ‖y - p.1‖ ≤ M₀ + 2 * R₀ + 1 := by have := norm_sub_le y p.1; linarith
      have h2 : ‖A‖ * ‖y - p.1‖ ≤ ‖A‖ * (M₀ + 2 * R₀ + 1) :=
        mul_le_mul_of_nonneg_left hyx (norm_nonneg A)
      exact le_trans (by linarith) (le_max_left _ _)
    · have hfar := hgfar p hp y (by linarith)
      have hyx : ‖y - p.1‖ ≤ ‖y‖ + R₀ := by have := norm_sub_le y p.1; linarith
      have h2 : ‖A‖ * ‖y - p.1‖ ≤ ‖A‖ * (‖y‖ + R₀) :=
        mul_le_mul_of_nonneg_left hyx (norm_nonneg A)
      refine le_trans ?_ (le_max_right _ _)
      nlinarith [hsquare ‖y‖ ‖A‖]
  -- (i): boundedness, proved FIRST so (ii) and (iii) may treat Γ as a genuine supremum
  have hbdd : ∀ p ∈ S, ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)} := by
    intro p hp A
    refine ⟨max (N₁ + ‖A‖ * (M₀ + 2 * R₀ + 1)) (smax * ‖A‖ ^ 2 + ‖A‖ * R₀), ?_⟩
    rintro w ⟨y, rfl⟩
    exact hub p hp A y
  have hnes : ∀ (p : F × ℝ × ℝ) (A : F), {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}.Nonempty :=
    fun p A => ⟨_, ⟨p.1, rfl⟩⟩
  have hlub : ∀ p ∈ S, ∀ A y : F,
      f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)
        ≤ sSup {w : ℝ | ∃ y' : F,
            w = f (toLp 2 (y', p.2.1)) - ‖y'‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y' - p.1)} :=
    fun p hp A y => le_csSup (hbdd p hp A) ⟨y, rfl⟩
  -- Γ(0) ≤ N₁
  have hΓ0 : ∀ p ∈ S, sSup {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ (0 : F) (y - p.1)} ≤ N₁ := by
    intro p hp
    refine csSup_le (hnes p 0) ?_
    rintro b ⟨y, rfl⟩
    simp only [inner_zero_left, sub_zero]
    rcases le_or_gt ‖y‖ (M₀ + R₀ + 1) with hy | hy
    · exact (abs_le.mp (hgnear p hp y hy)).2
    · have hfar := hgfar p hp y (by linarith)
      have : (0:ℝ) ≤ ‖y‖ ^ 2 / (4 * smax) := by positivity
      linarith
  -- Γ(A) ≥ ‖A‖ - N₁ for A ≠ 0, via the competitor x - A/‖A‖
  have hΓA : ∀ p ∈ S, ∀ A : F, A ≠ 0 → ‖A‖ - N₁ ≤ sSup {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)} := by
    intro p hp A hAne
    have hAn : ‖A‖ ≠ 0 := norm_ne_zero_iff.mpr hAne
    have hAn0 : 0 < ‖A‖ := norm_pos_iff.mpr hAne
    have hyA : ‖p.1 - ‖A‖⁻¹ • A‖ ≤ M₀ + R₀ + 1 := by
      have h1 : ‖p.1 - ‖A‖⁻¹ • A‖ ≤ ‖p.1‖ + ‖‖A‖⁻¹ • A‖ := norm_sub_le _ _
      have h2 : ‖‖A‖⁻¹ • A‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hAn]
      have h3 : ‖p.1‖ ≤ R₀ := hR₀ p hp
      rw [h2] at h1; linarith
    have hinner : (inner ℝ A ((p.1 - ‖A‖⁻¹ • A) - p.1) : ℝ) = -‖A‖ := by
      rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right,
        real_inner_self_eq_norm_sq]
      field_simp
    have hg := (abs_le.mp (hgnear p hp (p.1 - ‖A‖⁻¹ • A) hyA)).1
    have := hlub p hp A (p.1 - ‖A‖⁻¹ • A)
    rw [hinner] at this
    linarith
  -- Λ₀ and M
  obtain ⟨Λ₀, hΛ₀def⟩ : ∃ r : ℝ, r = 2 * N₁ + 1 := ⟨_, rfl⟩
  have hΛ₀0 : 0 ≤ Λ₀ := by rw [hΛ₀def]; linarith
  obtain ⟨M, hMdef⟩ : ∃ r : ℝ, r = max (M₀ + R₀ + 1)
      (max (8 * smax * (Λ₀ + 1)) (Real.sqrt (8 * smax * (N₁ + 1 + (Λ₀ + 1) * R₀)))) := ⟨_, rfl⟩
  have hM1 : M₀ + R₀ + 1 ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hM2 : 8 * smax * (Λ₀ + 1) ≤ M := by
    rw [hMdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hM3 : Real.sqrt (8 * smax * (N₁ + 1 + (Λ₀ + 1) * R₀)) ≤ M := by
    rw [hMdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hM0 : 0 < M := by linarith
  -- the far-field bound used by (iii)
  have hfaraway : ∀ p ∈ S, ∀ A : F, ‖A‖ ≤ Λ₀ + 1 → ∀ y : F, M ≤ ‖y‖ →
      f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1) ≤ -(N₁ + 1) := by
    intro p hp A hA y hy
    have hyp : 0 < ‖y‖ := by linarith
    have hfar := hgfar p hp y (by linarith)
    have hcs : -(inner ℝ A (y - p.1) : ℝ) ≤ ‖A‖ * ‖y - p.1‖ := by
      have := (abs_le.mp (abs_real_inner_le_norm A (y - p.1))).1; linarith
    have hyx : ‖y - p.1‖ ≤ ‖y‖ + R₀ := by
      have := norm_sub_le y p.1; linarith [hR₀ p hp]
    have hlin : -(inner ℝ A (y - p.1) : ℝ) ≤ (Λ₀ + 1) * (‖y‖ + R₀) :=
      le_trans hcs (mul_le_mul hA hyx (norm_nonneg _) (by linarith))
    have h4s : (0:ℝ) < 4 * smax := by linarith
    have hA1 : 2 * ((Λ₀ + 1) * ‖y‖) ≤ ‖y‖ ^ 2 / (4 * smax) := by
      rw [le_div_iff₀ h4s]
      nlinarith [mul_le_mul_of_nonneg_right (le_trans hM2 hy) (norm_nonneg y)]
    have hA2 : 2 * (N₁ + 1 + (Λ₀ + 1) * R₀) ≤ ‖y‖ ^ 2 / (4 * smax) := by
      rw [le_div_iff₀ h4s]
      have harg : (0:ℝ) ≤ 8 * smax * (N₁ + 1 + (Λ₀ + 1) * R₀) := by positivity
      nlinarith [Real.sq_sqrt harg, Real.sqrt_nonneg (8 * smax * (N₁ + 1 + (Λ₀ + 1) * R₀)),
        mul_self_le_mul_self (Real.sqrt_nonneg (8 * smax * (N₁ + 1 + (Λ₀ + 1) * R₀)))
          (le_trans hM3 hy)]
    linarith
  -- continuity of each competitor functional on the position ball
  have hcontball : ∀ p ∈ S, ∀ A : F, ContinuousOn
      (fun y : F => f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1))
      (closedBall (0 : F) M) := by
    intro p hp A
    have hfy : ContinuousOn (fun y : F => f (toLp 2 (y, p.2.1))) (closedBall (0 : F) M) :=
      hcont.comp (by fun_prop :
          Continuous (fun y : F => (toLp 2 (y, p.2.1) : WithLp 2 (F × ℝ)))).continuousOn
        (fun y _ => (hSadm p hp).2)
    have h1 : Continuous (fun y : F => ‖y‖ ^ 2 / (2 * p.2.2)) := by fun_prop
    have h2 : Continuous (fun y : F => (inner ℝ A (y - p.1) : ℝ)) := by fun_prop
    exact (hfy.sub h1.continuousOn).sub h2.continuousOn
  refine ⟨Λ₀, M, hΛ₀0, hM0, hbdd, ?_, ?_⟩
  · -- (ii)
    intro p hp A hA
    rcases eq_or_ne A 0 with rfl | hAne
    · rw [norm_zero]; linarith
    · have h1 := hΓA p hp A hAne
      have h2 := hΓ0 p hp
      rw [hΛ₀def]; linarith
  · -- (iii)
    intro p hp A hA
    obtain ⟨y₀, hy₀ball, hy₀max⟩ := (isCompact_closedBall (0 : F) M).exists_isMaxOn
      ⟨0, mem_closedBall_self hM0.le⟩ (hcontball p hp A)
    have hy₀M : ‖y₀‖ ≤ M := mem_closedBall_zero_iff.mp hy₀ball
    have hxball : p.1 ∈ closedBall (0 : F) M :=
      mem_closedBall_zero_iff.mpr (by linarith [hR₀ p hp])
    have hxle : f (toLp 2 (p.1, p.2.1)) - ‖p.1‖ ^ 2 / (2 * p.2.2) - inner ℝ A (p.1 - p.1)
        ≤ f (toLp 2 (y₀, p.2.1)) - ‖y₀‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y₀ - p.1) :=
      isMaxOn_iff.mp hy₀max p.1 hxball
    have hφx : -N₁ ≤ f (toLp 2 (p.1, p.2.1)) - ‖p.1‖ ^ 2 / (2 * p.2.2)
        - inner ℝ A (p.1 - p.1) := by
      have h := (abs_le.mp (hgnear p hp p.1 (by linarith [hR₀ p hp]))).1
      simp only [sub_self, inner_zero_right, sub_zero]
      linarith
    have hglobal : ∀ y : F,
        f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)
          ≤ f (toLp 2 (y₀, p.2.1)) - ‖y₀‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y₀ - p.1) := by
      intro y
      rcases le_or_gt ‖y‖ M with hy | hy
      · exact isMaxOn_iff.mp hy₀max y (mem_closedBall_zero_iff.mpr hy)
      · have h1 := hfaraway p hp A hA y hy.le
        linarith
    have hΓeq : sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
        = f (toLp 2 (y₀, p.2.1)) - ‖y₀‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y₀ - p.1) := by
      refine le_antisymm (csSup_le (hnes p A) ?_) (hlub p hp A y₀)
      rintro b ⟨y, rfl⟩
      exact hglobal y
    have hbddimg : BddAbove ((fun y : F => f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
        - inner ℝ A (y - p.1)) '' closedBall (0 : F) M) := by
      refine ⟨f (toLp 2 (y₀, p.2.1)) - ‖y₀‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y₀ - p.1), ?_⟩
      rintro b ⟨y, _, rfl⟩
      exact hglobal y
    have himg : sSup ((fun y : F => f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
          - inner ℝ A (y - p.1)) '' closedBall (0 : F) M)
        = f (toLp 2 (y₀, p.2.1)) - ‖y₀‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y₀ - p.1) := by
      refine le_antisymm (csSup_le ⟨_, ⟨y₀, hy₀ball, rfl⟩⟩ ?_)
        (le_csSup hbddimg ⟨y₀, hy₀ball, rfl⟩)
      rintro b ⟨y, _, rfl⟩
      exact hglobal y
    refine ⟨by rw [hΓeq, himg], ⟨y₀, hy₀M, hΓeq⟩, ?_⟩
    intro y hy
    by_contra hcon
    have h1 := hfaraway p hp A hA y (not_le.mp hcon).le
    rw [hΓeq] at hy
    linarith
