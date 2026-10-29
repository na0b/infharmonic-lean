import InfHarmonic.Preamble
set_option maxHeartbeats 400000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 7 of Proposition 6.7, part 3 (`MarkLocalization`): the frame travel
bound on the portion from a mark to that portion's stopping time.

The travel package of the stopped contact walk --- here the hypothesis
`hwtravel`, whose source is \noderef{StoppedWalkTravel} and which is not
re-derived --- gives, for any two stopping times `ρ ≤ σ ≤ τ` and any bounded
`𝒢`-adapted slope field `p`, four integrability facts and the Cauchy--Schwarz
travel inequality for the running displacement
`sup_{ρ ≤ n ≤ σ} r⁻¹ |x_n - x_ρ - (t_n - t_ρ) p|` in the sheared frame of slope
`p` and scale `r`. This node instantiates it twice --- once at the portion
`(σ_j, ς)` with the mark's fitted slope `p_j`, and once at the whole walk
`(0, τ)` with the zero slope, the latter only to bound the error sum over the
portion by the error sum over the walk --- and then bounds the three terms on
the right of the travel inequality.

The velocity term is bounded by `C_M L_K²`: on the event where the mark sits at
the level `r` the velocity deviation at an interior lattice site obeys
`|Q_0(n) - p_j| ≤ C_2(L_K + |log((ε/r) S_n)|)`, so the squared deviation is at
most `C_2²(2 L_K² + 2|log((ε/r) S_n)|²)`, and summing over the portion turns the
two halves into the time budget and the logarithmic grid sum; off that event the
portion is empty. The error term is bounded by `B_0`, the budget of the whole
walk, because the portion's index range sits inside the walk's. The time term is
bounded by `16`, because `(ε/r) bb = 8` converts the time budget `bb²/4` into
that constant. Feeding the three into the travel inequality and using
`2√C_M ≤ C'` and `4 ≤ C'` gives the bound `C'(L_K + √B_0)`.

The two conclusions are the integrability of the running displacement over the
portion and that quantitative bound; they are exactly what the cutoff-probability
step consumes. The ambient space is an arbitrary finite-dimensional real
inner-product space `F`. -/
theorem MarkFrameTravelBound {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
    (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (S : ℕ → Ω → ℤ)
    (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (tau' τ : Ω → ℕ) (j : ℕ) (bb : ℕ)
    (ε r Cp B₀ C' CM C₂ LK Λ : ℝ) (uw : ℤ → ℝ)
    (hwtravel :
      ∀ (ρ σ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ρ ω : ℕ∞)) →
          IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) →
          ∀ hρσ : (∀ ω, ρ ω ≤ σ ω), (∀ ω, σ ω ≤ τ ω) →
          ∀ (p : Ω → F) (Cp r : ℝ), 0 < r → (∀ ω, ‖p ω‖ ≤ Cp) →
          (∀ n, StronglyMeasurable[𝒢 n] (fun ω => if ρ ω ≤ n then p ω else 0)) →
          Integrable (fun ω => (Finset.Icc (ρ ω) (σ ω)).sup'
              (Finset.nonempty_Icc.mpr (hρσ ω))
              (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
                - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖)) μ ∧
          Integrable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
              (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) μ ∧
          Integrable (fun ω => (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ))) μ ∧
          Integrable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
              (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
                + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) μ ∧
          ∫ ω, (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
              (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
                - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖) ∂μ
            ≤ 2 * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                  (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ)
              + Real.sqrt (∫ ω, (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)) ∂μ)
                * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                    (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
                      + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1)
                          - Q₀ n ω‖ ^ 2)) ∂μ))
    (hpbd : ∀ ω, ‖pj j ω‖ ≤ Cp)
    (hσst : IsStoppingTime 𝒢 (fun ω => (smark j ω : ℕ∞)))
    (htau'st : IsStoppingTime 𝒢 (fun ω => (tau' ω : ℕ∞)))
    (hτst : IsStoppingTime 𝒢 (fun ω => (τ ω : ℕ∞)))
    (hσtau' : ∀ ω, smark j ω ≤ tau' ω) (htau'τ : ∀ ω, tau' ω ≤ τ ω)
    (hpmeasG : ∀ n, StronglyMeasurable[𝒢 n]
      (fun ω => if smark j ω ≤ n then pj j ω else 0))
    (hnstint : Integrable (fun ω => ((tau' ω - smark j ω : ℕ) : ℝ)) μ)
    (huwsumint' : Integrable
      (fun ω => ∑ m ∈ Finset.Ico (smark j ω) (tau' ω), uw (S m ω)) μ)
    (hlogsum : ∫ ω, (∑ m ∈ Finset.Ico (smark j ω) (tau' ω), uw (S m ω)) ∂μ ≤ 4 * Λ)
    (huwvalh : ∀ (n : ℕ) (ω : Ω), smark j ω ≤ n → n < tau' ω →
      uw (S n ω) = (ε / r) ^ 2 * |Real.log ((ε / r) * (S n ω : ℝ))| ^ 2)
    (hQ'bd : ∀ (n : ℕ) (ω : Ω), (ofLp (z (smark j ω) ω)).2 = r → smark j ω ≤ n →
      n < tau' ω → ‖Q₀ n ω - pj j ω‖ ≤ C₂ * (LK + |Real.log ((ε / r) * (S n ω : ℝ))|))
    (htau'off : ∀ ω, ¬ ((ofLp (z (smark j ω) ω)).2 = r) → tau' ω = smark j ω)
    (htimebudget : ∫ ω, ((tau' ω - smark j ω : ℕ) : ℝ) ∂μ ≤ (bb:ℝ) ^ 2 / 4)
    (hbudgetB : ∫ ω, (∑ n ∈ Finset.range (τ ω),
      (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ ≤ B₀)
    (hr0 : (0:ℝ) < r) (hεrbb : (ε / r) * (bb:ℝ) = 8)
    (hCMd : CM = 2 * C₂ ^ 2 * (16 + 4 * Λ)) (hCM0 : (0:ℝ) ≤ CM)
    (hC₂0 : (0:ℝ) < C₂) (hΛ0 : (0:ℝ) ≤ Λ)
    (hC'CM : 2 * Real.sqrt CM ≤ C') (hC'4 : (4:ℝ) ≤ C')
    (hLK1 : (1:ℝ) ≤ LK) :
    Integrable (fun ω => (Finset.Icc (smark j ω) (tau' ω)).sup'
        (Finset.nonempty_Icc.mpr (hσtau' ω))
        (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
          - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖)) μ ∧
      ∫ ω, (Finset.Icc (smark j ω) (tau' ω)).sup'
          (Finset.nonempty_Icc.mpr (hσtau' ω))
          (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
            - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖) ∂μ
        ≤ C' * (LK + Real.sqrt B₀) := by
  have h0st : IsStoppingTime 𝒢 (fun ω => (((fun _ => (0:ℕ)) ω : ℕ) : ℕ∞)) := by
    intro n
    have h1 : MeasurableSet[𝒢 n] (Set.univ : Set Ω) := MeasurableSet.univ
    simp
  have hpmeas0 : ∀ n, StronglyMeasurable[𝒢 n]
      (fun ω => if (fun _ => (0:ℕ)) ω ≤ n then (fun _ => (0:F)) ω else 0) := by
    intro n
    simp only
    exact stronglyMeasurable_const
  obtain ⟨hI1, hI2, hI3, hI4, htrav⟩ := hwtravel (smark j) tau' hσst htau'st hσtau' htau'τ
    (pj j) Cp r hr0 hpbd hpmeasG
  obtain ⟨-, -, -, hJ4, -⟩ := hwtravel (fun _ => (0:ℕ)) τ h0st hτst
    (fun ω => Nat.zero_le _) (fun ω => le_rfl) (fun _ => (0:F)) 0 1 one_pos
    (fun ω => by show ‖(0:F)‖ ≤ 0; simp) hpmeas0
  -- the velocity budget on the portion
  have hvelbd : ∫ ω, (∑ m ∈ Finset.Ico (smark j ω) (tau' ω),
      (ε / r) ^ 2 * ‖Q₀ m ω - pj j ω‖ ^ 2) ∂μ ≤ CM * LK ^ 2 := by
    have hrhsint : Integrable (fun ω => 2 * C₂ ^ 2 * LK ^ 2 *
        ((ε / r) ^ 2 * ((tau' ω - smark j ω : ℕ) : ℝ))
        + 2 * C₂ ^ 2 * (∑ m ∈ Finset.Ico (smark j ω) (tau' ω), uw (S m ω))) μ :=
      ((hnstint.const_mul ((ε / r) ^ 2)).const_mul (2 * C₂ ^ 2 * LK ^ 2)).add
        (huwsumint'.const_mul (2 * C₂ ^ 2))
    have hptle : ∀ ω, ∑ m ∈ Finset.Ico (smark j ω) (tau' ω),
        (ε / r) ^ 2 * ‖Q₀ m ω - pj j ω‖ ^ 2
        ≤ 2 * C₂ ^ 2 * LK ^ 2 * ((ε / r) ^ 2 * ((tau' ω - smark j ω : ℕ) : ℝ))
          + 2 * C₂ ^ 2 * (∑ m ∈ Finset.Ico (smark j ω) (tau' ω), uw (S m ω)) := by
      intro ω
      by_cases hR : (ofLp (z (smark j ω) ω)).2 = r
      · have hterm : ∀ m ∈ Finset.Ico (smark j ω) (tau' ω),
            (ε / r) ^ 2 * ‖Q₀ m ω - pj j ω‖ ^ 2
            ≤ 2 * C₂ ^ 2 * LK ^ 2 * (ε / r) ^ 2 + 2 * C₂ ^ 2 * uw (S m ω) := by
          intro m hm
          obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
          have h1 := hQ'bd m ω hR hm1 hm2
          have huwval : uw (S m ω) = (ε / r) ^ 2 * |Real.log ((ε / r) * (S m ω : ℝ))| ^ 2 :=
            huwvalh m ω hm1 hm2
          have h2 : (0:ℝ) ≤ ‖Q₀ m ω - pj j ω‖ := norm_nonneg _
          have h3 := mul_self_le_mul_self h2 h1
          have h4 : (0:ℝ) ≤ (ε / r) ^ 2 := sq_nonneg _
          have h5 : ‖Q₀ m ω - pj j ω‖ ^ 2
              ≤ C₂ ^ 2 * (2 * LK ^ 2 + 2 * |Real.log ((ε / r) * (S m ω : ℝ))| ^ 2) := by
            nlinarith only [h3, sq_nonneg (LK - |Real.log ((ε / r) * (S m ω : ℝ))|),
              sq_nonneg C₂, hC₂0]
          have h6 := mul_le_mul_of_nonneg_left h5 h4
          rw [huwval]
          nlinarith only [h6]
        have hsum := Finset.sum_le_sum hterm
        have heq : ∑ _m ∈ Finset.Ico (smark j ω) (tau' ω),
            (2 * C₂ ^ 2 * LK ^ 2 * (ε / r) ^ 2 + 2 * C₂ ^ 2 * uw (S _m ω))
            = 2 * C₂ ^ 2 * LK ^ 2 * ((ε / r) ^ 2 * ((tau' ω - smark j ω : ℕ) : ℝ))
              + 2 * C₂ ^ 2 * (∑ m ∈ Finset.Ico (smark j ω) (tau' ω), uw (S m ω)) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
            ← Finset.mul_sum]
          ring
        rw [heq] at hsum
        exact hsum
      · have hτ'σ : tau' ω = smark j ω := htau'off ω hR
        rw [hτ'σ]
        simp only [Finset.Ico_self, Finset.sum_empty]
        have h1 : (0:ℝ) ≤ 2 * C₂ ^ 2 * LK ^ 2 * ((ε / r) ^ 2
            * ((smark j ω - smark j ω : ℕ) : ℝ)) := by positivity
        have h2 : (0:ℝ) ≤ 2 * C₂ ^ 2 * (0:ℝ) := by positivity
        simp only [Nat.sub_self, Nat.cast_zero, mul_zero, add_zero]
        norm_num
    have h7 := integral_mono hI2 hrhsint hptle
    rw [integral_add ((hnstint.const_mul ((ε / r) ^ 2)).const_mul (2 * C₂ ^ 2 * LK ^ 2))
      (huwsumint'.const_mul (2 * C₂ ^ 2)), integral_const_mul, integral_const_mul,
      integral_const_mul] at h7
    have h8 : (ε / r) ^ 2 * ∫ ω, ((tau' ω - smark j ω : ℕ) : ℝ) ∂μ ≤ 16 := by
      have h9 : (0:ℝ) ≤ (ε / r) ^ 2 := sq_nonneg _
      have h10 := mul_le_mul_of_nonneg_left htimebudget h9
      have h11 : (ε / r) ^ 2 * ((bb:ℝ) ^ 2 / 4) = 16 := by
        have h12 : ((ε / r) * (bb:ℝ)) ^ 2 = 64 := by rw [hεrbb]; norm_num
        nlinarith only [h12]
      linarith only [h10, h11]
    have h13 : (0:ℝ) ≤ 2 * C₂ ^ 2 * LK ^ 2 := by positivity
    have h14 : 2 * C₂ ^ 2 * LK ^ 2 * ((ε / r) ^ 2 * ∫ ω, ((tau' ω - smark j ω : ℕ) : ℝ) ∂μ)
        ≤ 2 * C₂ ^ 2 * LK ^ 2 * 16 := mul_le_mul_of_nonneg_left h8 h13
    have h15 : (0:ℝ) ≤ 2 * C₂ ^ 2 := by positivity
    have h16 : 2 * C₂ ^ 2 * (∫ ω, (∑ m ∈ Finset.Ico (smark j ω) (tau' ω), uw (S m ω)) ∂μ)
        ≤ 2 * C₂ ^ 2 * (4 * Λ) := mul_le_mul_of_nonneg_left hlogsum h15
    have h17 : (1:ℝ) ≤ LK ^ 2 := by nlinarith only [hLK1]
    have h18 : (0:ℝ) ≤ 8 * C₂ ^ 2 * Λ := by positivity
    rw [hCMd]
    nlinarith only [h7, h14, h16, h17, h18]
  -- the error budget on the portion
  have herrbd : ∫ ω, (∑ n ∈ Finset.Ico (smark j ω) (tau' ω),
      (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ ≤ B₀ := by
    have hpt : ∀ ω, (∑ n ∈ Finset.Ico (smark j ω) (tau' ω),
        (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2))
        ≤ ∑ n ∈ Finset.Ico ((fun _ => (0:ℕ)) ω) (τ ω),
          (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
            + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2) := by
      intro ω
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
      refine Finset.Ico_subset_Ico (Nat.zero_le _) ?_
      exact htau'τ ω
    have h1 := integral_mono hI4 hJ4 hpt
    have h2 : ∫ ω, (∑ n ∈ Finset.Ico ((fun _ => (0:ℕ)) ω) (τ ω),
        (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ
        = ∫ ω, (∑ n ∈ Finset.range (τ ω),
          (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
            + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
      simp only [Finset.range_eq_Ico]
    rw [h2] at h1
    linarith only [h1, hbudgetB]
  -- the time budget in the form the travel bound uses
  have htimebd16 : ∫ ω, (ε / r) ^ 2 * ((tau' ω : ℝ) - ((smark j ω : ℕ) : ℝ)) ∂μ ≤ 16 := by
    have he : ∀ ω, (ε / r) ^ 2 * ((tau' ω : ℝ) - ((smark j ω : ℕ) : ℝ))
        = (ε / r) ^ 2 * ((tau' ω - smark j ω : ℕ) : ℝ) := by
      intro ω
      congr 1
      have h1 : smark j ω ≤ tau' ω := hσtau' ω
      rw [Nat.cast_sub h1]
    rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_const_mul]
    have h9 : (0:ℝ) ≤ (ε / r) ^ 2 := sq_nonneg _
    have h10 := mul_le_mul_of_nonneg_left htimebudget h9
    have h11 : (ε / r) ^ 2 * ((bb:ℝ) ^ 2 / 4) = 16 := by
      have h12 : ((ε / r) * (bb:ℝ)) ^ 2 = 64 := by rw [hεrbb]; norm_num
      nlinarith only [h12]
    linarith only [h10, h11]
  -- the travel bound
  have htravbd : ∫ ω, (Finset.Icc (smark j ω) (tau' ω)).sup'
      (Finset.nonempty_Icc.mpr (hσtau' ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖) ∂μ
      ≤ C' * (LK + Real.sqrt B₀) := by
    refine le_trans htrav ?_
    have e1 := Real.sqrt_le_sqrt hvelbd
    have e2 := Real.sqrt_le_sqrt htimebd16
    have e3 := Real.sqrt_le_sqrt herrbd
    have e4 : Real.sqrt (CM * LK ^ 2) = Real.sqrt CM * LK := by
      rw [Real.sqrt_mul hCM0, Real.sqrt_sq (by linarith only [hLK1])]
    have e5 : Real.sqrt (16:ℝ) = 4 := by
      rw [show (16:ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [e4] at e1
    rw [e5] at e2
    have e6 : (0:ℝ) ≤ Real.sqrt B₀ := Real.sqrt_nonneg B₀
    have e7 : (0:ℝ) ≤ Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (smark j ω) (tau' ω),
        (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ) :=
      Real.sqrt_nonneg _
    have e8 : (0:ℝ) ≤ Real.sqrt (∫ ω, (ε / r) ^ 2
        * ((tau' ω : ℝ) - ((smark j ω : ℕ) : ℝ)) ∂μ) := Real.sqrt_nonneg _
    have e9 : Real.sqrt (∫ ω, (ε / r) ^ 2 * ((tau' ω : ℝ) - ((smark j ω : ℕ) : ℝ)) ∂μ)
        * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (smark j ω) (tau' ω),
          (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
            + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ)
        ≤ 4 * Real.sqrt B₀ := mul_le_mul e2 e3 e7 (by norm_num)
    have e10 : (0:ℝ) ≤ LK := by linarith only [hLK1]
    nlinarith only [e1, e9, hC'CM, hC'4, e6, e10]
  exact ⟨hI1, htravbd⟩
