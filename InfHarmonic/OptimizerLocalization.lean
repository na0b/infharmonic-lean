module

public import InfHarmonic.EnvelopeCompetitorBounds
public import InfHarmonic.QuadEnvAttained

@[expose] public section
set_option maxHeartbeats 600000
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The uniform localization of the envelope optimizers of the proof of
Proposition 6.7: on a box `|x| ≤ R`, `δ_N ≤ t ≤ T` there is a single constant
`A ≥ 1` such that, for every length `ℓ ≤ min {1, δ_N/2}`, every optimizer of the
forward envelope of `W` and every optimizer of the backward envelope of `v` at a
center of the box lies within `2√(Aℓ)` of that center. -/
theorem OptimizerLocalization (v W : WithLp 2 (F × ℝ) → ℝ)
    (hvcont : Continuous v)
    (hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v)
    (hWcont : ContinuousOn W {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) W)
    (T R : ℝ) (hR : 2 ≤ R) (N : ℕ) (hN : 1 ≤ N) :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ l : ℝ, 0 < l → l ≤ min 1 ((1 / 2 : ℝ) ^ N / 2) →
        ∀ z : WithLp 2 (F × ℝ), ‖(ofLp z).1‖ ≤ R →
          (1 / 2 : ℝ) ^ N ≤ (ofLp z).2 → (ofLp z).2 ≤ T →
          ∀ y : F,
            (QuadEnvP W l z
                = W (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l) →
              ‖y - (ofLp z).1‖ ≤ 2 * Real.sqrt (A * l)) ∧
            (QuadEnvM v l z
                = v (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) →
              ‖y - (ofLp z).1‖ ≤ 2 * Real.sqrt (A * l)) := by
  classical
  -- the time window `J` and the boxes
  set d : ℝ := (1 / 2 : ℝ) ^ N with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdhalf : d ≤ 1 / 2 := by
    rw [hd]
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ 1 := by
          refine pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
      _ = 1 / 2 := by norm_num
  set J : Set ℝ := Set.Icc (d / 2) (T + 1) with hJ
  have hJc : IsCompact J := by rw [hJ]; exact isCompact_Icc
  have hJpos : ∀ s ∈ J, 0 < s := by
    intro s hs
    rw [hJ] at hs
    exact lt_of_lt_of_le (by linarith : (0:ℝ) < d / 2) hs.1
  have hJsub : J ⊆ Set.Ioi (0 : ℝ) := fun s hs => hJpos s hs
  -- the compact boxes and the bound they carry
  have hboxc : ∀ r : ℝ, IsCompact ((fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
      (Metric.closedBall (0 : F) r ×ˢ J)) := by
    intro r
    refine IsCompact.image ((isCompact_closedBall (0 : F) r).prod hJc) ?_
    exact WithLp.prod_continuous_toLp 2 F ℝ
  have hboxmem : ∀ (r : ℝ) (y : F) (s : ℝ), ‖y‖ ≤ r → s ∈ J →
      (toLp 2 (y, s) : WithLp 2 (F × ℝ))
        ∈ (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
            (Metric.closedBall (0 : F) r ×ˢ J) :=
    fun r y s hy hs => ⟨(y, s), ⟨by simpa using hy, hs⟩, rfl⟩
  -- `W` is continuous on each box
  have hWbox : ∀ r : ℝ, ContinuousOn W ((fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
      (Metric.closedBall (0 : F) r ×ˢ J)) := by
    intro r
    refine hWcont.mono ?_
    rintro _ ⟨⟨y, s⟩, ⟨-, hs⟩, rfl⟩
    exact hJpos s hs
  have hvbox : ∀ r : ℝ, ContinuousOn v ((fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
      (Metric.closedBall (0 : F) r ×ˢ J)) := fun r => hvcont.continuousOn
  -- the elementary quadratic inequality
  have hquad : ∀ y x : F, ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
    intro y x
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
        _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    nlinarith [norm_nonneg (y - x), norm_nonneg x, sq_nonneg (‖y - x‖ - ‖x‖), norm_nonneg y]
  have hR0 : (0 : ℝ) ≤ R := by linarith
  -- ## the forward constants
  obtain ⟨M1, hM10, hM1⟩ := hWgrow J hJsub hJc (1 / 8) (by norm_num)
  obtain ⟨A1', hA1'⟩ := (hboxc (max M1 R)).exists_bound_of_continuousOn (hWbox (max M1 R))
  set A1 : ℝ := max A1' 1 with hA1def
  have hA10 : (1 : ℝ) ≤ A1 := le_max_right _ _
  have hA1 : ∀ (y : F) (s : ℝ), ‖y‖ ≤ max M1 R → s ∈ J → |W (toLp 2 (y, s))| ≤ A1 := by
    intro y s hy hs
    have h := hA1' _ (hboxmem _ y s hy hs)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  set M2 : ℝ := max (max M1 (Real.sqrt (8 * A1 + 4 * R ^ 2))) R with hM2def
  obtain ⟨Ap', hAp'⟩ := (hboxc M2).exists_bound_of_continuousOn (hWbox M2)
  set Ap : ℝ := max Ap' 1 with hApdef
  have hAp0 : (1 : ℝ) ≤ Ap := le_max_right _ _
  have hAp : ∀ (y : F) (s : ℝ), ‖y‖ ≤ M2 → s ∈ J → |W (toLp 2 (y, s))| ≤ Ap := by
    intro y s hy hs
    have h := hAp' _ (hboxmem _ y s hy hs)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  -- ## the backward constants
  obtain ⟨M3, hM30, hM3⟩ := hvgrow J (Set.subset_univ _) hJc (1 / 8) (by norm_num)
  obtain ⟨A3', hA3'⟩ := (hboxc (max M3 R)).exists_bound_of_continuousOn (hvbox (max M3 R))
  set A3 : ℝ := max A3' 1 with hA3def
  have hA30 : (1 : ℝ) ≤ A3 := le_max_right _ _
  have hA3 : ∀ (y : F) (s : ℝ), ‖y‖ ≤ max M3 R → s ∈ J → |v (toLp 2 (y, s))| ≤ A3 := by
    intro y s hy hs
    have h := hA3' _ (hboxmem _ y s hy hs)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  set M4 : ℝ := max (max M3 (Real.sqrt (8 * A3 + 4 * R ^ 2))) R with hM4def
  obtain ⟨Am', hAm'⟩ := (hboxc M4).exists_bound_of_continuousOn (hvbox M4)
  set Am : ℝ := max Am' 1 with hAmdef
  have hAm0 : (1 : ℝ) ≤ Am := le_max_right _ _
  have hAm : ∀ (y : F) (s : ℝ), ‖y‖ ≤ M4 → s ∈ J → |v (toLp 2 (y, s))| ≤ Am := by
    intro y s hy hs
    have h := hAm' _ (hboxmem _ y s hy hs)
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  -- ## the constant
  refine ⟨max Ap Am, le_trans hAp0 (le_max_left _ _), ?_⟩
  intro l hl0 hlmin z hx hdt htT y
  have hl1 : l ≤ 1 := le_trans hlmin (min_le_left _ _)
  have hl2 : l ≤ d / 2 := le_trans hlmin (min_le_right _ _)
  have ht0 : 0 < (ofLp z).2 := lt_of_lt_of_le hd0 hdt
  have htlJ : (ofLp z).2 + l ∈ J := by
    rw [hJ]
    exact ⟨by linarith, by linarith⟩
  have htmJ : (ofLp z).2 - l ∈ J := by
    rw [hJ]
    exact ⟨by linarith, by linarith⟩
  have hsqrtstep : ∀ (u A : ℝ), 0 ≤ u → 1 ≤ A → u ^ 2 ≤ 4 * (A * l) →
      u ≤ 2 * Real.sqrt (A * l) := by
    intro u A hu hA h
    have h2 : Real.sqrt (4 * (A * l)) = 2 * Real.sqrt (A * l) := by
      rw [show (4 : ℝ) * (A * l) = 2 ^ 2 * (A * l) by ring, Real.sqrt_mul (by norm_num),
        Real.sqrt_sq (by norm_num)]
    calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu).symm
      _ ≤ Real.sqrt (4 * (A * l)) := Real.sqrt_le_sqrt h
      _ = 2 * Real.sqrt (A * l) := h2
  constructor
  · -- the forward implication
    intro hy
    have hdom := ((EnvelopeCompetitorBounds (Set.Ioi (0 : ℝ)) W hWcont hWgrow).1 l z hl0
      (by exact ht0) (by exact hJpos _ htlJ)).1 (ofLp z).1
    have hz0 : ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l) = 0 := by
      rw [sub_self, norm_zero]
      simp
    rw [hz0, sub_zero, hy] at hdom
    have hcmp : ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
        ≤ W (toLp 2 (y, (ofLp z).2 + l)) - W (toLp 2 ((ofLp z).1, (ofLp z).2 + l)) := by
      linarith
    have hyM2 : ‖y‖ ≤ M2 := by
      rcases le_or_gt ‖y‖ M1 with hc | hc
      · exact le_trans hc (le_trans (le_max_left _ _) (le_max_left _ _))
      · have hfar := hM1 (toLp 2 (y, (ofLp z).2 + l)) (by simpa using hc.le) (by simpa using htlJ)
        have hnear := hA1 (ofLp z).1 ((ofLp z).2 + l)
          (le_trans hx (le_max_right _ _)) htlJ
        have hab1 := abs_le.mp hfar
        have hab2 := abs_le.mp hnear
        have hq := hquad y (ofLp z).1
        have hdiv : ‖y - (ofLp z).1‖ ^ 2 / 2 ≤ ‖y - (ofLp z).1‖ ^ 2 / (2 * l) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith : (0:ℝ) < 2 * l)
          linarith
        have hub : ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ (1 / 8) * ‖y‖ ^ 2 + A1 := by
          linarith [hcmp, hab1.2, hab2.1]
        have hxR : ‖(ofLp z).1‖ ^ 2 ≤ R ^ 2 := by
          have := norm_nonneg (ofLp z).1
          nlinarith
        have hy2 : ‖y‖ ^ 2 ≤ 8 * A1 + 4 * R ^ 2 := by nlinarith
        have : ‖y‖ ≤ Real.sqrt (8 * A1 + 4 * R ^ 2) :=
          (Real.le_sqrt (norm_nonneg y) (by nlinarith [sq_nonneg R])).mpr hy2
        exact le_trans this (le_trans (le_max_right _ _) (le_max_left _ _))
    have h1 := hAp y ((ofLp z).2 + l) hyM2 htlJ
    have h2 := hAp (ofLp z).1 ((ofLp z).2 + l)
      (le_trans hx (le_max_right _ _)) htlJ
    have hab1 := abs_le.mp h1
    have hab2 := abs_le.mp h2
    have hfin : ‖y - (ofLp z).1‖ ^ 2 ≤ 4 * (max Ap Am * l) := by
      have hdd : ‖y - (ofLp z).1‖ ^ 2 ≤ 2 * Ap * (2 * l) := by
        have h3 : ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ 2 * Ap := by
          linarith [hcmp, hab1.2, hab2.1]
        exact (div_le_iff₀ (by linarith : (0:ℝ) < 2 * l)).mp h3
      have hApA : Ap ≤ max Ap Am := le_max_left _ _
      nlinarith [hl0.le]
    exact hsqrtstep _ _ (norm_nonneg _) (le_trans hAp0 (le_max_left _ _)) hfin
  · -- the backward implication
    intro hy
    have hdom := ((EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont.continuousOn hvgrow).2.1
      l z hl0 (Set.mem_univ _) (Set.mem_univ _)).1 (ofLp z).1
    have hz0 : ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l) = 0 := by
      rw [sub_self, norm_zero]
      simp
    rw [hz0, add_zero, hy] at hdom
    have hcmp : ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
        ≤ v (toLp 2 ((ofLp z).1, (ofLp z).2 - l)) - v (toLp 2 (y, (ofLp z).2 - l)) := by
      linarith
    have hyM4 : ‖y‖ ≤ M4 := by
      rcases le_or_gt ‖y‖ M3 with hc | hc
      · exact le_trans hc (le_trans (le_max_left _ _) (le_max_left _ _))
      · have hfar := hM3 (toLp 2 (y, (ofLp z).2 - l)) (by simpa using hc.le) (by simpa using htmJ)
        have hnear := hA3 (ofLp z).1 ((ofLp z).2 - l)
          (le_trans hx (le_max_right _ _)) htmJ
        have hab1 := abs_le.mp hfar
        have hab2 := abs_le.mp hnear
        have hq := hquad y (ofLp z).1
        have hdiv : ‖y - (ofLp z).1‖ ^ 2 / 2 ≤ ‖y - (ofLp z).1‖ ^ 2 / (2 * l) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by linarith : (0:ℝ) < 2 * l)
          linarith
        have hxR : ‖(ofLp z).1‖ ^ 2 ≤ R ^ 2 := by
          have := norm_nonneg (ofLp z).1
          nlinarith
        have hy2 : ‖y‖ ^ 2 ≤ 8 * A3 + 4 * R ^ 2 := by nlinarith [hcmp, hab1.1, hab2.2]
        have : ‖y‖ ≤ Real.sqrt (8 * A3 + 4 * R ^ 2) :=
          (Real.le_sqrt (norm_nonneg y) (by nlinarith [sq_nonneg R])).mpr hy2
        exact le_trans this (le_trans (le_max_right _ _) (le_max_left _ _))
    have h1 := hAm y ((ofLp z).2 - l) hyM4 htmJ
    have h2 := hAm (ofLp z).1 ((ofLp z).2 - l)
      (le_trans hx (le_max_right _ _)) htmJ
    have hab1 := abs_le.mp h1
    have hab2 := abs_le.mp h2
    have hfin : ‖y - (ofLp z).1‖ ^ 2 ≤ 4 * (max Ap Am * l) := by
      have hdd : ‖y - (ofLp z).1‖ ^ 2 ≤ 2 * Am * (2 * l) := by
        have h3 : ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ 2 * Am := by
          linarith [hcmp, hab1.1, hab2.2]
        exact (div_le_iff₀ (by linarith : (0:ℝ) < 2 * l)).mp h3
      have hAmA : Am ≤ max Ap Am := le_max_right _ _
      nlinarith [hl0.le]
    exact hsqrtstep _ _ (norm_nonneg _) (le_trans hAp0 (le_max_left _ _)) hfin
