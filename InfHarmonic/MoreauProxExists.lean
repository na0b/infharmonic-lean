import InfHarmonic.IsMoreauProx
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A real convex function on all of `E` admits a proximal map. -/
theorem MoreauProxExists (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) :
    ∃ u : E → E, IsMoreauProx ψ u := by
  -- `ψ` is convex and real-valued on the open set `E`, hence continuous (preamble)
  have hcont : Continuous ψ := continuousOn_univ.1 (hψ.continuousOn isOpen_univ)
  -- eq:mpe-minorant, in the form the rest of the proof uses: `ψ x ≥ -a‖x‖ + c` with `a ≥ 0`
  obtain ⟨a, c, ha0, hmin⟩ : ∃ a c : ℝ, 0 ≤ a ∧ ∀ x : E, -a * ‖x‖ + c ≤ ψ x := by
    obtain ⟨w, -, hwmin'⟩ := IsCompact.exists_isMinOn (f := ψ)
      (isCompact_closedBall (0:E) 1) ⟨0, by simp⟩ hcont.continuousOn
    have hwmin : ∀ z ∈ Metric.closedBall (0:E) 1, ψ w ≤ ψ z := fun z hz => hwmin' hz
    have h0 : ψ w ≤ ψ 0 := hwmin 0 (by simp)
    refine ⟨ψ 0 - ψ w, ψ w, sub_nonneg.mpr h0, fun x => ?_⟩
    rcases le_or_gt ‖x‖ 1 with hle | hgt
    · have h1 : ψ w ≤ ψ x := hwmin x (by simpa [Metric.mem_closedBall, dist_zero_right] using hle)
      have h2 : 0 ≤ (ψ 0 - ψ w) * ‖x‖ := mul_nonneg (sub_nonneg.mpr h0) (norm_nonneg x)
      linarith only [h1, h2]
    · -- convexity along the ray from `0` through `x`, at the unit-sphere point `x / ‖x‖`
      have hxpos : (0:ℝ) < ‖x‖ := by linarith only [hgt]
      have hinv : ‖x‖⁻¹ • x ∈ Metric.closedBall (0:E) 1 := by
        simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv,
          Real.norm_eq_abs, abs_of_pos hxpos]
        rw [inv_mul_cancel₀ (ne_of_gt hxpos)]
      have hi0 : (0:ℝ) ≤ ‖x‖⁻¹ := le_of_lt (inv_pos.mpr hxpos)
      have hi1 : (0:ℝ) ≤ 1 - ‖x‖⁻¹ := by
        have hle1 : ‖x‖⁻¹ ≤ 1 := by rw [inv_le_one_iff₀]; right; linarith only [hgt]
        linarith only [hle1]
      have hconv := hψ.2 (Set.mem_univ x) (Set.mem_univ (0:E)) hi0 hi1 (by ring)
      rw [smul_zero, add_zero] at hconv
      have hwle : ψ w ≤ ‖x‖⁻¹ * ψ x + (1 - ‖x‖⁻¹) * ψ 0 := le_trans (hwmin _ hinv) hconv
      have hscaled := mul_le_mul_of_nonneg_left hwle hxpos.le
      have e1 : ‖x‖ * (‖x‖⁻¹ * ψ x + (1 - ‖x‖⁻¹) * ψ 0) = ψ x + ‖x‖ * ψ 0 - ψ 0 := by
        field_simp
        ring
      rw [e1] at hscaled
      linarith only [hscaled, h0]
  -- for each `y`, `Θ y` attains its infimum over `E`: eq:mpe-min
  have key : ∀ y : E, ∃ x : E, ∀ x' : E,
      ψ x + ‖x - y‖ ^ 2 / 2 ≤ ψ x' + ‖x' - y‖ ^ 2 / 2 := by
    intro y
    have hΘcont : Continuous (fun x : E => ψ x + ‖x - y‖ ^ 2 / 2) :=
      hcont.add (((continuous_id.sub continuous_const).norm.pow 2).div_const 2)
    refine hΘcont.exists_forall_le' y ?_
    -- the explicit coercivity radius, so no asymptotic argument is needed
    obtain ⟨M, hM1, hM2⟩ : ∃ M : ℝ, 2 * (a + 1) ≤ M ∧ (ψ y - c) + a * ‖y‖ + 1 ≤ M :=
      ⟨max (2 * (a + 1)) ((ψ y - c) + a * ‖y‖ + 1), le_max_left _ _, le_max_right _ _⟩
    refine Metric.mem_cocompact_of_closedBall_compl_subset (0:E) ⟨‖y‖ + M, ?_⟩
    intro x hx
    have hxR : ‖y‖ + M < ‖x‖ := by
      simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hx
    -- `t = ‖x‖ - ‖y‖` as an atom, with exactly the facts used
    obtain ⟨t, htpos, htM, htx, htn⟩ :
        ∃ t : ℝ, 0 < t ∧ M < t ∧ ‖x‖ = t + ‖y‖ ∧ t ≤ ‖x - y‖ := by
      refine ⟨‖x‖ - ‖y‖, ?_, by linarith only [hxR], by ring, norm_sub_norm_le x y⟩
      have : (0:ℝ) < M := by linarith only [hM1, ha0]
      linarith only [hxR, this]
    have hsq : t ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith only [htpos, htn]
    -- the single product the estimate needs: `t * (t/2 - a) ≥ t`
    have hhalf : (1:ℝ) ≤ t / 2 - a := by linarith only [htM, hM1]
    have hprod : t * 1 ≤ t * (t / 2 - a) := mul_le_mul_of_nonneg_left hhalf htpos.le
    have hring : t ^ 2 / 2 - a * t = t * (t / 2 - a) := by ring
    have hpsi := hmin x
    have hay : -a * ‖x‖ = -a * t - a * ‖y‖ := by rw [htx]; ring
    show ψ y + ‖y - y‖ ^ 2 / 2 ≤ ψ x + ‖x - y‖ ^ 2 / 2
    rw [sub_self, norm_zero]
    linarith only [hpsi, hsq, hprod, hring, hay, htM, hM2]
  -- 'Choosing one such minimizer for each y' is a choice function
  choose u hu using key
  exact ⟨u, fun y x => hu y x⟩
