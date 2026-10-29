module

public import InfHarmonic.ProxSubdifferentialSingleton

@[expose] public section
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 4(b) of Alexandrov's theorem: above a point where the proximal map is
differentiable with invertible derivative, proximal preimages are uniformly
localized -- any `y'` whose proximal image is near `u y` is itself near `y`. -/
theorem ProxPreimageLocalization (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E)
    (hu : IsMoreauProx ψ u) (y : E) (P : E →L[ℝ] E) (hP : HasFDerivAt u P y)
    (hdet : LinearMap.det (P : E →ₗ[ℝ] E) ≠ 0) :
    ∀ σ > 0, ∃ ρ > 0, ∀ y' : E, ‖u y' - u y‖ < ρ → ‖y' - y‖ < σ := by
  -- Body-only acknowledgement (trap 2): the instance bundle is part of this node's
  -- protected signature; the route below does not consume it directly.
  have _ : FiniteDimensional ℝ E := inferInstance
  intro σ hσ
  -- `u` is 1-Lipschitz, hence continuous
  have hulip : ∀ a b : E, ‖u a - u b‖ ≤ ‖a - b‖ := by
    intro a b
    have h := MoreauProxMonotone ψ hψ a b (u a) (u b) (hu a) (hu b)
    nlinarith [sq_nonneg ‖(a - u a) - (b - u b)‖, norm_nonneg (u a - u b),
      norm_nonneg (a - b)]
  have hucont : Continuous u := by
    refine LipschitzWith.continuous (K := 1) ?_
    intro a b
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    simp only [ENNReal.coe_one, one_mul]
    exact ENNReal.ofReal_le_ofReal (hulip a b)
  -- `ψ` is Lipschitz on a ball around `u y`
  obtain ⟨K, tset, ht, hKlip⟩ := (hψ.locallyLipschitzOn isOpen_univ) (mem_univ (u y))
  rw [nhdsWithin_univ] at ht
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = r / 3 := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; linarith
  have hsub : Metric.closedBall (u y) (2 * a) ⊆ tset := by
    intro z hz
    refine hball ?_
    have := Metric.mem_closedBall.mp hz
    rw [Metric.mem_ball]
    rw [ha] at this; linarith
  -- the subgradient at any nearby proximal image is bounded by the Lipschitz constant
  have hsbound : ∀ y' : E, ‖u y' - u y‖ ≤ a → ‖y' - u y'‖ ≤ (K : ℝ) := by
    intro y' hy'
    have hsg : ∀ x : E, ψ (u y') + inner ℝ (y' - u y') (x - u y') ≤ ψ x :=
      (MoreauProxSubgradient ψ hψ y' (u y')).mp (hu y')
    have hw' : u y' ∈ Metric.closedBall (u y) (2 * a) := by
      rw [Metric.mem_closedBall, dist_eq_norm]; linarith
    by_contra hcon
    rw [not_le] at hcon
    have hs0 : (0:ℝ) < ‖y' - u y'‖ := lt_of_le_of_lt (by positivity) hcon
    obtain ⟨e, he⟩ : ∃ e : E, e = ‖y' - u y'‖⁻¹ • (y' - u y') := ⟨_, rfl⟩
    have hen : ‖e‖ = 1 := by
      rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hs0)]
    have hpt : u y' + a • e ∈ Metric.closedBall (u y) (2 * a) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h1 : ‖u y' + a • e - u y‖ ≤ ‖u y' - u y‖ + ‖a • e‖ := by
        calc ‖u y' + a • e - u y‖ = ‖(u y' - u y) + a • e‖ := by rw [show
              u y' + a • e - u y = (u y' - u y) + a • e by abel]
          _ ≤ ‖u y' - u y‖ + ‖a • e‖ := norm_add_le _ _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha0, hen, mul_one] at h1
      linarith
    -- the Lipschitz bound and the subgradient inequality fight each other
    have hlip := hKlip.dist_le_mul (u y') (hsub hw') (u y' + a • e) (hsub hpt)
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hsne : ‖y' - u y'‖ ≠ 0 := ne_of_gt hs0
    -- the directional derivative along the unit vector `e` is exactly the norm
    have hie : (inner ℝ (y' - u y') e : ℝ) = ‖y' - u y'‖ := by
      rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hineq := hsg (u y' + a • e)
    rw [show u y' + a • e - u y' = a • e by abel, real_inner_smul_right, hie] at hineq
    have hnn : ‖u y' - (u y' + a • e)‖ = a := by
      rw [show u y' - (u y' + a • e) = -(a • e) by abel, norm_neg, norm_smul,
        Real.norm_eq_abs, abs_of_pos ha0, hen, mul_one]
    rw [hnn] at hlip
    have habs : ψ (u y' + a • e) - ψ (u y') ≤ (K : ℝ) * a := by
      have hA := abs_le.mp (by rw [← Real.norm_eq_abs]; exact hlip :
        |ψ (u y') - ψ (u y' + a • e)| ≤ (K : ℝ) * a)
      linarith [hA.1]
    have hkey : a * ‖y' - u y'‖ ≤ (K : ℝ) * a := by linarith
    nlinarith [hkey, mul_pos ha0 (sub_pos.mpr hcon)]
  -- every relevant `y'` lies in one fixed ball
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = ‖u y‖ + a + (K : ℝ) := ⟨_, rfl⟩
  have hRbound : ∀ y' : E, ‖u y' - u y‖ ≤ a → ‖y'‖ ≤ R := by
    intro y' hy'
    have h1 : ‖u y'‖ ≤ ‖u y‖ + a := by
      have := norm_sub_norm_le (u y') (u y)
      calc ‖u y'‖ = ‖u y'‖ := rfl
        _ ≤ ‖u y‖ + ‖u y' - u y‖ := by
            have h2 := norm_add_le (u y) (u y' - u y)
            rw [show u y + (u y' - u y) = u y' by abel] at h2; exact h2
        _ ≤ ‖u y‖ + a := by linarith
    have h3 : ‖y'‖ ≤ ‖u y'‖ + ‖y' - u y'‖ := by
      have h4 := norm_add_le (u y') (y' - u y')
      rw [show u y' + (y' - u y') = y' by abel] at h4; exact h4
    have h5 := hsbound y' hy'
    rw [hR]; linarith
  -- the compact slice of far-away points inside that ball
  obtain ⟨C, hC⟩ : ∃ C : Set E, C = Metric.closedBall (0 : E) R ∩ {z : E | σ ≤ ‖z - y‖} := ⟨_, rfl⟩
  have hCc : IsCompact C := by
    rw [hC]
    exact (isCompact_closedBall _ _).inter_right (isClosed_le continuous_const (by fun_prop))
  rcases Set.eq_empty_or_nonempty C with hCe | hCne
  · -- no far-away point is in the ball at all
    refine ⟨a, ha0, fun y' hy' => ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    have : y' ∈ C := by
      rw [hC]
      exact ⟨mem_closedBall_zero_iff.mpr (hRbound y' hy'.le), hcon⟩
    rw [hCe] at this
    exact this
  · -- the minimum of ‖u · - u y‖ over the slice is positive
    obtain ⟨ŷ, hŷC, hŷmin⟩ := hCc.exists_isMinOn hCne
      (f := fun z : E => ‖u z - u y‖) (by fun_prop)
    have hŷfar : σ ≤ ‖ŷ - y‖ := by rw [hC] at hŷC; exact hŷC.2
    have hmpos : 0 < ‖u ŷ - u y‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (u ŷ - u y)) with heq | hlt
      · exfalso
        have huŷ : u ŷ = u y := sub_eq_zero.mp (norm_eq_zero.mp heq.symm)
        have hsg : ∀ x : E, ψ (u y) + inner ℝ (ŷ - u y) (x - u y) ≤ ψ x := by
          have h := (MoreauProxSubgradient ψ hψ ŷ (u ŷ)).mp (hu ŷ)
          rw [huŷ] at h; exact h
        have := ProxSubdifferentialSingleton ψ hψ u hu y P hP hdet (ŷ - u y) hsg
        have hŷy : ŷ = y := by
          have h6 := congrArg (fun z : E => z + u y) this
          simpa using h6
        rw [hŷy, sub_self, norm_zero] at hŷfar
        linarith
      · exact hlt
    refine ⟨min a ‖u ŷ - u y‖, lt_min ha0 hmpos, fun y' hy' => ?_⟩
    by_contra hcon
    rw [not_lt] at hcon
    have hin : y' ∈ C := by
      rw [hC]
      exact ⟨mem_closedBall_zero_iff.mpr
        (hRbound y' (le_trans hy'.le (min_le_left _ _))), hcon⟩
    have := isMinOn_iff.mp hŷmin y' hin
    have h2 : ‖u ŷ - u y‖ ≤ ‖u y' - u y‖ := this
    have h3 := lt_of_lt_of_le hy' (min_le_right a ‖u ŷ - u y‖)
    linarith
