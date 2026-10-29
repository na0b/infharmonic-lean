import InfHarmonic.MoreauCurveExpansion
import InfHarmonic.ProxPreimageLocalization
import InfHarmonic.ProxQuadraticFormComparison
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 5 of Alexandrov's theorem: at a point `u y` lying above a `y` where the
proximal map is differentiable with invertible derivative `P`, the convex function
`ψ` has a second-order expansion with slope `y - u y` and quadratic form
`⟪(I - P) (P⁻¹ k), k⟫`. -/
theorem ProxEnvelopeExpansionAt (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E)
    (hu : IsMoreauProx ψ u) (hdense : Dense (Set.range u))
    (y : E) (P Pinv : E →L[ℝ] E) (hP : HasFDerivAt u P y)
    (hinv : ∀ z : E, Pinv (P z) = z) (hinv' : ∀ z : E, P (Pinv z) = z)
    (hdet : LinearMap.det (P : E →ₗ[ℝ] E) ≠ 0) :
    ∀ δ > 0, ∃ ρ > 0, ∀ k : E, ‖k‖ < ρ →
      |ψ (u y + k) - ψ (u y) - inner ℝ (y - u y) k
        - inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) k / 2| ≤ δ * ‖k‖ ^ 2 := by
  -- THE SHAPE OF THE ARGUMENT, recorded here so it is citable by file and line.
  -- Write x = u y, p = y - x, Q = id - P, A₀ = Q ∘ P⁻¹ and
  --   G k = ψ (x + k) - ψ x - ⟪p, k⟫ - ⟪A₀ k, k⟫ / 2.
  -- `MoreauCurveExpansion` controls the SAME quantity written in the `h` variable along the
  -- curve h ↦ u (y + h); `ProxPreimageLocalization` says that a `k` small enough forces its
  -- preimage `h` small, so the curve estimate is available; `ProxQuadraticFormComparison`
  -- converts the quadratic form ⟪Q h, P h⟫ into ⟪A₀ k, k⟫ at a cost O(δ₁)‖k‖².  That gives
  -- |G k| ≤ δ‖k‖² for every `k` with x + k IN THE RANGE of u.  The range is dense, the set
  -- {k | |G k| ≤ δ‖k‖²} is CLOSED (both sides continuous), so the ball is contained in the
  -- closure of the range points and hence in that set -- no sequences needed.
  -- Body-only acknowledgements of the protected signature (trap 3): the route below runs off
  -- the one-sided inverse `hinv` alone, and consumes finite-dimensionality only through the
  -- imported nodes, so neither `hinv'` nor the instance is named again.
  have _ := hinv'
  have _ : FiniteDimensional ℝ E := inferInstance
  -- ψ is convex and real-valued on the open set `univ`, hence continuous (preamble route).
  have hψc : Continuous ψ := continuousOn_univ.1 (hψ.continuousOn isOpen_univ)
  intro δ hδ
  -- (0) THE DEGENERATE BRANCH.  `c = 1/‖P⁻¹‖` needs ‖P⁻¹‖ ≠ 0, and ‖P⁻¹‖ = 0 forces
  -- P⁻¹ = 0, hence z = P⁻¹ (P z) = 0 for every z, i.e. E = {0}; then every `k` is `0` and
  -- both sides of the conclusion vanish.
  rcases eq_or_lt_of_le (norm_nonneg Pinv) with hPz | hPpos
  · refine ⟨1, one_pos, fun k _ => ?_⟩
    have hPinv0 : Pinv = 0 := by rw [← norm_eq_zero]; exact hPz.symm
    have hz : ∀ z : E, z = 0 := by
      intro z
      rw [← hinv z, hPinv0]
      exact zero_apply (P z)
    rw [hz k]
    simp
  -- (1) A LOWER BOUND FOR P.  ‖z‖ = ‖P⁻¹ (P z)‖ ≤ ‖P⁻¹‖ ‖P z‖ rearranges to c‖z‖ ≤ ‖P z‖.
  obtain ⟨c, hc⟩ : ∃ t : ℝ, t = 1 / ‖Pinv‖ := ⟨_, rfl⟩
  have hcpos : 0 < c := by rw [hc]; exact div_pos one_pos hPpos
  have hcsq : (0:ℝ) < c ^ 2 := pow_pos hcpos 2
  have hlow : ∀ z : E, c * ‖z‖ ≤ ‖P z‖ := by
    intro z
    have h1 : ‖z‖ ≤ ‖P z‖ * ‖Pinv‖ := by
      rw [mul_comm]
      calc ‖z‖ = ‖Pinv (P z)‖ := by rw [hinv z]
        _ ≤ ‖Pinv‖ * ‖P z‖ := ContinuousLinearMap.le_opNorm _ _
    rw [hc, div_mul_eq_mul_div, one_mul, div_le_iff₀ hPpos]
    exact h1
  -- (2) THE PARAMETER BUDGET.  C₁ is a FIXED FINITE number built from the statement's own
  -- operator norms, so it is established BEFORE the δ's are chosen and the budget below is
  -- realizable: δ₁ ≤ min (1, c/2) with C₁δ₁ ≤ δ, and δ₂ = c²δ/8 so that 4δ₂/c² = δ/2.
  obtain ⟨C₁, hC₁⟩ : ∃ t : ℝ, t = 4 * ‖ContinuousLinearMap.id ℝ E - P‖ * ‖Pinv‖ * ‖P‖ / c ^ 2
      + 2 * ‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ / c := ⟨_, rfl⟩
  have hC₁nn : 0 ≤ C₁ := by
    rw [hC₁]
    have ha : (0:ℝ) ≤ 4 * ‖ContinuousLinearMap.id ℝ E - P‖ * ‖Pinv‖ * ‖P‖ / c ^ 2 :=
      div_nonneg (by positivity) hcsq.le
    have hb : (0:ℝ) ≤ 2 * ‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ / c :=
      div_nonneg (by positivity) hcpos.le
    linarith
  have hC1p : (0:ℝ) < C₁ + 1 := by linarith
  obtain ⟨δ₁, hδ₁def⟩ : ∃ t : ℝ, t = min (min 1 (c / 2)) (δ / (C₁ + 1)) := ⟨_, rfl⟩
  have hδ₁pos : 0 < δ₁ := by
    rw [hδ₁def]
    exact lt_min (lt_min one_pos (by linarith)) (div_pos hδ hC1p)
  have hδ₁c : δ₁ ≤ c / 2 :=
    le_trans (by rw [hδ₁def]; exact min_le_left _ _) (min_le_right _ _)
  have hδ₁C : C₁ * δ₁ ≤ δ := by
    have h1 : δ₁ ≤ δ / (C₁ + 1) := by rw [hδ₁def]; exact min_le_right _ _
    rw [le_div_iff₀ hC1p] at h1
    nlinarith [hδ₁pos.le]
  obtain ⟨δ₂, hδ₂def⟩ : ∃ t : ℝ, t = c ^ 2 * δ / 8 := ⟨_, rfl⟩
  have hδ₂pos : 0 < δ₂ := by
    rw [hδ₂def]
    have := mul_pos hcsq hδ
    linarith
  -- (3) THE THREE RADII.
  obtain ⟨ρ₁, hρ₁, hcurve⟩ := MoreauCurveExpansion ψ hψ u hu y P hP δ₂ hδ₂pos
  obtain ⟨ρ₂, hρ₂, hrho⟩ : ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
      ‖u (y + h) - u y - P h‖ ≤ δ₁ * ‖h‖ := by
    have hlo := (hP.isLittleO).def hδ₁pos
    rw [Metric.eventually_nhds_iff] at hlo
    obtain ⟨ε, hε, hball⟩ := hlo
    refine ⟨ε, hε, fun h hh => ?_⟩
    have hmem : dist (y + h) y < ε := by rw [dist_eq_norm]; simpa using hh
    simpa using hball hmem
  obtain ⟨ρ₃, hρ₃, hloc⟩ :=
    ProxPreimageLocalization ψ hψ u hu y P hP hdet (min ρ₁ ρ₂) (lt_min hρ₁ hρ₂)
  -- (4) THE ESTIMATE AT POINTS OF THE RANGE.
  have hrange : ∀ k : E, ‖k‖ < ρ₃ → u y + k ∈ Set.range u →
      |ψ (u y + k) - ψ (u y) - inner ℝ (y - u y) k
        - inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) k / 2| ≤ δ * ‖k‖ ^ 2 := by
    intro k hk hmemr
    obtain ⟨y', hy'⟩ := hmemr
    obtain ⟨h, hh⟩ : ∃ z : E, z = y' - y := ⟨_, rfl⟩
    have hyh : y + h = y' := by rw [hh]; abel
    have he1 : u y + k - u y = k := by abel
    have hxh2 : u (y + h) = u y + k := by rw [hyh, hy']
    have hxh : u (y + h) - u y = k := by rw [hxh2, he1]
    have hk' : ‖u y' - u y‖ < ρ₃ := by rw [hy', he1]; exact hk
    have hhlt : ‖h‖ < min ρ₁ ρ₂ := by rw [hh]; exact hloc y' hk'
    have hh1 : ‖h‖ < ρ₁ := lt_of_lt_of_le hhlt (min_le_left _ _)
    have hh2 : ‖h‖ < ρ₂ := lt_of_lt_of_le hhlt (min_le_right _ _)
    -- |k - P h| ≤ δ₁ |h| : the first-order remainder of `u`, read in the `k` variable
    have hdk : ‖k - P h‖ ≤ δ₁ * ‖h‖ := by
      have hr := hrho h hh2
      rw [hxh] at hr
      exact hr
    obtain ⟨hcomp1, hcomp2⟩ :=
      ProxQuadraticFormComparison P Pinv hinv c hcpos hlow δ₁ hδ₁pos hδ₁c h k hdk
    rw [← hC₁] at hcomp2
    -- the curve estimate, with `u (y + h) - u y` replaced by `k`
    have hcv := hcurve h hh1
    rw [hxh2, he1] at hcv
    -- δ₂|h|² ≤ (δ/2)|k|², because |h| ≤ (2/c)|k| and δ₂ = c²δ/8
    have hb1 : δ₂ * ‖h‖ ^ 2 ≤ δ / 2 * ‖k‖ ^ 2 := by
      have hcn : c * ‖h‖ ≤ 2 * ‖k‖ := by
        have hm := mul_le_mul_of_nonneg_left hcomp1 hcpos.le
        rw [show c * (2 / c * ‖k‖) = 2 * ‖k‖ by field_simp] at hm
        exact hm
      have hsq : c ^ 2 * ‖h‖ ^ 2 ≤ 4 * ‖k‖ ^ 2 := by
        nlinarith [hcn, mul_nonneg hcpos.le (norm_nonneg h), norm_nonneg k]
      rw [hδ₂def]
      linarith [mul_le_mul_of_nonneg_left hsq (show (0:ℝ) ≤ δ / 8 by linarith)]
    have hb2 : C₁ * δ₁ * ‖k‖ ^ 2 ≤ δ * ‖k‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hδ₁C (by positivity)
    have hc1 := abs_le.mp hcv
    have hc2 := abs_le.mp hcomp2
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith only [hc1.1, hc1.2, hc2.1, hc2.2, hb1, hb2]
    · linarith only [hc1.1, hc1.2, hc2.1, hc2.2, hb1, hb2]
  -- (5) REMOVING THE RESTRICTION, BY DENSITY.
  refine ⟨ρ₃, hρ₃, ?_⟩
  obtain ⟨T, hT⟩ : ∃ T : Set E, T = {k : E | ‖k‖ < ρ₃ ∧ u y + k ∈ Set.range u} := ⟨_, rfl⟩
  obtain ⟨S, hS⟩ : ∃ S : Set E, S = {k : E |
      |ψ (u y + k) - ψ (u y) - inner ℝ (y - u y) k
        - inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) k / 2| ≤ δ * ‖k‖ ^ 2} := ⟨_, rfl⟩
  -- both sides are continuous: ψ is continuous, A₀ is continuous linear, the inner product
  -- and the absolute value are continuous, so S is closed.
  have hScl : IsClosed S := by
    have hcA : Continuous fun k : E =>
        (inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) k : ℝ) := by
      have h1 : Continuous fun k : E => (ContinuousLinearMap.id ℝ E - P) (Pinv k) :=
        (ContinuousLinearMap.id ℝ E - P).continuous.comp' Pinv.continuous
      exact h1.inner continuous_id
    have hcp : Continuous fun k : E => (inner ℝ (y - u y) k : ℝ) :=
      (continuous_const (y := y - u y)).inner continuous_id
    have hcψ : Continuous fun k : E => ψ (u y + k) :=
      hψc.comp' (continuous_const.add continuous_id)
    rw [hS]
    refine isClosed_le (Continuous.abs ?_) (by fun_prop)
    exact ((hcψ.sub continuous_const).sub hcp).sub (hcA.div_const 2)
  have hTS : T ⊆ S := by
    intro k' hk'
    rw [hT] at hk'
    rw [hS]
    exact hrange k' hk'.1 hk'.2
  intro k hk
  -- T is dense in the ball: around any k₀ in the ball, shrink ε so the ε-ball stays inside,
  -- and use the density of the range of u on the open ball about u y + k₀.
  have hmem : k ∈ closure T := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨e, he0, hee, heρ⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ε ∧ ‖k‖ + t < ρ₃ := by
      refine ⟨min ε ((ρ₃ - ‖k‖) / 2), lt_min hε (by linarith), min_le_left _ _, ?_⟩
      have := min_le_right ε ((ρ₃ - ‖k‖) / 2)
      linarith
    obtain ⟨z, hzr, hzmem⟩ := hdense.exists_mem_open
      (Metric.isOpen_ball (x := u y + k) (ε := e)) ⟨u y + k, Metric.mem_ball_self he0⟩
    obtain ⟨y', hy'⟩ := hzr
    have hdz : ‖z - (u y + k)‖ < e := by
      have hd := Metric.mem_ball.mp hzmem
      rwa [dist_eq_norm] at hd
    have hid : z - u y - k = z - (u y + k) := by abel
    refine ⟨z - u y, ?_, ?_⟩
    · rw [hT]
      refine ⟨?_, Set.mem_range.mpr ⟨y', by rw [hy']; abel⟩⟩
      have h1 : ‖z - u y‖ ≤ ‖k‖ + ‖z - u y - k‖ := by
        calc ‖z - u y‖ = ‖k + (z - u y - k)‖ := by
              rw [show k + (z - u y - k) = z - u y by abel]
          _ ≤ ‖k‖ + ‖z - u y - k‖ := norm_add_le _ _
      rw [hid] at h1
      linarith
    · rw [dist_eq_norm]
      have h2 : k - (z - u y) = -(z - (u y + k)) := by abel
      rw [h2, norm_neg]
      linarith
  have hfin : k ∈ S := closure_minimal hTS hScl hmem
  rw [hS] at hfin
  exact hfin
