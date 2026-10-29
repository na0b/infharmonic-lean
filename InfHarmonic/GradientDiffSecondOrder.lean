module

public import InfHarmonic.Preamble

@[expose] public section
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A function whose gradient exists everywhere, is continuous, and is itself
differentiable at one point has a second-order Taylor expansion at that point,
with quadratic form the derivative of the gradient. -/
theorem GradientDiffSecondOrder (F : E → ℝ) (w : E → E)
    (hgrad : ∀ z : E, HasGradientAt F (w z) z) (hwc : Continuous w)
    (y : E) (Q : E →L[ℝ] E) (hQ : HasFDerivAt w Q y) :
    ∀ δ > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
      |F (y + h) - F y - inner ℝ (w y) h - inner ℝ (Q h) h / 2| ≤ δ * ‖h‖ ^ 2 := by
  -- ∫₀¹ t dt = 1/2, proved from the same FTC the preamble names
  have hhalf : (∫ t in (0:ℝ)..1, t) = 1 / 2 := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
      intro t _
      simpa using ((hasDerivAt_pow 2 t).div_const 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (continuous_id.intervalIntegrable 0 1)]
    norm_num
  -- integrating the gradient along each segment
  have hFTC : ∀ h : E,
      F (y + h) - F y = ∫ t in (0:ℝ)..1, (inner ℝ (w (y + t • h)) h : ℝ) := by
    intro h
    have hline : ∀ t : ℝ, HasDerivAt (fun τ : ℝ => y + τ • h) h t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const h).const_add y
    have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun τ : ℝ => F (y + τ • h)) (inner ℝ (w (y + t • h)) h : ℝ) t := by
      intro t _
      have hc := ((hgrad (y + t • h)).hasFDerivAt).comp_hasDerivAt t (hline t)
      exact hc
    have hint : IntervalIntegrable
        (fun t : ℝ => (inner ℝ (w (y + t • h)) h : ℝ)) volume 0 1 := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  intro δ hδ
  -- the derivative of `w` at `y` gives a ball on which the remainder is small
  obtain ⟨ρ, hρ, hr⟩ : ∃ ρ > 0, ∀ k : E, ‖k‖ < ρ →
      ‖w (y + k) - w y - Q k‖ ≤ δ * ‖k‖ := by
    have hlo := (hQ.isLittleO).def hδ
    rw [Metric.eventually_nhds_iff] at hlo
    obtain ⟨ε, hε, hball⟩ := hlo
    refine ⟨ε, hε, fun k hk => ?_⟩
    have hmem : dist (y + k) y < ε := by rw [dist_eq_norm]; simpa using hk
    simpa using hball hmem
  refine ⟨ρ, hρ, fun h hh => ?_⟩
  have hnh : (0:ℝ) ≤ ‖h‖ := norm_nonneg h
  -- the integrand splits into constant, linear and remainder parts
  have hsplit : ∀ t : ℝ, (inner ℝ (w (y + t • h)) h : ℝ)
      = (inner ℝ (w y) h : ℝ) + t * (inner ℝ (Q h) h : ℝ)
        + (inner ℝ (w (y + t • h) - w y - Q (t • h)) h : ℝ) := by
    intro t
    rw [inner_sub_left, inner_sub_left, map_smul, real_inner_smul_left]
    ring
  -- integrability of the three pieces
  have ig : IntervalIntegrable
      (fun t : ℝ => (inner ℝ (w (y + t • h) - w y - Q (t • h)) h : ℝ)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have iA : IntervalIntegrable (fun _ : ℝ => (inner ℝ (w y) h : ℝ)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have iB : IntervalIntegrable
      (fun t : ℝ => t * (inner ℝ (Q h) h : ℝ)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  -- so the error is exactly the remainder integral
  have herr : F (y + h) - F y - inner ℝ (w y) h - inner ℝ (Q h) h / 2
      = ∫ t in (0:ℝ)..1, (inner ℝ (w (y + t • h) - w y - Q (t • h)) h : ℝ) := by
    rw [hFTC h]
    simp only [hsplit]
    rw [intervalIntegral.integral_add (iA.add iB) ig,
      intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const, hhalf]
    ring
  rw [herr]
  -- bound the remainder integrand pointwise and integrate the bound
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |(inner ℝ (w (y + t • h) - w y - Q (t • h)) h : ℝ)| ≤ δ * ‖h‖ ^ 2 := by
    intro t ht
    have htn : ‖t • h‖ = t * ‖h‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hlt : ‖t • h‖ < ρ := by rw [htn]; nlinarith [ht.1, ht.2]
    have hcs := abs_real_inner_le_norm (w (y + t • h) - w y - Q (t • h)) h
    have hrb := hr (t • h) hlt
    rw [htn] at hrb
    nlinarith [mul_le_mul_of_nonneg_right hrb hnh, hcs,
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hδ.le) (sq_nonneg ‖h‖)]
  calc |∫ t in (0:ℝ)..1, (inner ℝ (w (y + t • h) - w y - Q (t • h)) h : ℝ)|
      ≤ ∫ t in (0:ℝ)..1, |(inner ℝ (w (y + t • h) - w y - Q (t • h)) h : ℝ)| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ _t in (0:ℝ)..1, δ * ‖h‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num) ig.abs
          (by apply Continuous.intervalIntegrable; fun_prop) hpt
    _ = δ * ‖h‖ ^ 2 := by rw [intervalIntegral.integral_const]; simp
