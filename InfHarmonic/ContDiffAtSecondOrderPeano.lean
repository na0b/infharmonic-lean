module

public import InfHarmonic.Preamble

@[expose] public section
open Set MeasureTheory Metric
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The second-order Taylor expansion with Peano remainder, from a purely LOCAL
hypothesis: a function that is twice continuously differentiable near one point
has, at that point, an expansion whose linear term is the gradient and whose
quadratic term is the second Fréchet derivative read as a bilinear form.  The
hypothesis is `ContDiffAt`, so nothing is assumed about `Ψ` away from a
neighbourhood of `Z`, and the conclusion is two-sided. -/
theorem ContDiffAtSecondOrderPeano (Ψ : E → ℝ) (Z : E) (hΨ : ContDiffAt ℝ 2 Ψ Z) :
    ∀ δ > 0, ∃ ρ > 0, ∀ W : E, ‖W‖ < ρ →
      |Ψ (Z + W) - Ψ Z - inner ℝ (∇ Ψ Z) W
        - (fderiv ℝ (fderiv ℝ Ψ) Z) W W / 2| ≤ δ * ‖W‖ ^ 2 := by
  -- ∫₀¹ t dt = 1/2, from the same FTC the preamble names
  have hhalf : (∫ t in (0:ℝ)..1, t) = 1 / 2 := by
    have hderiv : ∀ t ∈ Set.uIcc (0:ℝ) 1, HasDerivAt (fun τ : ℝ => τ ^ 2 / 2) t t := by
      intro t _
      simpa using ((hasDerivAt_pow 2 t).div_const 2)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (continuous_id.intervalIntegrable 0 1)]
    norm_num
  -- A BALL ON WHICH Ψ IS C², which is all the locality the FTC needs
  obtain ⟨r, hr, hb⟩ : ∃ r > 0, ∀ y : E, dist y Z < r → ContDiffAt ℝ 2 Ψ y := by
    have hev := hΨ.eventually (by norm_num)
    rw [Metric.eventually_nhds_iff] at hev
    exact hev
  have hD : ∀ y : E, dist y Z < r → HasFDerivAt Ψ (fderiv ℝ Ψ y) y := fun y hy =>
    ((hb y hy).differentiableAt (by norm_num)).hasFDerivAt
  have hDc : ∀ y : E, dist y Z < r → ContinuousAt (fun u : E => fderiv ℝ Ψ u) y := fun y hy =>
    ((hb y hy).fderiv_right (m := 0) (by norm_num)).continuousAt
  -- the second derivative at Z
  obtain ⟨A, hAdef⟩ : ∃ A : E →L[ℝ] E →L[ℝ] ℝ, A = fderiv ℝ (fderiv ℝ Ψ) Z := ⟨_, rfl⟩
  have hA : HasFDerivAt (fun u : E => fderiv ℝ Ψ u) A Z := by
    rw [hAdef]
    exact ((hΨ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  intro δ hδ
  -- the little-o of the second derivative
  obtain ⟨ρ₁, hρ₁, hrem⟩ : ∃ ρ > 0, ∀ V : E, ‖V‖ < ρ →
      ‖fderiv ℝ Ψ (Z + V) - fderiv ℝ Ψ Z - A V‖ ≤ δ * ‖V‖ := by
    have hlo := (hA.isLittleO).def hδ
    rw [Metric.eventually_nhds_iff] at hlo
    obtain ⟨ε, hε, hball⟩ := hlo
    refine ⟨ε, hε, fun V hV => ?_⟩
    have hmem : dist (Z + V) Z < ε := by rw [dist_eq_norm]; simpa using hV
    simpa using hball hmem
  refine ⟨min r ρ₁, lt_min hr hρ₁, fun W hW => ?_⟩
  have hWr : ‖W‖ < r := lt_of_lt_of_le hW (min_le_left _ _)
  have hWρ : ‖W‖ < ρ₁ := lt_of_lt_of_le hW (min_le_right _ _)
  have hWn : (0:ℝ) ≤ ‖W‖ := norm_nonneg W
  -- the whole segment from Z to Z + W stays inside the ball
  have hseg : ∀ t ∈ Set.uIcc (0:ℝ) 1, dist (Z + t • W) Z < r := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)] at ht
    rw [dist_eq_norm, show Z + t • W - Z = t • W from by abel, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht.1]
    nlinarith [ht.1, ht.2, hWn, hWr]
  -- the integrand is continuous on [0,1]
  have hcoOn : ContinuousOn (fun t : ℝ => ((fderiv ℝ Ψ (Z + t • W)) W : ℝ))
      (Set.uIcc 0 1) := by
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun u : E => fderiv ℝ Ψ u) (Z + t • W) := hDc _ (hseg t ht)
    have h2 : ContinuousAt (fun s : ℝ => Z + s • W) t := by fun_prop
    have h3 : ContinuousAt (fun s : ℝ => fderiv ℝ Ψ (Z + s • W)) t :=
      ContinuousAt.comp (g := fun u : E => fderiv ℝ Ψ u)
        (f := fun s : ℝ => Z + s • W) h1 h2
    exact (ContinuousLinearMap.apply ℝ ℝ W).continuous.continuousAt.comp h3
  -- FTC along the segment
  have hFTC : Ψ (Z + W) - Ψ Z = ∫ t in (0:ℝ)..1, ((fderiv ℝ Ψ (Z + t • W)) W : ℝ) := by
    have hline : ∀ t : ℝ, HasDerivAt (fun τ : ℝ => Z + τ • W) W t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const W).const_add Z
    have hd : ∀ t ∈ Set.uIcc (0:ℝ) 1,
        HasDerivAt (fun τ : ℝ => Ψ (Z + τ • W)) ((fderiv ℝ Ψ (Z + t • W)) W : ℝ) t := by
      intro t ht
      exact (hD _ (hseg t ht)).comp_hasDerivAt t (hline t)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcoOn.intervalIntegrable]
    simp
  -- the integrand splits into constant, linear and remainder parts
  have hsplit : ∀ t : ℝ, ((fderiv ℝ Ψ (Z + t • W)) W : ℝ)
      = ((fderiv ℝ Ψ Z) W : ℝ) + t * (A W W)
        + ((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ) := by
    intro t
    simp only [sub_apply, map_smul, smul_apply, smul_eq_mul]
    ring
  have igOn : ContinuousOn
      (fun t : ℝ => ((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ))
      (Set.uIcc 0 1) := by
    have heq : (fun t : ℝ => ((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ))
        = fun t : ℝ => ((fderiv ℝ Ψ (Z + t • W)) W : ℝ)
            - (((fderiv ℝ Ψ Z) W : ℝ) + t * (A W W)) := by
      funext t
      rw [hsplit t]
      ring
    rw [heq]
    exact hcoOn.sub (continuousOn_const.add (by fun_prop))
  have ig : IntervalIntegrable
      (fun t : ℝ => ((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ))
      volume 0 1 := igOn.intervalIntegrable
  have iA : IntervalIntegrable (fun _ : ℝ => ((fderiv ℝ Ψ Z) W : ℝ)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  have iB : IntervalIntegrable (fun t : ℝ => t * (A W W)) volume 0 1 := by
    apply Continuous.intervalIntegrable; fun_prop
  -- so the error is exactly the remainder integral
  have herr : Ψ (Z + W) - Ψ Z - ((fderiv ℝ Ψ Z) W : ℝ) - A W W / 2
      = ∫ t in (0:ℝ)..1, ((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ) := by
    rw [hFTC]
    simp only [hsplit]
    rw [intervalIntegral.integral_add (iA.add iB) ig,
      intervalIntegral.integral_add iA iB,
      intervalIntegral.integral_const, intervalIntegral.integral_mul_const, hhalf]
    ring
  rw [← hAdef, inner_gradient_left, herr]
  -- bound the remainder integrand pointwise and integrate the bound
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1,
      |((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ)| ≤ δ * ‖W‖ ^ 2 := by
    intro t ht
    have htn : ‖t • W‖ = t * ‖W‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hlt : ‖t • W‖ < ρ₁ := by
      rw [htn]
      nlinarith [ht.1, ht.2, hWn, hWρ]
    have hop := (fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)).le_opNorm W
    have hrb := hrem (t • W) hlt
    rw [htn] at hrb
    rw [Real.norm_eq_abs] at hop
    nlinarith [mul_le_mul_of_nonneg_right hrb hWn, hop,
      mul_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) hδ.le) (sq_nonneg ‖W‖)]
  calc |∫ t in (0:ℝ)..1, ((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ)|
      ≤ ∫ t in (0:ℝ)..1, |((fderiv ℝ Ψ (Z + t • W) - fderiv ℝ Ψ Z - A (t • W)) W : ℝ)| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ _t in (0:ℝ)..1, δ * ‖W‖ ^ 2 :=
        intervalIntegral.integral_mono_on (by norm_num) ig.abs
          (by apply Continuous.intervalIntegrable; fun_prop) hpt
    _ = δ * ‖W‖ ^ 2 := by rw [intervalIntegral.integral_const]; simp
