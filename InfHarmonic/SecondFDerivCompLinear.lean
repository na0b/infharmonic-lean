import InfHarmonic.Preamble
open Filter Topology

/-- The second derivative of a composition with a continuous linear map on the right:
`D²(f ∘ L)(W)[ξ, η] = D²f(L W)[L ξ, L η]`.  Mathlib supplies this only for a globally
`C^n` function; the hypothesis here is `ContDiffAt` at the single point `L W`, which is
what a test function in viscosity theory actually provides. -/
theorem SecondFDerivCompLinear {P Q : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (L : P →L[ℝ] Q) (f : Q → ℝ) (W : P) (hf : ContDiffAt ℝ 2 f (L W)) (ξ η : P) :
    fderiv ℝ (fderiv ℝ (fun U => f (L U))) W ξ η
      = fderiv ℝ (fderiv ℝ f) (L W) (L ξ) (L η) := by
  -- precomposition by `L` is itself a continuous linear map
  obtain ⟨CL, hCL⟩ : ∃ CL : (Q →L[ℝ] ℝ) →L[ℝ] (P →L[ℝ] ℝ), ∀ g, CL g = g.comp L :=
    ⟨(ContinuousLinearMap.compL ℝ P Q ℝ).flip L, fun g => rfl⟩
  -- near `L W` the function `f` is differentiable
  have hev : ∀ᶠ y in 𝓝 (L W), DifferentiableAt ℝ f y := by
    filter_upwards [hf.eventually (by norm_num)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hevW : ∀ᶠ U in 𝓝 W, DifferentiableAt ℝ f (L U) :=
    (L.continuous.continuousAt (x := W)).eventually hev
  -- so the first derivative of the composition is the composition of the derivatives
  have hfd : (fun U => fderiv ℝ (fun U' => f (L U')) U)
      =ᶠ[𝓝 W] fun U => CL (fderiv ℝ f (L U)) := by
    filter_upwards [hevW] with U hU
    rw [hCL]
    exact (hU.hasFDerivAt.comp U L.hasFDerivAt).fderiv
  -- differentiate once more
  have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) (L W)) (L W) :=
    ((hf.fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num)).hasFDerivAt
  have hB : HasFDerivAt (fun U => fderiv ℝ f (L U))
      ((fderiv ℝ (fderiv ℝ f) (L W)).comp L) W := hA.comp W L.hasFDerivAt
  have hC : HasFDerivAt (fun U => CL (fderiv ℝ f (L U)))
      (CL.comp ((fderiv ℝ (fderiv ℝ f) (L W)).comp L)) W := CL.hasFDerivAt.comp W hB
  rw [hfd.fderiv_eq, hC.fderiv]
  simp [hCL]
