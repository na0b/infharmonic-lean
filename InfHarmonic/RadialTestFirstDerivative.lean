import InfHarmonic.Preamble

/-- The three-block radial test is `C²` off the diagonal, and its first derivative there.
The test is an affine functional plus a localizing factor `B` evaluated at one linear
image, times a radial profile `f` of the norm of a second linear image, plus the squared
norm of a third linear image divided by the square of that same radius.  Away from the
locus where the radius vanishes the whole expression is `C²`, and its derivative is the
sum of the four displayed contributions; the coefficient of the radial direction
`e = ‖Ld W‖⁻¹ • Ld W` is exactly the constant the three-point estimate calls `a`.
Stated over abstract normed spaces, which is what makes it usable at a `PiLp` product
without fighting the instances there (cf. `SecondFDerivCompLinear`). -/
theorem RadialTestFirstDerivative {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (A : V →L[ℝ] ℝ) (Lc Ld Lh : V →L[ℝ] E) (B : E → ℝ) (f : ℝ → ℝ)
    (W : V) (fr' : ℝ) (hW : Ld W ≠ 0)
    (hB : ContDiffAt ℝ 2 B (Lc W)) (hf : ContDiffAt ℝ 2 f ‖Ld W‖)
    (hf' : HasDerivAt f fr' ‖Ld W‖) :
    ContDiffAt ℝ 2
        (fun U : V => A U + B (Lc U) * f ‖Ld U‖ + ‖Lh U‖ ^ 2 / ‖Ld U‖ ^ 2) W
      ∧ ∀ ζ : V,
        fderiv ℝ (fun U : V => A U + B (Lc U) * f ‖Ld U‖ + ‖Lh U‖ ^ 2 / ‖Ld U‖ ^ 2) W ζ
          = A ζ + f ‖Ld W‖ * fderiv ℝ B (Lc W) (Lc ζ)
            + (B (Lc W) * fr' - 2 * ‖Lh W‖ ^ 2 / ‖Ld W‖ ^ 3)
                * (inner ℝ (‖Ld W‖⁻¹ • Ld W) (Ld ζ))
            + 2 * (inner ℝ (Lh W) (Lh ζ) : ℝ) / ‖Ld W‖ ^ 2 := by
  have hn0 : ‖Ld W‖ ≠ 0 := norm_ne_zero_iff.mpr hW
  have hnpos : 0 < ‖Ld W‖ := norm_pos_iff.mpr hW
  have hsq0 : ‖Ld W‖ ^ 2 ≠ 0 := pow_ne_zero 2 hn0
  -- each block is `C²` at `W`; the radius is `C²` because it does not vanish there
  have hcLd : ContDiffAt ℝ 2 (fun U : V => ‖Ld U‖) W :=
    (Ld.contDiff (n := 2)).contDiffAt.norm ℝ hW
  have hcB : ContDiffAt ℝ 2 (fun U : V => B (Lc U)) W :=
    hB.comp W (Lc.contDiff (n := 2)).contDiffAt
  have hcf : ContDiffAt ℝ 2 (fun U : V => f ‖Ld U‖) W := hf.comp W hcLd
  have hcnum : ContDiffAt ℝ 2 (fun U : V => ‖Lh U‖ ^ 2) W :=
    (Lh.contDiff (n := 2)).contDiffAt.norm_sq ℝ
  have hcden : ContDiffAt ℝ 2 (fun U : V => ‖Ld U‖ ^ 2) W :=
    (Ld.contDiff (n := 2)).contDiffAt.norm_sq ℝ
  have hC2 : ContDiffAt ℝ 2
      (fun U : V => A U + B (Lc U) * f ‖Ld U‖ + ‖Lh U‖ ^ 2 / ‖Ld U‖ ^ 2) W :=
    ((A.contDiff (n := 2)).contDiffAt.add (hcB.mul hcf)).add (hcnum.div hcden hsq0)
  refine ⟨hC2, ?_⟩
  -- the squared norms, whose derivative is `2⟪·, ·⟫` transported through the linear map
  have hns : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (2 • innerSL ℝ (Ld W)) (Ld W) := by
    have h := ((contDiff_norm_sq ℝ (E := E)).differentiable (n := 2) (by norm_num)
      (Ld W)).hasFDerivAt
    rw [← fderiv_norm_sq_apply (Ld W)]
    exact h
  have hden : HasFDerivAt (fun U : V => ‖Ld U‖ ^ 2)
      ((2 • innerSL ℝ (Ld W)).comp Ld) W := hns.comp W Ld.hasFDerivAt
  have hnsh : HasFDerivAt (fun x : E => ‖x‖ ^ 2) (2 • innerSL ℝ (Lh W)) (Lh W) := by
    have h := ((contDiff_norm_sq ℝ (E := E)).differentiable (n := 2) (by norm_num)
      (Lh W)).hasFDerivAt
    rw [← fderiv_norm_sq_apply (Lh W)]
    exact h
  have hnum : HasFDerivAt (fun U : V => ‖Lh U‖ ^ 2)
      ((2 • innerSL ℝ (Lh W)).comp Lh) W := hnsh.comp W Lh.hasFDerivAt
  -- the radius itself, as the square root of the squared norm
  have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (‖Ld W‖ ^ 2))) (‖Ld W‖ ^ 2) :=
    Real.hasDerivAt_sqrt hsq0
  have hsq : Real.sqrt (‖Ld W‖ ^ 2) = ‖Ld W‖ := Real.sqrt_sq (norm_nonneg _)
  have h2 := hs.comp_hasFDerivAt W hden
  rw [hsq] at h2
  have hdn : HasFDerivAt (fun U : V => ‖Ld U‖)
      ((1 / (2 * ‖Ld W‖)) • (2 • innerSL ℝ (Ld W)).comp Ld) W :=
    h2.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun U => (Real.sqrt_sq (norm_nonneg (Ld U))).symm)
  have hDnv : ∀ ζ : V, ((1 / (2 * ‖Ld W‖)) • (2 • innerSL ℝ (Ld W)).comp Ld) ζ
      = (inner ℝ (‖Ld W‖⁻¹ • Ld W) (Ld ζ) : ℝ) := by
    intro ζ
    have hv : ((1 / (2 * ‖Ld W‖)) • (2 • innerSL ℝ (Ld W)).comp Ld) ζ
        = (1 / (2 * ‖Ld W‖)) * (2 * (inner ℝ (Ld W) (Ld ζ) : ℝ)) := by
      simp [ContinuousLinearMap.comp_apply]
    rw [hv, real_inner_smul_left]
    field_simp
  -- the two factors of the localizing product, then the product
  have hBd : HasFDerivAt (fun U : V => B (Lc U)) ((fderiv ℝ B (Lc W)).comp Lc) W :=
    (hB.differentiableAt (by norm_num)).hasFDerivAt.comp W Lc.hasFDerivAt
  have hfd : HasFDerivAt (fun U : V => f ‖Ld U‖)
      (fr' • ((1 / (2 * ‖Ld W‖)) • (2 • innerSL ℝ (Ld W)).comp Ld)) W :=
    hf'.comp_hasFDerivAt W hdn
  have hprod : HasFDerivAt (fun U : V => B (Lc U) * f ‖Ld U‖)
      (B (Lc W) • (fr' • ((1 / (2 * ‖Ld W‖)) • (2 • innerSL ℝ (Ld W)).comp Ld))
        + f ‖Ld W‖ • (fderiv ℝ B (Lc W)).comp Lc) W := hBd.mul hfd
  -- the penalty, as a product with the inverse of the squared radius
  have hinv : HasFDerivAt (fun U : V => (‖Ld U‖ ^ 2)⁻¹)
      ((-((‖Ld W‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ (Ld W)).comp Ld) W :=
    (hasDerivAt_inv hsq0).comp_hasFDerivAt W hden
  have hq' : HasFDerivAt (fun U : V => ‖Lh U‖ ^ 2 * (‖Ld U‖ ^ 2)⁻¹)
      (‖Lh W‖ ^ 2 • ((-((‖Ld W‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ (Ld W)).comp Ld)
        + (‖Ld W‖ ^ 2)⁻¹ • (2 • innerSL ℝ (Lh W)).comp Lh) W := hnum.mul hinv
  have hquot : HasFDerivAt (fun U : V => ‖Lh U‖ ^ 2 / ‖Ld U‖ ^ 2)
      (‖Lh W‖ ^ 2 • ((-((‖Ld W‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ (Ld W)).comp Ld)
        + (‖Ld W‖ ^ 2)⁻¹ • (2 • innerSL ℝ (Lh W)).comp Lh) W :=
    hq'.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun U => div_eq_mul_inv (‖Lh U‖ ^ 2) (‖Ld U‖ ^ 2))
  have htot0 := (A.hasFDerivAt.add hprod).add hquot
  have htot : HasFDerivAt
      (fun U : V => A U + B (Lc U) * f ‖Ld U‖ + ‖Lh U‖ ^ 2 / ‖Ld U‖ ^ 2) _ W := htot0
  intro ζ
  rw [htot.fderiv]
  have v1 : ((1 / (2 * ‖Ld W‖)) • (2 • innerSL ℝ (Ld W)).comp Ld) ζ
      = (inner ℝ (‖Ld W‖⁻¹ • Ld W) (Ld ζ) : ℝ) := hDnv ζ
  have v2 : ((2 • innerSL ℝ (Ld W)).comp Ld) ζ = 2 * (inner ℝ (Ld W) (Ld ζ) : ℝ) := by
    simp [ContinuousLinearMap.comp_apply]
  have v3 : ((2 • innerSL ℝ (Lh W)).comp Lh) ζ = 2 * (inner ℝ (Lh W) (Lh ζ) : ℝ) := by
    simp [ContinuousLinearMap.comp_apply]
  have hinner : (inner ℝ (Ld W) (Ld ζ) : ℝ)
      = ‖Ld W‖ * (inner ℝ (‖Ld W‖⁻¹ • Ld W) (Ld ζ) : ℝ) := by
    rw [real_inner_smul_left]; field_simp
  have v4 : ((fderiv ℝ B (Lc W)).comp Lc) ζ = (fderiv ℝ B (Lc W)) (Lc ζ) := rfl
  simp only [add_apply, smul_apply, smul_eq_mul, v1, v2, v3, v4, hinner]
  field_simp
  ring
