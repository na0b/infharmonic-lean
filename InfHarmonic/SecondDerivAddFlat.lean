module

public import InfHarmonic.Preamble

@[expose] public section
open Filter Topology

/-- Adding a function that is flat to second order at a point changes neither the first
nor the second derivative there.  This is what makes a strictifying perturbation free:
one adds a term with a strict sign away from the centre, and at the centre itself the
first- and second-order data are untouched. -/
theorem SecondDerivAddFlat {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    (f g : Q → ℝ) (x : Q) (hf : ContDiffAt ℝ 2 f x) (hg : ContDiff ℝ 2 g)
    (hg1 : fderiv ℝ g x = 0) (hg2 : fderiv ℝ (fderiv ℝ g) x = 0) :
    fderiv ℝ (fun y => f y + g y) x = fderiv ℝ f x
      ∧ fderiv ℝ (fderiv ℝ (fun y => f y + g y)) x = fderiv ℝ (fderiv ℝ f) x := by
  have hgd : ∀ y, HasFDerivAt g (fderiv ℝ g y) y :=
    fun y => (hg.differentiable (by norm_num) y).hasFDerivAt
  constructor
  · -- the first derivative
    have h1 : HasFDerivAt (fun y => f y + g y) (fderiv ℝ f x + fderiv ℝ g x) x :=
      (hf.differentiableAt (by norm_num)).hasFDerivAt.add (hgd x)
    rw [h1.fderiv, hg1, add_zero]
  · -- the second derivative
    have hA : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
      ((hf.fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num)).hasFDerivAt
    have hB : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) x) x :=
      (((hg.contDiffAt.fderiv_right (m := 1) le_rfl)).differentiableAt (by norm_num)).hasFDerivAt
    -- the first derivative of the sum splits on a neighbourhood of `x`
    have hev : fderiv ℝ (fun y => f y + g y)
        =ᶠ[𝓝 x] fun y => fderiv ℝ f y + fderiv ℝ g y := by
      filter_upwards [hf.eventually (by norm_num)] with y hy
      exact ((hy.differentiableAt (by norm_num)).hasFDerivAt.add (hgd y)).fderiv
    have hsd : HasFDerivAt (fderiv ℝ (fun y => f y + g y))
        (fderiv ℝ (fderiv ℝ f) x + fderiv ℝ (fderiv ℝ g) x) x :=
      (hA.add hB).congr_of_eventuallyEq hev
    rw [hsd.fderiv, hg2, add_zero]
