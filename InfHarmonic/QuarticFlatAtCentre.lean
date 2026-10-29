module

public import InfHarmonic.Preamble

@[expose] public section
open Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The quartic penalty `Z ↦ ‖Z - Z₀‖⁴` is `C²` and vanishes at `Z₀` to second order:
both its first and its second derivative are zero there.  Adding it to a test function
therefore makes a maximum strict without changing the first or second derivative at the
contact point. -/
theorem QuarticFlatAtCentre (Z₀ : E) :
    ContDiff ℝ 2 (fun Z : E => ‖Z - Z₀‖ ^ 4) ∧
    fderiv ℝ (fun Z : E => ‖Z - Z₀‖ ^ 4) Z₀ = 0 ∧
    fderiv ℝ (fderiv ℝ (fun Z : E => ‖Z - Z₀‖ ^ 4)) Z₀ = 0 := by
  -- the quartic is the square of the squared norm
  have hsq : ∀ Z : E, ‖Z - Z₀‖ ^ 4 = (‖Z - Z₀‖ ^ 2) ^ 2 := by
    intro Z; ring
  have hfun : (fun Z : E => ‖Z - Z₀‖ ^ 4) = fun Z : E => (‖Z - Z₀‖ ^ 2) ^ 2 := by
    funext Z; exact hsq Z
  -- smoothness
  have hcd : ContDiff ℝ 2 (fun Z : E => ‖Z - Z₀‖ ^ 4) := by
    rw [hfun]
    exact ((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).pow 2
  -- the first derivative, everywhere
  have hd : ∀ Z : E, HasFDerivAt (fun Z : E => ‖Z - Z₀‖ ^ 4)
      ((4 * ‖Z - Z₀‖ ^ 2) • innerSL ℝ (Z - Z₀)) Z := by
    intro Z
    have h1 : HasFDerivAt (fun Z : E => Z - Z₀) (ContinuousLinearMap.id ℝ E) Z :=
      (hasFDerivAt_id Z).sub_const Z₀
    have h2 : HasFDerivAt (fun Z : E => ‖Z - Z₀‖ ^ 2)
        (2 • (innerSL ℝ (Z - Z₀)).comp (ContinuousLinearMap.id ℝ E)) Z := h1.norm_sq
    have h2' : HasFDerivAt (fun Z : E => ‖Z - Z₀‖ ^ 2)
        ((2 : ℝ) • (innerSL ℝ (Z - Z₀))) Z := by
      refine h2.congr_fderiv (ContinuousLinearMap.ext fun u : E => ?_)
      simp
    have h3 := h2'.pow 2
    rw [hfun]
    refine h3.congr_fderiv (ContinuousLinearMap.ext fun u : E => ?_)
    simp
    ring
  -- so the first derivative vanishes at the centre
  have hd0 : fderiv ℝ (fun Z : E => ‖Z - Z₀‖ ^ 4) Z₀ = 0 := by
    rw [(hd Z₀).fderiv]
    simp
  refine ⟨hcd, hd0, ?_⟩
  -- the second derivative: a product of two factors that both vanish at the centre
  have hG : fderiv ℝ (fun Z : E => ‖Z - Z₀‖ ^ 4)
      = fun Z : E => (4 * ‖Z - Z₀‖ ^ 2) • innerSL ℝ (Z - Z₀) := by
    funext Z; exact (hd Z).fderiv
  rw [hG]
  have h1 : HasFDerivAt (fun Z : E => Z - Z₀) (ContinuousLinearMap.id ℝ E) Z₀ :=
    (hasFDerivAt_id Z₀).sub_const Z₀
  have hc : HasFDerivAt (fun Z : E => 4 * ‖Z - Z₀‖ ^ 2)
      ((4 : ℝ) • (2 • (innerSL ℝ (Z₀ - Z₀)).comp (ContinuousLinearMap.id ℝ E))) Z₀ :=
    (h1.norm_sq).const_mul 4
  have hf : HasFDerivAt (fun Z : E => innerSL ℝ (Z - Z₀))
      ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).comp (ContinuousLinearMap.id ℝ E)) Z₀ :=
    (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt.comp Z₀ h1
  have hprod := hc.smul hf
  -- pure defeq bridge (Pi.smul versus the lambda): `show`, never `simpa`
  show fderiv ℝ ((fun Z : E => 4 * ‖Z - Z₀‖ ^ 2) • fun Z : E => innerSL ℝ (Z - Z₀)) Z₀ = 0
  rw [hprod.fderiv]
  simp
