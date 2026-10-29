module

public import InfHarmonic.Preamble

@[expose] public section

/-- The first and second variations of a `C²` function along a straight line are computed
by any one-variable function that agrees with the restriction near the base point.  This is
the bridge from the second iterated Fréchet derivative, which is what the limiting
operator of \noderef{LimitOp} is stated with, to an ordinary one-dimensional second
derivative, which is what an explicit test function can be differentiated by hand.
It is strictly more general than \noderef{SecondVariationAddAffineOnLine}, which
only discards a summand whose restriction is affine: here the restriction may be any
function with a second derivative at the base point, and it is identified only up to
agreement on a neighbourhood, so the bookkeeping of the algebraic rearrangement can
be done on a neighbourhood rather than globally. -/
theorem SecondVariationAlongLine {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : P → ℝ) (W ζ : P) (hg : ContDiffAt ℝ 2 g W)
    (r r' : ℝ → ℝ) (c : ℝ)
    (hgr : ∀ᶠ h : ℝ in nhds (0:ℝ), g (W + h • ζ) = r h)
    (hr : ∀ᶠ h : ℝ in nhds (0:ℝ), HasDerivAt r (r' h) h)
    (hr2 : HasDerivAt r' c 0) :
    fderiv ℝ g W ζ = r' 0 ∧ iteratedFDeriv ℝ 2 g W (fun _ => ζ) = c := by
  -- the straight line through `W` with velocity `ζ`
  have hline : HasDerivAt (fun h : ℝ => W + h • ζ) ζ 0 := by
    have h1 : HasDerivAt (fun h : ℝ => h • ζ) ζ 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const ζ
    simpa using h1.const_add W
  have hcline : Continuous (fun h : ℝ => W + h • ζ) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- evaluation at `ζ`, as a continuous linear map on the dual
  obtain ⟨E, hE⟩ : ∃ E : (P →L[ℝ] ℝ) →L[ℝ] ℝ, ∀ φ : P →L[ℝ] ℝ, E φ = φ ζ :=
    ⟨ContinuousLinearMap.apply ℝ ℝ ζ, fun φ => rfl⟩
  -- `g` is differentiable near `W`, and `fderiv ℝ g` is differentiable at `W`
  have hdiff : ∀ᶠ y : P in nhds W, DifferentiableAt ℝ g y := by
    filter_upwards [hg.eventually (by simp)] with y hy
    exact hy.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fderiv ℝ g) W :=
    (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hfdline : ∀ᶠ h : ℝ in nhds (0:ℝ), DifferentiableAt ℝ g (W + h • ζ) := by
    have htend : Filter.Tendsto (fun h : ℝ => W + h • ζ) (nhds (0:ℝ)) (nhds W) := by
      have h := hcline.tendsto 0
      simpa using h
    exact htend.eventually hdiff
  -- near `0` the given derivative `r'` is the directional derivative of `g`
  have key : ∀ᶠ h : ℝ in nhds (0:ℝ), r' h = E (fderiv ℝ g (W + h • ζ)) := by
    filter_upwards [eventually_eventually_nhds.mpr hgr, hr, hfdline]
      with h hagree hrh hdh
    have hee : (fun k : ℝ => g (W + k • ζ)) =ᶠ[nhds h] r := hagree
    have hlh : HasDerivAt (fun k : ℝ => W + k • ζ) ζ h := by
      have h2 : HasDerivAt (fun k : ℝ => k • ζ) ζ h := by
        simpa using (hasDerivAt_id h).smul_const ζ
      simpa using h2.const_add W
    have h1 : HasDerivAt (fun k : ℝ => g (W + k • ζ)) (fderiv ℝ g (W + h • ζ) ζ) h :=
      hdh.hasFDerivAt.comp_hasDerivAt h hlh
    rw [hE]
    exact hrh.unique (h1.congr_of_eventuallyEq hee.symm)
  -- and the directional derivative is itself differentiable at `0`, with the second
  -- Fréchet derivative as its derivative
  have hd2' : HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) W) (W + (0:ℝ) • ζ) := by
    rw [zero_smul, add_zero]; exact hd2.hasFDerivAt
  have hL : HasDerivAt (fun h : ℝ => E (fderiv ℝ g (W + h • ζ)))
      (E (fderiv ℝ (fderiv ℝ g) W ζ)) 0 :=
    E.hasFDerivAt.comp_hasDerivAt 0 (hd2'.comp_hasDerivAt 0 hline)
  have hL' : HasDerivAt r' (E (fderiv ℝ (fderiv ℝ g) W ζ)) 0 :=
    hL.congr_of_eventuallyEq key
  -- the first variation is the value of `r'` at the base point
  have hfirst : fderiv ℝ g W ζ = r' 0 := by
    have h0 := key.self_of_nhds
    rw [hE, zero_smul, add_zero] at h0
    exact h0.symm
  refine ⟨hfirst, ?_⟩
  rw [iteratedFDeriv_two_apply]
  have hcE := hr2.unique hL'
  rw [hcE, hE]
