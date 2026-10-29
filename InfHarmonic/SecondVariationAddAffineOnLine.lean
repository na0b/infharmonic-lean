import InfHarmonic.Preamble
open Filter Topology

/-- Adding a term that is affine along one straight motion does not change the second
variation in that direction.  This is the mechanism behind "this summand is affine in
`h`, so it contributes nothing": the second-order quantity a common-time sum rule
produces is evaluated on a single fixed direction, so a summand need not be flat in every
direction -- only along the straight motion with that velocity.  Taking `g = 0` recovers
the statement that such a summand has vanishing second variation on its own. -/
theorem SecondVariationAddAffineOnLine {P : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] (g ψ : P → ℝ) (W ζ : P)
    (hg : ContDiffAt ℝ 2 g W) (hψ : ContDiffAt ℝ 2 ψ W) (a b : ℝ)
    (haff : ∀ᶠ h : ℝ in nhds (0:ℝ), ψ (W + h • ζ) = a + b * h) :
    iteratedFDeriv ℝ 2 (fun U => g U + ψ U) W (fun _ => ζ)
      = iteratedFDeriv ℝ 2 g W (fun _ => ζ) := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  -- the straight motion through `W` with velocity `ζ`
  have hγ : ∀ h : ℝ, HasDerivAt (fun s : ℝ => W + s • ζ) ζ h := by
    intro h
    have h1 : HasDerivAt (fun s : ℝ => s • ζ) ζ h := by
      simpa using (hasDerivAt_id h).smul_const ζ
    simpa using h1.const_add W
  have hline : Filter.Tendsto (fun h : ℝ => W + h • ζ) (nhds (0:ℝ)) (nhds W) := by
    have hc : Continuous (fun h : ℝ => W + h • ζ) := by fun_prop
    simpa using hc.tendsto (0:ℝ)
  have hnear : ∀ (u : P → ℝ), ContDiffAt ℝ 2 u W →
      ∀ᶠ h : ℝ in nhds (0:ℝ), DifferentiableAt ℝ u (W + h • ζ) := by
    intro u hu
    have h1 : ∀ᶠ x in nhds W, DifferentiableAt ℝ u x := by
      filter_upwards [hu.eventually (by norm_num)] with x hx
      exact hx.differentiableAt (by norm_num)
    exact hline.eventually h1
  -- the derivative of each function along the motion, as a function of the parameter
  obtain ⟨A, hAd⟩ : ∃ A : ℝ → ℝ,
      A = fun h => fderiv ℝ (fun U => g U + ψ U) (W + h • ζ) ζ := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ B : ℝ → ℝ, B = fun h => fderiv ℝ g (W + h • ζ) ζ := ⟨_, rfl⟩
  -- near `0` the affine summand shifts the derivative along the motion by the constant `b`
  have hAB : ∀ᶠ h : ℝ in nhds (0:ℝ), A h = B h + b := by
    filter_upwards [hnear g hg, hnear ψ hψ, haff.eventually_nhds] with h hdg hdψ haffh
    have hu1 : HasDerivAt (fun s : ℝ => g (W + s • ζ) + ψ (W + s • ζ))
        (fderiv ℝ (fun U => g U + ψ U) (W + h • ζ) ζ) h := by
      have h0 : HasFDerivAt (fun U => g U + ψ U)
          (fderiv ℝ (fun U => g U + ψ U) (W + h • ζ)) (W + h • ζ) :=
        (hdg.add hdψ).hasFDerivAt
      exact h0.comp_hasDerivAt h (hγ h)
    have hu2 : HasDerivAt (fun s : ℝ => g (W + s • ζ) + ψ (W + s • ζ))
        (fderiv ℝ g (W + h • ζ) ζ + b) h := by
      have hg1 : HasDerivAt (fun s : ℝ => g (W + s • ζ)) (fderiv ℝ g (W + h • ζ) ζ) h :=
        hdg.hasFDerivAt.comp_hasDerivAt h (hγ h)
      have hψ1 : HasDerivAt (fun s : ℝ => ψ (W + s • ζ)) b h := by
        have hlin : HasDerivAt (fun s : ℝ => a + b * s) b h := by
          simpa using ((hasDerivAt_id h).const_mul b).const_add a
        exact hlin.congr_of_eventuallyEq haffh
      exact hg1.add hψ1
    simp only [hAd, hBd]
    exact hu1.unique hu2
  -- each of `A` and `B` has, at `0`, the corresponding second variation as its derivative
  have hsnd : ∀ (u : P → ℝ), ContDiffAt ℝ 2 u W →
      HasDerivAt (fun h : ℝ => fderiv ℝ u (W + h • ζ) ζ)
        (fderiv ℝ (fderiv ℝ u) W ζ ζ) 0 := by
    intro u hu
    have h1 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) W) W :=
      ((hu.fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num)).hasFDerivAt
    have h2 : HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) W)
        ((fun s : ℝ => W + s • ζ) 0) := by simpa using h1
    have h3 : HasDerivAt (fun h : ℝ => fderiv ℝ u (W + h • ζ))
        (fderiv ℝ (fderiv ℝ u) W ζ) 0 := h2.comp_hasDerivAt (0:ℝ) (hγ 0)
    have h4 := h3.clm_apply (hasDerivAt_const (0:ℝ) ζ)
    simpa using h4
  have hAderiv : HasDerivAt A
      (fderiv ℝ (fderiv ℝ (fun U => g U + ψ U)) W ζ ζ) 0 := by
    rw [hAd]; exact hsnd _ (hg.add hψ)
  have hBderiv : HasDerivAt B (fderiv ℝ (fderiv ℝ g) W ζ ζ) 0 := by
    rw [hBd]; exact hsnd g hg
  -- `A` agrees near `0` with `B` plus a constant, so the two derivatives at `0` agree
  have hAderiv' : HasDerivAt A (fderiv ℝ (fderiv ℝ g) W ζ ζ) 0 := by
    have h1 : HasDerivAt (fun h : ℝ => B h + b) (fderiv ℝ (fderiv ℝ g) W ζ ζ) 0 := by
      simpa using hBderiv.add_const b
    exact h1.congr_of_eventuallyEq hAB
  exact hAderiv.unique hAderiv'
