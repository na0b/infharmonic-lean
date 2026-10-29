import InfHarmonic.IsInfHarmonicOn
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Affine rescaling preserves infinity-harmonicity: for `A > 0` the function
`y ↦ u (x₀ + A • y)` is infinity-harmonic on the preimage of `Ω`. -/
theorem InfHarmonicRescale (Ω : Set E) (u : E → ℝ) (hu : IsInfHarmonicOn Ω u)
    (x₀ : E) (A : ℝ) (hA : 0 < A) :
    IsInfHarmonicOn ((fun y : E => x₀ + A • y) ⁻¹' Ω) (fun y : E => u (x₀ + A • y)) := by
  obtain ⟨⟨hΩ, hcu, hsub⟩, ⟨-, -, hsup⟩⟩ := hu
  have hAne : A ≠ 0 := ne_of_gt hA
  -- Step 0: `T y = x₀ + A • y` is an affine homeomorphism with `T⁻¹ x = A⁻¹ • (x - x₀)`,
  -- so `T ⁻¹' Ω` is open and `u ∘ T` is continuous on it.
  have hTcont : Continuous (fun y : E => x₀ + A • y) := by fun_prop
  have hopen : IsOpen ((fun y : E => x₀ + A • y) ⁻¹' Ω) := hΩ.preimage hTcont
  have hcont : ContinuousOn (fun y : E => u (x₀ + A • y))
      ((fun y : E => x₀ + A • y) ⁻¹' Ω) :=
    hcu.comp hTcont.continuousOn (Set.mapsTo_preimage _ _)
  have hcancel : ∀ w : E, (A * A⁻¹) • w = w := by
    intro w; rw [mul_inv_cancel₀ hAne, one_smul]
  have hcancel' : ∀ w : E, (A⁻¹ * A) • w = w := by
    intro w; rw [inv_mul_cancel₀ hAne, one_smul]
  have hST : ∀ w : E, A⁻¹ • (x₀ + A • w - x₀) = w := by
    intro w; rw [add_sub_cancel_left, smul_smul]; exact hcancel' w
  have hTS : ∀ x : E, x₀ + A • (A⁻¹ • (x - x₀)) = x := by
    intro x; rw [smul_smul, hcancel (x - x₀)]; abel
  -- Step 1: the chain rule gives `∇(g ∘ T)(y) = A ∇g(T y)`.
  have hgradcomp : ∀ (g : E → ℝ) (y : E), DifferentiableAt ℝ g (x₀ + A • y) →
      gradient (fun w : E => g (x₀ + A • w)) y = A • gradient g (x₀ + A • y) := by
    intro g y hg
    have hTd : HasFDerivAt (fun w : E => x₀ + A • w)
        (A • ContinuousLinearMap.id ℝ E) y := by
      simpa using ((hasFDerivAt_id y).const_smul A).const_add x₀
    have hcomp : HasFDerivAt (fun w : E => g (x₀ + A • w))
        ((fderiv ℝ g (x₀ + A • y)).comp (A • ContinuousLinearMap.id ℝ E)) y :=
      hg.hasFDerivAt.comp y hTd
    have heq : (fderiv ℝ g (x₀ + A • y)).comp (A • ContinuousLinearMap.id ℝ E)
        = A • fderiv ℝ g (x₀ + A • y) := by
      ext v; simp
    rw [heq] at hcomp
    have hgr : HasGradientAt (fun w : E => g (x₀ + A • w))
        (A • gradient g (x₀ + A • y)) y := by
      rw [hasGradientAt_iff_hasFDerivAt]
      simpa using hcomp
    exact hgr.gradient
  -- Step 2: `T` has zero second derivative, so `D²(g ∘ T)(y)[v,v] = A² D²g(T y)[v,v]`.
  have hsecond : ∀ (g : E → ℝ) (y v : E),
      iteratedFDeriv ℝ 2 (fun w : E => g (x₀ + A • w)) y (fun _ => v)
        = A ^ 2 * iteratedFDeriv ℝ 2 g (x₀ + A • y) (fun _ => v) := by
    intro g y v
    let L : E ≃L[ℝ] E :=
      ContinuousLinearEquiv.equivOfInverse (A • ContinuousLinearMap.id ℝ E)
        (A⁻¹ • ContinuousLinearMap.id ℝ E)
        (fun w => by simpa [smul_smul] using hcancel w)
        (fun w => by simpa [smul_smul] using hcancel' w)
    have hLapp : ∀ w : E, L w = A • w := by intro w; simp [L]
    have hfun : (fun w : E => g (x₀ + A • w)) = (fun z : E => g (x₀ + z)) ∘ L := by
      funext w; simp [hLapp w]
    have hstep := L.iteratedFDerivWithin_comp_right (fun z : E => g (x₀ + z))
      (s := univ) uniqueDiffOn_univ (x := y) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hstep
    rw [hfun, hstep, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp only [ContinuousLinearEquiv.coe_coe, hLapp, iteratedFDeriv_comp_add_left]
    simpa using (iteratedFDeriv ℝ 2 g (x₀ + A • y)).map_smul_univ
      (fun _ : Fin 2 => A) (fun _ : Fin 2 => v)
  -- Step 3: both slots of the jet scale, so `Δ_∞(g ∘ T)(y) = A⁴ Δ_∞ g(T y)`.
  have hkey : ∀ (g : E → ℝ) (y : E), DifferentiableAt ℝ g (x₀ + A • y) →
      InfLap (fun w : E => g (x₀ + A • w)) y = A ^ 4 * InfLap g (x₀ + A • y) := by
    intro g y hg
    simp only [InfLap]
    rw [hgradcomp g y hg, hsecond g y (A • gradient g (x₀ + A • y))]
    have happ : iteratedFDeriv ℝ 2 g (x₀ + A • y) (fun _ => A • gradient g (x₀ + A • y))
        = A ^ 2 * iteratedFDeriv ℝ 2 g (x₀ + A • y) (fun _ => gradient g (x₀ + A • y)) := by
      simpa using (iteratedFDeriv ℝ 2 g (x₀ + A • y)).map_smul_univ
        (fun _ : Fin 2 => A) (fun _ : Fin 2 => gradient g (x₀ + A • y))
    rw [happ]
    ring
  refine ⟨⟨hopen, hcont, ?_⟩, ⟨hopen, hcont, ?_⟩⟩
  · -- Upper tests: `φ = ψ ∘ T⁻¹` is a `C²` upper test for `u` at `T y₀`.
    intro y₀ hy₀ ψ hψ hmax
    have hy₀' : x₀ + A • y₀ ∈ Ω := hy₀
    have hSy : A⁻¹ • (x₀ + A • y₀ - x₀) = y₀ := hST y₀
    have hφ : ContDiffAt ℝ 2 (fun x : E => ψ (A⁻¹ • (x - x₀))) (x₀ + A • y₀) := by
      have h1 : ContDiffAt ℝ 2 (fun x : E => A⁻¹ • (x - x₀)) (x₀ + A • y₀) := by fun_prop
      have h2 : ContDiffAt ℝ 2 ψ (A⁻¹ • (x₀ + A • y₀ - x₀)) := by rw [hSy]; exact hψ
      exact h2.comp (x₀ + A • y₀) h1
    have hmax' : IsLocalMaxOn (fun x : E => u x - ψ (A⁻¹ • (x - x₀))) Ω (x₀ + A • y₀) := by
      have hSc : ContinuousWithinAt (fun x : E => A⁻¹ • (x - x₀)) Ω (x₀ + A • y₀) := by
        fun_prop
      have hmaps : Set.MapsTo (fun x : E => A⁻¹ • (x - x₀)) Ω
          ((fun y : E => x₀ + A • y) ⁻¹' Ω) := by
        intro x hx; simpa [hTS x] using hx
      have htend := hSc.tendsto_nhdsWithin hmaps
      simp only [hSy] at htend
      refine Filter.Eventually.mono (htend.eventually hmax) fun x hx => ?_
      simp only [hSy]
      simpa only [hTS] using hx
    have h := hsub (x₀ + A • y₀) hy₀' (fun x : E => ψ (A⁻¹ • (x - x₀))) hφ hmax'
    have hscale : InfLap ψ y₀
        = A ^ 4 * InfLap (fun x : E => ψ (A⁻¹ • (x - x₀))) (x₀ + A • y₀) := by
      simpa only [hST] using
        hkey (fun x : E => ψ (A⁻¹ • (x - x₀))) y₀ (hφ.differentiableAt (by norm_num))
    rw [hscale]
    exact mul_nonneg (by positivity) h
  · -- Lower tests: the mirror argument with minima.
    intro y₀ hy₀ ψ hψ hmin
    have hy₀' : x₀ + A • y₀ ∈ Ω := hy₀
    have hSy : A⁻¹ • (x₀ + A • y₀ - x₀) = y₀ := hST y₀
    have hφ : ContDiffAt ℝ 2 (fun x : E => ψ (A⁻¹ • (x - x₀))) (x₀ + A • y₀) := by
      have h1 : ContDiffAt ℝ 2 (fun x : E => A⁻¹ • (x - x₀)) (x₀ + A • y₀) := by fun_prop
      have h2 : ContDiffAt ℝ 2 ψ (A⁻¹ • (x₀ + A • y₀ - x₀)) := by rw [hSy]; exact hψ
      exact h2.comp (x₀ + A • y₀) h1
    have hmin' : IsLocalMinOn (fun x : E => u x - ψ (A⁻¹ • (x - x₀))) Ω (x₀ + A • y₀) := by
      have hSc : ContinuousWithinAt (fun x : E => A⁻¹ • (x - x₀)) Ω (x₀ + A • y₀) := by
        fun_prop
      have hmaps : Set.MapsTo (fun x : E => A⁻¹ • (x - x₀)) Ω
          ((fun y : E => x₀ + A • y) ⁻¹' Ω) := by
        intro x hx; simpa [hTS x] using hx
      have htend := hSc.tendsto_nhdsWithin hmaps
      simp only [hSy] at htend
      refine Filter.Eventually.mono (htend.eventually hmin) fun x hx => ?_
      simp only [hSy]
      simpa only [hTS] using hx
    have h := hsup (x₀ + A • y₀) hy₀' (fun x : E => ψ (A⁻¹ • (x - x₀))) hφ hmin'
    have hscale : InfLap ψ y₀
        = A ^ 4 * InfLap (fun x : E => ψ (A⁻¹ • (x - x₀))) (x₀ + A • y₀) := by
      simpa only [hST] using
        hkey (fun x : E => ψ (A⁻¹ • (x - x₀))) y₀ (hφ.differentiableAt (by norm_num))
    rw [hscale]
    have hA4 : (0 : ℝ) ≤ A ^ 4 := by positivity
    nlinarith [h, hA4]
