module

public import InfHarmonic.ClosedSuperjet
public import InfHarmonic.IsInfSubsolutionOn

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- An infinity subsolution satisfies the operator inequality on its closed
superjets, not only at `C²` upper tests. -/
theorem InfSubsolutionClosedSuperjet (Ω : Set E) (u : E → ℝ)
    (hu : IsInfSubsolutionOn Ω u) (z : E) (hz : z ∈ Ω)
    (p : E) (X : E →L[ℝ] E →L[ℝ] ℝ) (hpX : (p, X) ∈ ClosedSuperjet u z) :
    0 ≤ X p p := by
  -- Step 1: the inequality at a plain superjet.
  have step1 : ∀ a : E, a ∈ Ω → ∀ (q : E) (Y : E →L[ℝ] E →L[ℝ] ℝ),
      (q, Y) ∈ Superjet u a → 0 ≤ Y q q := by
    intro a ha q Y hqY
    obtain ⟨hsymm, hjet⟩ := hqY
    -- The real inner product as an honest `ℝ`-bilinear continuous form, so that it can be
    -- added to `Y`. (`innerSL ℝ` is typed conjugate-linear in its first slot and cannot be.)
    set B : E →L[ℝ] E →L[ℝ] ℝ :=
      (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap with hBdef
    have hB : ∀ v w : E, B v w = inner ℝ v w := fun v w => rfl
    have hgradB : ∀ v : E, (InnerProductSpace.toDual ℝ E).symm (B v) = v := by
      intro v
      have h : (InnerProductSpace.toDual ℝ E) v = B v := ContinuousLinearMap.ext fun w => rfl
      rw [h.symm]
      simp
    -- The family of upper tests `φ_ε`, written with the single bilinear form
    -- `Z = Y/2 + εB`, so that `Z w w = Y w w / 2 + ε‖w‖²`.
    have key : ∀ ε : ℝ, 0 < ε → 0 ≤ Y q q + 2 * ε * ‖q‖ ^ 2 := by
      intro ε hε
      set Z : E →L[ℝ] E →L[ℝ] ℝ := (1/2 : ℝ) • Y + ε • B with hZdef
      set W : E →L[ℝ] E →L[ℝ] ℝ := Z + ContinuousLinearMap.flip Z with hWdef
      have hZ : ∀ w : E, Z w w = Y w w / 2 + ε * ‖w‖ ^ 2 := by
        intro w
        rw [hZdef]
        simp [hB]
        ring
      set ψ : E → ℝ := fun x => u a + B q (x - a) + Z (x - a) (x - a) with hψdef
      have hsub : ∀ x : E, HasFDerivAt (fun y : E => y - a) (ContinuousLinearMap.id ℝ E) x :=
        fun x => (hasFDerivAt_id x).sub_const a
      -- the linear part
      have hlin : ∀ x : E, HasFDerivAt (fun y : E => B q (y - a)) (B q) x := by
        intro x
        refine (((B q).hasFDerivAt (x := x - a)).comp x (hsub x)).congr_fderiv ?_
        apply ContinuousLinearMap.ext; intro h
        simp
      -- the quadratic part: its derivative at `x` is `W (x - a)`
      have hT : ∀ x : E, HasFDerivAt (fun y : E => Z (y - a) (y - a)) (W (x - a)) x := by
        intro x
        refine ((Z.hasFDerivAt.comp x (hsub x)).clm_apply (hsub x)).congr_fderiv ?_
        apply ContinuousLinearMap.ext; intro h
        simp [hWdef]
      have hψD : ∀ x : E, HasFDerivAt ψ (B q + W (x - a)) x :=
        fun x => ((hlin x).const_add (u a)).add (hT x)
      have hfd : fderiv ℝ ψ = fun x => B q + W (x - a) :=
        funext fun x => (hψD x).fderiv
      -- the gradient at the contact point is `q`
      have hgrad : gradient ψ a = q := by
        unfold gradient
        rw [(hψD a).fderiv]
        simpa using hgradB q
      -- the 2-jet at the contact point is `W`
      have hjet2 : ∀ v : E, iteratedFDeriv ℝ 2 ψ a (fun _ => v) = W v v := by
        intro v
        have hd2 : HasFDerivAt (fun x : E => B q + W (x - a)) W a := by
          refine ((W.hasFDerivAt.comp a (hsub a)).const_add (B q)).congr_fderiv ?_
          apply ContinuousLinearMap.ext; intro h
          simp
        rw [iteratedFDeriv_two_apply, hfd, hd2.fderiv]
      -- `ψ` is `C²`
      have hψC : ContDiff ℝ 2 ψ := by
        have hq : ContDiff ℝ 2 (fun y : E => B q (y - a)) :=
          (B q).contDiff.comp (contDiff_id.sub contDiff_const)
        have hT' : ContDiff ℝ 2 (fun y : E => Z (y - a) (y - a)) :=
          (Z.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
            (contDiff_id.sub contDiff_const)
        exact (contDiff_const.add hq).add hT'
      -- the value of the operator at the contact point
      have hWqq : W q q = Y q q + 2 * ε * ‖q‖ ^ 2 := by
        rw [hWdef]
        simp only [add_apply, ContinuousLinearMap.flip_apply]
        rw [hZ q]
        ring
      -- `ψ` is an upper test for `u` at `a`
      obtain ⟨δ, hδ, hball⟩ := hjet ε hε
      have hψa : ψ a = u a := by simp [hψdef]
      have hlocmax : IsLocalMaxOn (fun x => u x - ψ x) Ω a := by
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [Metric.ball_mem_nhds a hδ] with x hx
        have hd : ‖x - a‖ < δ := by
          simpa [dist_eq_norm] using Metric.mem_ball.mp hx
        have hb := hball (x - a) hd
        have hax : a + (x - a) = x := by abel
        rw [hax] at hb
        have hψx : ψ x = u a + inner ℝ q (x - a) + Y (x - a) (x - a) / 2
            + ε * ‖x - a‖ ^ 2 := by
          simp only [hψdef]
          rw [hZ (x - a), hB q (x - a)]
          ring
        simp only [hψa, hψx]
        simp only at hb
        linarith
      -- the subsolution inequality
      have hsubsol := hu.2.2 a ha ψ hψC.contDiffAt hlocmax
      rw [InfLap, hgrad, hjet2 q, hWqq] at hsubsol
      exact hsubsol
    -- let `ε` tend to zero
    by_contra hcon
    push Not at hcon
    have hpos : 0 < -(Y q q) := by linarith
    have hden : (0:ℝ) < 2 * (‖q‖ ^ 2 + 1) := by positivity
    have h2 := key (-(Y q q) / (2 * (‖q‖ ^ 2 + 1))) (div_pos hpos hden)
    have h3 : 0 ≤ (Y q q + 2 * (-(Y q q) / (2 * (‖q‖ ^ 2 + 1))) * ‖q‖ ^ 2) *
        (2 * (‖q‖ ^ 2 + 1)) := mul_nonneg h2 hden.le
    have h4 : (Y q q + 2 * (-(Y q q) / (2 * (‖q‖ ^ 2 + 1))) * ‖q‖ ^ 2) *
        (2 * (‖q‖ ^ 2 + 1)) = 2 * Y q q := by
      field_simp
      ring
    rw [h4] at h3
    linarith
  -- Step 2: passing to the closure.
  obtain ⟨zs, ps, Xs, hsj, hzl, -, hpl, hXl⟩ := hpX
  obtain ⟨δ₀, hδ₀, hball₀⟩ := Metric.isOpen_iff.mp hu.1 z hz
  have hnn : ∀ᶠ k : ℕ in Filter.atTop, 0 ≤ Xs k (ps k) (ps k) := by
    filter_upwards [Metric.tendsto_nhds.mp hzl δ₀ hδ₀] with k hk
    exact step1 (zs k) (hball₀ (Metric.mem_ball.mpr hk)) (ps k) (Xs k) (hsj k)
  have hlim : Filter.Tendsto (fun k => Xs k (ps k) (ps k)) Filter.atTop (nhds (X p p)) := by
    have h1 : Filter.Tendsto (fun k => Xs k (ps k)) Filter.atTop (nhds (X p)) := by
      simpa [Function.comp_def] using
        (isBoundedBilinearMap_apply.continuous.tendsto (X, p)).comp (hXl.prodMk_nhds hpl)
    simpa [Function.comp_def] using
      (isBoundedBilinearMap_apply.continuous.tendsto (X p, p)).comp (h1.prodMk_nhds hpl)
  exact ge_of_tendsto hlim hnn
