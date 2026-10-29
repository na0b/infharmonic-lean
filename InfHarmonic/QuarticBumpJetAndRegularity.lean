module

public import InfHarmonic.LimitOp

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 1 of the viscosity stability argument: adding the quartic bump
`s * (‖ζ - z‖ ^ 2) ^ 2` to a test function `φ` that is `C²` at `z` leaves the
limiting operator at `z` unchanged, because the bump's second derivative
vanishes at `z`, and the sum is `C²` on some open neighbourhood of `z`
contained in `Ω`. -/
theorem QuarticBumpJetAndRegularity (Ω : Set (WithLp 2 (F × ℝ))) (hΩ : IsOpen Ω)
    (z : WithLp 2 (F × ℝ)) (hz : z ∈ Ω) (s : ℝ)
    (φ : WithLp 2 (F × ℝ) → ℝ) (hφ : ContDiffAt ℝ 2 φ z) :
    LimitOp (φ + fun ζ => s * (‖ζ - z‖ ^ 2) ^ 2) z = LimitOp φ z ∧
      ∃ V : Set (WithLp 2 (F × ℝ)), IsOpen V ∧ z ∈ V ∧ V ⊆ Ω ∧
        ContDiffOn ℝ 2 (φ + fun ζ => s * (‖ζ - z‖ ^ 2) ^ 2) V := by
  set q : WithLp 2 (F × ℝ) → ℝ := fun ζ => s * (‖ζ - z‖ ^ 2) ^ 2 with hqdef
  set ψ : WithLp 2 (F × ℝ) → ℝ := φ + q with hψdef
  have hnormsq : ContDiff ℝ 2 (fun ζ : WithLp 2 (F × ℝ) => ‖ζ - z‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  have hqC : ContDiff ℝ 2 q := contDiff_const.mul (hnormsq.pow 2)
  -- the everywhere derivative of the bump
  have hD : ∀ ζ : WithLp 2 (F × ℝ),
      HasFDerivAt q ((s * (4 * ‖ζ - z‖ ^ 2)) • innerSL ℝ (ζ - z)) ζ := by
    intro ζ
    have h1 : HasFDerivAt (fun w : WithLp 2 (F × ℝ) => w - z)
        (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))) ζ := (hasFDerivAt_id ζ).sub_const z
    refine (((h1.norm_sq).pow 2).const_mul s).congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    simp
    ring
  have hfd : fderiv ℝ q = fun ζ => (s * (4 * ‖ζ - z‖ ^ 2)) • innerSL ℝ (ζ - z) :=
    funext fun ζ => (hD ζ).fderiv
  -- the second derivative of the bump vanishes at the contact point: `eq:ls-fourth`
  have hD2 : fderiv ℝ (fderiv ℝ q) z
      = (0 : WithLp 2 (F × ℝ) →L[ℝ] (WithLp 2 (F × ℝ) →L[ℝ] ℝ)) := by
    rw [hfd]
    have hsub : HasFDerivAt (fun w : WithLp 2 (F × ℝ) => w - z)
        (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))) z := (hasFDerivAt_id z).sub_const z
    have hc : HasFDerivAt (fun ζ : WithLp 2 (F × ℝ) => s * (4 * ‖ζ - z‖ ^ 2))
        ((s * 4) • (2 • (innerSL ℝ (z - z)).comp
          (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))))) z := by
      refine (((hsub.norm_sq).const_mul (4 : ℝ)).const_mul s).congr_fderiv ?_
      apply ContinuousLinearMap.ext; intro u; simp
    have hf : HasFDerivAt (fun ζ : WithLp 2 (F × ℝ) => innerSL ℝ (ζ - z))
        ((innerSL ℝ (E := WithLp 2 (F × ℝ))).comp
          (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ)))) z :=
      (innerSL ℝ (E := WithLp 2 (F × ℝ))).hasFDerivAt.comp z hsub
    exact ((hc.smul hf).congr_fderiv (by simp)).fderiv
  have hjet : ∀ w : WithLp 2 (F × ℝ), iteratedFDeriv ℝ 2 q z (fun _ => w) = 0 := by
    intro w; rw [iteratedFDeriv_two_apply, hD2]; simp
  -- `eq:ls-same-jet`: the strictified test has the same 2-jet at `z`
  have hjetid : LimitOp ψ z = LimitOp φ z := by
    have hq0 : fderiv ℝ q z = 0 := by rw [hfd]; simp
    have hgrad : gradient ψ z = gradient φ z := by
      unfold gradient
      rw [hψdef, fderiv_add (hφ.differentiableAt (by norm_num))
        ((hqC.differentiable (by norm_num)).differentiableAt), hq0]
      simp
    unfold LimitOp
    rw [hgrad, hψdef,
      iteratedFDeriv_add_apply (i := 2) hφ hqC.contDiffAt]
    simp [hjet]
  -- a neighbourhood of `z` on which `ψ` is `C²`, inside `Ω`
  obtain ⟨u, hu, hφu⟩ := hφ.contDiffOn (m := 2) le_rfl (by simp)
  obtain ⟨V₀, hV₀u, hV₀open, hzV₀⟩ := _root_.mem_nhds_iff.mp hu
  set V : Set (WithLp 2 (F × ℝ)) := V₀ ∩ Ω with hVdef
  have hVopen : IsOpen V := hV₀open.inter hΩ
  have hzV : z ∈ V := ⟨hzV₀, hz⟩
  have hVΩ : V ⊆ Ω := inter_subset_right
  have hψV : ContDiffOn ℝ 2 ψ V :=
    (hφu.mono (fun w hw => hV₀u hw.1)).add (hqC.contDiffOn.mono (subset_univ _))
  exact ⟨hjetid, V, hVopen, hzV, hVΩ, hψV⟩
