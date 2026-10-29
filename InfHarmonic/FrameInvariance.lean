import InfHarmonic.IsFitClass
import InfHarmonic.FrameChange
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.1, changes of frame: a sheared change of frame preserves the class
`A_{m,C₀}`, and transforms a fit at the corresponding center and radius
`R ρ` into the fit with parameters subtracted at radius `ρ`. -/
theorem FrameInvariance (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (z₀ : WithLp 2 (F × ℝ)) (R : ℝ) (hR : 0 < R) (p₀ : F) (a₀ : ℝ) :
    IsFitClass C₀ (FrameChange v z₀ R p₀ a₀) ∧
    ∀ (ζ : WithLp 2 (F × ℝ)) (ρ : ℝ) (p : F) (a : ℝ),
      IsFit C₀ v
          (z₀ + toLp 2 (R • ((ofLp ζ).1 + (ofLp ζ).2 • p₀), R * (ofLp ζ).2)) (R * ρ) p a →
        IsFit C₀ (FrameChange v z₀ R p₀ a₀) ζ ρ (p - p₀) (a - a₀) := by
  -- The proof runs in three steps, after a block of reusable infrastructure.
  -- Infrastructure: the change of frame `ζ ↦ z₀ + L ζ` as a genuine affine
  -- homeomorphism, its 2-jet transfer, and the affine part of `FrameChange`
  -- as a continuous linear map.  Step 1 shows the frame change is again a
  -- limit solution on all of space-time; Step 2 is the fit transformation;
  -- Step 3 feeds Step 2 the fits of `v` to get the fits of the frame change.
  have hRne : R ≠ 0 := ne_of_gt hR
  -- The shear `(y, s) ↦ (R • (y + s • p₀), R * s)` on the PLAIN product, with
  -- its inverse.  A `prodMap` will not do: the shear couples the two blocks.
  obtain ⟨SP, hSP⟩ : ∃ SP : (F × ℝ) →L[ℝ] (F × ℝ),
      ∀ q : F × ℝ, SP q = (R • (q.1 + q.2 • p₀), R * q.2) :=
    ⟨(R • (ContinuousLinearMap.fst ℝ F ℝ
        + (ContinuousLinearMap.snd ℝ F ℝ).smulRight p₀)).prod
      (R • ContinuousLinearMap.snd ℝ F ℝ), by intro q; simp⟩
  obtain ⟨SI, hSI⟩ : ∃ SI : (F × ℝ) →L[ℝ] (F × ℝ),
      ∀ q : F × ℝ, SI q = (R⁻¹ • q.1 - (R⁻¹ * q.2) • p₀, R⁻¹ * q.2) :=
    ⟨((R⁻¹ • ContinuousLinearMap.fst ℝ F ℝ)
        - (R⁻¹ • ContinuousLinearMap.snd ℝ F ℝ).smulRight p₀).prod
      (R⁻¹ • ContinuousLinearMap.snd ℝ F ℝ), by intro q; simp⟩
  have hleft : ∀ q : F × ℝ, SI (SP q) = q := by
    intro q
    have hRR : R⁻¹ * R = 1 := inv_mul_cancel₀ hRne
    rw [hSP, hSI]
    refine Prod.ext ?_ ?_
    · show R⁻¹ • (R • (q.1 + q.2 • p₀)) - (R⁻¹ * (R * q.2)) • p₀ = q.1
      rw [smul_smul, hRR, one_smul, ← mul_assoc, hRR, one_mul]; abel
    · show R⁻¹ * (R * q.2) = q.2
      rw [← mul_assoc, hRR, one_mul]
  have hright : ∀ q : F × ℝ, SP (SI q) = q := by
    intro q
    have hRR : R * R⁻¹ = 1 := mul_inv_cancel₀ hRne
    rw [hSI, hSP]
    refine Prod.ext ?_ ?_
    · show R • ((R⁻¹ • q.1 - (R⁻¹ * q.2) • p₀) + (R⁻¹ * q.2) • p₀) = q.1
      rw [sub_add_cancel, smul_smul, hRR, one_smul]
    · show R * (R⁻¹ * q.2) = q.2
      rw [← mul_assoc, hRR, one_mul]
  -- On space-time, by CONJUGATION through `prodContinuousLinearEquiv`: no
  -- round trip has to be proved in `WithLp` at all, and the apply lemma lands
  -- exactly on the inner argument of `FrameChange`.
  obtain ⟨L, hL⟩ : ∃ L : WithLp 2 (F × ℝ) ≃L[ℝ] WithLp 2 (F × ℝ),
      ∀ z : WithLp 2 (F × ℝ),
        L z = toLp 2 (R • ((ofLp z).1 + (ofLp z).2 • p₀), R * (ofLp z).2) :=
    ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).trans
      ((ContinuousLinearEquiv.equivOfInverse SP SI hleft hright).trans
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm), by intro z; simp [hSP]⟩
  -- the 2-jet transfers along the affine equivalence, the direction going through `L`
  have hjet : ∀ (h : WithLp 2 (F × ℝ) → ℝ) (ζ η : WithLp 2 (F × ℝ)),
      iteratedFDeriv ℝ 2 (fun ν => h (z₀ + L ν)) ζ (fun _ => η)
        = iteratedFDeriv ℝ 2 h (z₀ + L ζ) (fun _ => L η) := by
    intro h ζ η
    have hcomp : (fun ν => h (z₀ + L ν)) = (fun Z => h (z₀ + Z)) ∘ L := by funext ν; rfl
    have hstep := L.iteratedFDerivWithin_comp_right (fun Z => h (z₀ + Z))
      (s := univ) uniqueDiffOn_univ (x := ζ) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hstep
    rw [hcomp, hstep, ContinuousMultilinearMap.compContinuousLinearMap_apply]
    simp only [ContinuousLinearEquiv.coe_coe, iteratedFDeriv_comp_add_left]
  -- an affine function has a vanishing 2-jet, which is what kills `Al` below
  have haff : ∀ (b : ℝ) (Tl : WithLp 2 (F × ℝ) →L[ℝ] ℝ) (x : WithLp 2 (F × ℝ))
      (m : Fin 2 → WithLp 2 (F × ℝ)), iteratedFDeriv ℝ 2 (fun ζ => b + Tl ζ) x m = 0 := by
    intro b Tl x m
    have hfd : fderiv ℝ (fun ζ => b + Tl ζ) = fun _ => (Tl : WithLp 2 (F × ℝ) →L[ℝ] ℝ) := by
      funext ζ; rw [fderiv_const_add]; exact Tl.fderiv
    have hD2 : fderiv ℝ (fderiv ℝ (fun ζ => b + Tl ζ)) x = 0 := by
      rw [hfd]; exact (hasFDerivAt_const (Tl : WithLp 2 (F × ℝ) →L[ℝ] ℝ) x).fderiv
    rw [iteratedFDeriv_two_apply, hD2]; simp
  -- the 2-jet is degree 2 in its direction, so a scaled direction pulls out `c ^ 2`
  have hsmul2 : ∀ (h : WithLp 2 (F × ℝ) → ℝ) (x w : WithLp 2 (F × ℝ)) (c : ℝ),
      iteratedFDeriv ℝ 2 h x (fun _ => c • w) = c ^ 2 * iteratedFDeriv ℝ 2 h x (fun _ => w) := by
    intro h x w c
    have := (iteratedFDeriv ℝ 2 h x).map_smul_univ (fun _ : Fin 2 => c) (fun _ : Fin 2 => w)
    simpa [Finset.prod_const] using this
  -- the affine part of FrameChange, as a CLM
  obtain ⟨Al, hAl⟩ : ∃ Al : WithLp 2 (F × ℝ) →L[ℝ] ℝ,
      ∀ ζ : WithLp 2 (F × ℝ),
        Al ζ = -(inner ℝ p₀ (ofLp ζ).1) - (a₀ + ‖p₀‖ ^ 2 / 2) * (ofLp ζ).2 := by
    refine ⟨-((innerSL ℝ p₀).comp ((ContinuousLinearMap.fst ℝ F ℝ).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap))
      - (a₀ + ‖p₀‖ ^ 2 / 2) • ((ContinuousLinearMap.snd ℝ F ℝ).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap), ?_⟩
    intro ζ; simp
  -- the inner-product split and the spatial-test extensionality
  have hsplit : ∀ (g : WithLp 2 (F × ℝ)) (h : F),
      (inner ℝ g (toLp 2 (h, (0:ℝ))) : ℝ) = inner ℝ (ofLp g).1 h := by
    intro g h; simp [WithLp.prod_inner_apply]
  have hext : ∀ u w : F, (∀ h : F, (inner ℝ u h : ℝ) = inner ℝ w h) → u = w := by
    intro u w hyp
    have hz : ∀ h : F, (inner ℝ (u - w) h : ℝ) = 0 := by
      intro h; rw [inner_sub_left, hyp h]; ring
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ) (x := u - w)).mp (hz (u - w)))
  -- the gradient/fderiv bridge
  have hbridge : ∀ (f : WithLp 2 (F × ℝ) → ℝ) (x w : WithLp 2 (F × ℝ)),
      fderiv ℝ f x w = inner ℝ (gradient f x) w := by
    intro f x w; rw [← toDual_gradient (f := f) (x := x)]; rfl
  -- the affine map and the chain rule through it
  have haffd : ∀ ζ : WithLp 2 (F × ℝ),
      HasFDerivAt (fun ν : WithLp 2 (F × ℝ) => z₀ + L ν)
        (L : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ)) ζ := by
    intro ζ
    simpa using ((L : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ)).hasFDerivAt).const_add z₀
  -- the first derivative of the frame-changed test, in applied form
  have hphid : ∀ (ψ : WithLp 2 (F × ℝ) → ℝ) (ζ₀ : WithLp 2 (F × ℝ)) (K : ℝ),
      DifferentiableAt ℝ ψ (z₀ + L ζ₀) → ∀ ξ : WithLp 2 (F × ℝ),
      fderiv ℝ (fun ζ => (ψ (z₀ + L ζ) - K) / R + Al ζ) ζ₀ ξ
        = R⁻¹ * fderiv ℝ ψ (z₀ + L ζ₀) (L ξ) + Al ξ := by
    intro ψ ζ₀ K hψ ξ
    simp only [div_eq_mul_inv]
    have h1 : HasFDerivAt (fun ν => ψ (z₀ + L ν))
        ((fderiv ℝ ψ (z₀ + L ζ₀)).comp
          (L : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ))) ζ₀ :=
      (hψ.hasFDerivAt).comp ζ₀ (haffd ζ₀)
    have h1b : HasFDerivAt (fun ν => ψ (z₀ + L ν) - K)
        ((fderiv ℝ ψ (z₀ + L ζ₀)).comp
          (L : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ))) ζ₀ := h1.sub_const K
    have h2 : HasFDerivAt (fun ζ => (ψ (z₀ + L ζ) - K) * R⁻¹ + Al ζ)
        (R⁻¹ • ((fderiv ℝ ψ (z₀ + L ζ₀)).comp
          (L : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ))) + Al) ζ₀ :=
      (HasFDerivAt.mul_const h1b R⁻¹).add (Al.hasFDerivAt (x := ζ₀))
    rw [h2.fderiv]
    simp
  -- eq:fi-grad : the spatial gradient of the frame-changed test is the old one minus p₀
  have hgrad : ∀ (ψ : WithLp 2 (F × ℝ) → ℝ) (ζ₀ : WithLp 2 (F × ℝ)) (K : ℝ),
      DifferentiableAt ℝ ψ (z₀ + L ζ₀) →
      (ofLp (gradient (fun ζ => (ψ (z₀ + L ζ) - K) / R + Al ζ) ζ₀)).1
        = (ofLp (gradient ψ (z₀ + L ζ₀))).1 - p₀ := by
    intro ψ ζ₀ K hψ
    refine hext _ _ fun h => ?_
    have hsm : (toLp 2 (R • h, (0:ℝ)) : WithLp 2 (F × ℝ)) = R • toLp 2 (h, (0:ℝ)) := by
      have h0 : (R • (toLp 2 (h, (0:ℝ)) : WithLp 2 (F × ℝ)))
          = toLp 2 (R • h, R • (0:ℝ)) := rfl
      rw [h0, smul_zero]
    have hstep : L (toLp 2 (h, (0:ℝ))) = R • toLp 2 (h, (0:ℝ)) := by
      rw [hL]; simp only [zero_smul, add_zero, mul_zero]
      exact hsm
    rw [← hsplit, ← hbridge, hphid ψ ζ₀ K hψ, hstep, map_smul, hAl,
      inner_sub_left, ← hsplit, ← hbridge]
    simp only [smul_eq_mul, mul_zero, sub_zero]
    rw [← mul_assoc, inv_mul_cancel₀ hRne, one_mul]
    ring
  -- eq:fi-Fscale : LimitOp of the frame-changed test, the mathematical core
  have hop : ∀ (ψ : WithLp 2 (F × ℝ) → ℝ) (ζ₀ : WithLp 2 (F × ℝ)) (K : ℝ),
      ContDiffAt ℝ 2 ψ (z₀ + L ζ₀) →
      LimitOp (fun ζ => (ψ (z₀ + L ζ) - K) / R + Al ζ) ζ₀
        = R * LimitOp ψ (z₀ + L ζ₀) := by
    intro ψ ζ₀ K hψ
    have hψd : DifferentiableAt ℝ ψ (z₀ + L ζ₀) := hψ.differentiableAt (by norm_num)
    have haffC : ContDiffAt ℝ 2 (fun ζ : WithLp 2 (F × ℝ) => z₀ + L ζ) ζ₀ := by fun_prop
    have hcomp : ContDiffAt ℝ 2 (fun ζ => R⁻¹ • ψ (z₀ + L ζ)) ζ₀ :=
      (hψ.comp ζ₀ haffC).const_smul R⁻¹
    have hcomp0 : ContDiffAt ℝ 2 (fun ζ => ψ (z₀ + L ζ)) ζ₀ := hψ.comp ζ₀ haffC
    have hA : ContDiffAt ℝ 2 (fun ζ : WithLp 2 (F × ℝ) => -(K / R) + Al ζ) ζ₀ := by
      fun_prop
    have hfeq : (fun ζ : WithLp 2 (F × ℝ) => (ψ (z₀ + L ζ) - K) / R + Al ζ)
        = (fun ζ => R⁻¹ • ψ (z₀ + L ζ) + (-(K / R) + Al ζ)) := by
      funext ζ; simp only [smul_eq_mul]; ring
    rw [LimitOp, LimitOp, hgrad ψ ζ₀ K hψd]
    -- the shear sends the corrected direction back to the straight one, scaled by R
    have hdir : L (toLp 2 ((ofLp (gradient ψ (z₀ + L ζ₀))).1 - p₀, (1:ℝ)))
        = R • toLp 2 ((ofLp (gradient ψ (z₀ + L ζ₀))).1, (1:ℝ)) := by
      rw [hL]
      have h0 : (R • (toLp 2 ((ofLp (gradient ψ (z₀ + L ζ₀))).1, (1:ℝ))
            : WithLp 2 (F × ℝ)))
          = toLp 2 (R • (ofLp (gradient ψ (z₀ + L ζ₀))).1, R • (1:ℝ)) := rfl
      rw [h0]
      simp
    rw [hfeq, fun_iteratedFDeriv_add_apply hcomp hA, add_apply, haff, add_zero,
      iteratedFDeriv_const_smul_apply' hcomp0]
    simp only [smul_apply, smul_eq_mul]
    -- `R⁻¹` from the frame change, `R ^ 2` from the sheared direction: net `R`
    rw [hjet, hdir, hsmul2]
    field_simp
  -- ------------------------------------------------------------------
  -- the frame change, written against `L` and `Al`
  have hwval : ∀ ζ : WithLp 2 (F × ℝ),
      FrameChange v z₀ R p₀ a₀ ζ = (v (z₀ + L ζ) - v z₀) / R + Al ζ := by
    intro ζ
    simp only [FrameChange]
    rw [← hL ζ, hAl ζ]
    ring
  -- the shear moves the box corner by the same shear
  have hcent : ∀ (ζ : WithLp 2 (F × ℝ)) (h : F) (l : ℝ),
      z₀ + L (ζ + toLp 2 (h, l)) = (z₀ + L ζ) + toLp 2 (R • (h + l • p₀), R * l) := by
    intro ζ h l
    have hstep : L (ζ + toLp 2 (h, l)) = L ζ + toLp 2 (R • (h + l • p₀), R * l) := by
      rw [map_add, hL (toLp 2 (h, l))]
    rw [hstep]
    abel
  -- ------------------------------------------------------------------
  -- STEP 2 : the fit transformation, (4.4)-(4.5) of the paper
  have hfit : ∀ (ζ : WithLp 2 (F × ℝ)) (ρ : ℝ) (p : F) (a : ℝ),
      IsFit C₀ v (z₀ + L ζ) (R * ρ) p a →
      IsFit C₀ (FrameChange v z₀ R p₀ a₀) ζ ρ (p - p₀) (a - a₀) := by
    intro ζ ρ p a hf h l hl hhl
    have hb1 : |R * l| ≤ R * ρ := by
      rw [abs_mul, abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left hl (le_of_lt hR)
    have hsh : R • (h + l • p₀) - (R * l) • p = R • (h - l • (p - p₀)) := by
      module
    have hb2 : ‖R • (h + l • p₀) - (R * l) • p‖ ≤ R * ρ := by
      rw [hsh, norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      exact mul_le_mul_of_nonneg_left hhl (le_of_lt hR)
    have hkey := hf (R • (h + l • p₀)) (R * l) hb1 hb2
    rw [← hcent ζ h l] at hkey
    -- the two deviations differ by exactly the factor `R`
    have hexp : FrameChange v z₀ R p₀ a₀ (ζ + toLp 2 (h, l))
          - FrameChange v z₀ R p₀ a₀ ζ - inner ℝ (p - p₀) h
          - (a - a₀ - ‖p - p₀‖ ^ 2 / 2) * l
        = (v (z₀ + L (ζ + toLp 2 (h, l))) - v (z₀ + L ζ)
            - inner ℝ p (R • (h + l • p₀)) - (a - ‖p‖ ^ 2 / 2) * (R * l)) / R := by
      rw [hwval (ζ + toLp 2 (h, l)), hwval ζ, hAl (ζ + toLp 2 (h, l)), hAl ζ,
        inner_sub_left, norm_sub_sq_real, real_inner_smul_right, inner_add_right,
        real_inner_smul_right]
      simp only [WithLp.ofLp_add, Prod.fst_add, Prod.snd_add, inner_add_right]
      field_simp
      ring
    rw [hexp, abs_div, abs_of_pos hR, div_le_iff₀ hR]
    calc |v (z₀ + L (ζ + toLp 2 (h, l))) - v (z₀ + L ζ)
            - inner ℝ p (R • (h + l • p₀)) - (a - ‖p‖ ^ 2 / 2) * (R * l)|
        ≤ C₀ * (R * ρ) := hkey
      _ = C₀ * ρ * R := by ring
  -- ------------------------------------------------------------------
  -- STEP 1 : the frame change is again a limit solution, on all of space-time
  have hvc : Continuous v := continuousOn_univ.mp hv.1.1.2.1
  have hwc : Continuous (FrameChange v z₀ R p₀ a₀) := by
    have h1 : Continuous fun ζ : WithLp 2 (F × ℝ) => z₀ + L ζ := by fun_prop
    have h3 : Continuous fun ζ : WithLp 2 (F × ℝ) =>
        (v (z₀ + L ζ) - v z₀) / R + Al ζ :=
      (((hvc.comp h1).sub continuous_const).div_const R).add Al.continuous
    exact h3.congr fun ζ => (hwval ζ).symm
  -- the test function for `v` produced from a test function for the frame change
  -- Given a test `φ` touching the frame change at `ζ₀`, this is the test for `v`
  -- at `z₀ + L ζ₀` whose own frame change is `φ` ITSELF, so `hop` applies verbatim
  -- and no second, inverse computation of `LimitOp` is needed.
  have hpull : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (ζ₀ : WithLp 2 (F × ℝ)),
      ContDiffAt ℝ 2 φ ζ₀ →
      ∃ ψ : WithLp 2 (F × ℝ) → ℝ, ContDiffAt ℝ 2 ψ (z₀ + L ζ₀) ∧
        LimitOp φ ζ₀ = R * LimitOp ψ (z₀ + L ζ₀) ∧
        ∀ Z : WithLp 2 (F × ℝ), v Z - ψ Z
          = R * (FrameChange v z₀ R p₀ a₀ (L.symm (Z - z₀)) - φ (L.symm (Z - z₀))) := by
    intro φ ζ₀ hφ
    have hTζ : L.symm (z₀ + L ζ₀ - z₀) = ζ₀ := by simp
    refine ⟨fun Z => R * (φ (L.symm (Z - z₀)) - Al (L.symm (Z - z₀))) + v z₀, ?_, ?_, ?_⟩
    · have hT : ContDiffAt ℝ 2
          (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) (z₀ + L ζ₀) := by fun_prop
      have hφ' : ContDiffAt ℝ 2 φ (L.symm (z₀ + L ζ₀ - z₀)) := by rw [hTζ]; exact hφ
      have hcφ : ContDiffAt ℝ 2 (fun Z => φ (L.symm (Z - z₀))) (z₀ + L ζ₀) :=
        hφ'.comp (z₀ + L ζ₀) hT
      have hcA : ContDiffAt ℝ 2
          (fun Z : WithLp 2 (F × ℝ) => Al (L.symm (Z - z₀))) (z₀ + L ζ₀) :=
        (Al.contDiff.contDiffAt).comp (z₀ + L ζ₀) hT
      exact ((hcφ.sub hcA).const_smul R).add contDiffAt_const
    · -- the frame change of this `ψ` is `φ` itself, so `hop` applies verbatim
      have hψv : ∀ ζ : WithLp 2 (F × ℝ),
          R * (φ (L.symm (z₀ + L ζ - z₀)) - Al (L.symm (z₀ + L ζ - z₀))) + v z₀
            = R * (φ ζ - Al ζ) + v z₀ := by
        intro ζ; rw [show L.symm (z₀ + L ζ - z₀) = ζ by simp]
      have hφeq : (fun ζ => (R * (φ (L.symm (z₀ + L ζ - z₀))
            - Al (L.symm (z₀ + L ζ - z₀))) + v z₀ - v z₀) / R + Al ζ) = φ := by
        funext ζ
        rw [hψv ζ]
        field_simp
        ring
      have hid := hop (fun Z => R * (φ (L.symm (Z - z₀)) - Al (L.symm (Z - z₀))) + v z₀)
        ζ₀ (v z₀) ?_
      · rw [hφeq] at hid
        exact hid
      · have hT : ContDiffAt ℝ 2
            (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) (z₀ + L ζ₀) := by fun_prop
        have hφ' : ContDiffAt ℝ 2 φ (L.symm (z₀ + L ζ₀ - z₀)) := by rw [hTζ]; exact hφ
        exact (((hφ'.comp (z₀ + L ζ₀) hT).sub
          ((Al.contDiff.contDiffAt).comp (z₀ + L ζ₀) hT)).const_smul R).add contDiffAt_const
    · intro Z
      rw [hwval (L.symm (Z - z₀)), show z₀ + L (L.symm (Z - z₀)) = Z by simp]
      field_simp
      ring
  -- the local extremum transfers along the affine homeomorphism, both signs
  have htrans : ∀ (g : WithLp 2 (F × ℝ) → ℝ) (G : WithLp 2 (F × ℝ) → ℝ)
      (ζ₀ : WithLp 2 (F × ℝ)),
      (∀ Z : WithLp 2 (F × ℝ), G Z = R * g (L.symm (Z - z₀))) →
      Filter.Tendsto (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀))
        (nhds (z₀ + L ζ₀)) (nhds ζ₀) := by
    intro g G ζ₀ _
    have h1 : ContinuousAt (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) (z₀ + L ζ₀) := by
      fun_prop
    rw [ContinuousAt, show L.symm (z₀ + L ζ₀ - z₀) = ζ₀ by simp] at h1
    exact h1
  refine ⟨⟨⟨⟨isOpen_univ, hwc.continuousOn, ?_⟩, ⟨isOpen_univ, hwc.continuousOn, ?_⟩⟩, ?_⟩, ?_⟩
  · -- subsolution
    intro ζ₀ _ φ hφ hmax
    obtain ⟨ψ, hψC, hid, hrel⟩ := hpull φ ζ₀ hφ
    have hmax0 : ∀ᶠ ν in nhdsWithin ζ₀ Set.univ,
        FrameChange v z₀ R p₀ a₀ ν - φ ν
          ≤ FrameChange v z₀ R p₀ a₀ ζ₀ - φ ζ₀ := hmax
    rw [nhdsWithin_univ] at hmax0
    have hTt := htrans (fun ν => FrameChange v z₀ R p₀ a₀ ν - φ ν)
      (fun Z => v Z - ψ Z) ζ₀ hrel
    have hev := hTt.eventually hmax0
    have hmax' : IsLocalMaxOn (fun Z => v Z - ψ Z) Set.univ (z₀ + L ζ₀) := by
      show ∀ᶠ Z in nhdsWithin (z₀ + L ζ₀) Set.univ,
        v Z - ψ Z ≤ v (z₀ + L ζ₀) - ψ (z₀ + L ζ₀)
      rw [nhdsWithin_univ]
      filter_upwards [hev] with Z hZ
      rw [hrel Z, hrel (z₀ + L ζ₀), show L.symm (z₀ + L ζ₀ - z₀) = ζ₀ by simp]
      exact mul_le_mul_of_nonneg_left hZ (le_of_lt hR)
    rw [hid]
    exact mul_nonneg (le_of_lt hR) (hv.1.1.2.2 (z₀ + L ζ₀) (Set.mem_univ _) ψ hψC hmax')
  · -- supersolution
    intro ζ₀ _ φ hφ hmin
    obtain ⟨ψ, hψC, hid, hrel⟩ := hpull φ ζ₀ hφ
    have hmin0 : ∀ᶠ ν in nhdsWithin ζ₀ Set.univ,
        FrameChange v z₀ R p₀ a₀ ζ₀ - φ ζ₀
          ≤ FrameChange v z₀ R p₀ a₀ ν - φ ν := hmin
    rw [nhdsWithin_univ] at hmin0
    have hTt := htrans (fun ν => FrameChange v z₀ R p₀ a₀ ν - φ ν)
      (fun Z => v Z - ψ Z) ζ₀ hrel
    have hev := hTt.eventually hmin0
    have hmin' : IsLocalMinOn (fun Z => v Z - ψ Z) Set.univ (z₀ + L ζ₀) := by
      show ∀ᶠ Z in nhdsWithin (z₀ + L ζ₀) Set.univ,
        v (z₀ + L ζ₀) - ψ (z₀ + L ζ₀) ≤ v Z - ψ Z
      rw [nhdsWithin_univ]
      filter_upwards [hev] with Z hZ
      rw [hrel Z, hrel (z₀ + L ζ₀), show L.symm (z₀ + L ζ₀ - z₀) = ζ₀ by simp]
      exact mul_le_mul_of_nonneg_left hZ (le_of_lt hR)
    rw [hid]
    have := hv.1.2.2.2 (z₀ + L ζ₀) (Set.mem_univ _) ψ hψC hmin'
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hR) this
  · -- STEP 3 : every centre and radius still admits a fit
    intro ζ ρ hρ
    obtain ⟨p, a, hf⟩ := hv.2 (z₀ + L ζ) (R * ρ) (mul_pos hR hρ)
    exact ⟨p - p₀, a - a₀, hfit ζ ρ p a hf⟩
  · -- the second conjunct of the statement is Step 2, with the centre rewritten
    intro ζ ρ p a hf
    refine hfit ζ ρ p a ?_
    rw [hL ζ]
    exact hf
