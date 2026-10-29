import InfHarmonic.IsInfHarmonicOn
import InfHarmonic.IsRescaledSolutionOn
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equations (3.6)--(3.7): the anisotropic rescaling of an infinity-harmonic
function solves `D²v[(∇_x v, 1 + λ v_t)] = 0` in the viscosity sense. -/
theorem RescaledEquation (Ω : Set (WithLp 2 (F × ℝ))) (U : WithLp 2 (F × ℝ) → ℝ)
    (hU : IsInfHarmonicOn Ω U) (z₀ : WithLp 2 (F × ℝ)) (r c lam : ℝ)
    (hr : 0 < r) (hc : 0 < c) (hlam : 0 < lam)
    (Φ : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ)) (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : ∀ z : WithLp 2 (F × ℝ),
      U (z₀ + r • Φ (toLp 2 (Real.sqrt lam • (ofLp z).1, (ofLp z).2)))
        = U z₀ + r * c * ((ofLp z).2 + lam * v z)) :
    IsRescaledSolutionOn lam
      ((fun z : WithLp 2 (F × ℝ) =>
        z₀ + r • Φ (toLp 2 (Real.sqrt lam • (ofLp z).1, (ofLp z).2))) ⁻¹' Ω) v := by
  obtain ⟨⟨hΩ, hcU, hsub⟩, ⟨-, -, hsup⟩⟩ := hU
  have hrne : r ≠ 0 := ne_of_gt hr
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hcne : c ≠ 0 := ne_of_gt hc
  have hane : Real.sqrt lam ≠ 0 := by positivity
  -- Step 0a: the anisotropic stretch `S` and its inverse, as continuous linear maps.
  obtain ⟨S, hS⟩ : ∃ S : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ),
      ∀ z : WithLp 2 (F × ℝ), S z = toLp 2 (Real.sqrt lam • (ofLp z).1, (ofLp z).2) :=
    ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
      (((Real.sqrt lam • ContinuousLinearMap.id ℝ F).prodMap
        (ContinuousLinearMap.id ℝ ℝ)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap), fun _ => rfl⟩
  obtain ⟨Si, hSi⟩ : ∃ Si : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ),
      ∀ z : WithLp 2 (F × ℝ), Si z = toLp 2 ((Real.sqrt lam)⁻¹ • (ofLp z).1, (ofLp z).2) :=
    ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
      ((((Real.sqrt lam)⁻¹ • ContinuousLinearMap.id ℝ F).prodMap
        (ContinuousLinearMap.id ℝ ℝ)).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap), fun _ => rfl⟩
  have hSiS : ∀ z : WithLp 2 (F × ℝ), Si (S z) = z := by
    intro z; rw [hS, hSi]; simp only [smul_smul, inv_mul_cancel₀ hane, one_smul]
  have hSSi : ∀ z : WithLp 2 (F × ℝ), S (Si z) = z := by
    intro z; rw [hSi, hS]; simp only [smul_smul, mul_inv_cancel₀ hane, one_smul]
  -- Step 0b: `L = r • (Φ ∘ S)` is a linear homeomorphism of space-time.
  have hLc : ∀ z : WithLp 2 (F × ℝ),
      (r • ((Φ.toContinuousLinearEquiv.toContinuousLinearMap).comp S)) z = r • Φ (S z) := by
    intro z; simp
  have hMc : ∀ z : WithLp 2 (F × ℝ),
      (r⁻¹ • (Si.comp (Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap))) z
        = r⁻¹ • Si (Φ.symm z) := by
    intro z; simp
  have h1 : ∀ z, (r⁻¹ • (Si.comp (Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap)))
      ((r • ((Φ.toContinuousLinearEquiv.toContinuousLinearMap).comp S)) z) = z := by
    intro z
    rw [hLc, hMc, map_smul, Φ.symm_apply_apply, map_smul, smul_smul, inv_mul_cancel₀ hrne,
      one_smul, hSiS]
  have h2 : ∀ z, (r • ((Φ.toContinuousLinearEquiv.toContinuousLinearMap).comp S))
      ((r⁻¹ • (Si.comp (Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap))) z) = z := by
    intro z
    rw [hLc, hMc, map_smul, map_smul, smul_smul, mul_inv_cancel₀ hrne, one_smul, hSSi,
      Φ.apply_symm_apply]
  set L : WithLp 2 (F × ℝ) ≃L[ℝ] WithLp 2 (F × ℝ) :=
    ContinuousLinearEquiv.equivOfInverse
      (r • ((Φ.toContinuousLinearEquiv.toContinuousLinearMap).comp S))
      (r⁻¹ • (Si.comp (Φ.symm.toContinuousLinearEquiv.toContinuousLinearMap))) h1 h2 with hLdef
  have hLapp : ∀ z, L z = r • Φ (S z) := by intro z; rw [hLdef]; exact hLc z
  -- the frame map of the statement is `z ↦ z₀ + L z`
  have hfun : (fun z : WithLp 2 (F × ℝ) =>
      z₀ + r • Φ (toLp 2 (Real.sqrt lam • (ofLp z).1, (ofLp z).2)))
      = (fun z : WithLp 2 (F × ℝ) => z₀ + L z) := by
    funext z; rw [hLapp, hS]
  rw [hfun]
  have hvL : ∀ z : WithLp 2 (F × ℝ),
      U (z₀ + L z) = U z₀ + r * c * ((ofLp z).2 + lam * v z) := by
    intro z; rw [hLapp, hS]; exact hv z
  -- Step 0c: `T⁻¹(Ω)` is open and `v` is continuous on it.
  have hTcont : Continuous (fun z : WithLp 2 (F × ℝ) => z₀ + L z) := by fun_prop
  have hopen : IsOpen ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) := hΩ.preimage hTcont
  have hinvT : ∀ z : WithLp 2 (F × ℝ), L.symm (z₀ + L z - z₀) = z := by
    intro z; rw [add_sub_cancel_left, L.symm_apply_apply]
  have hvformula : ∀ z : WithLp 2 (F × ℝ),
      v z = ((U (z₀ + L z) - U z₀) / (r * c) - (ofLp z).2) / lam := by
    intro z
    have h := hvL z
    field_simp
    linarith [h]
  have hvcont : ContinuousOn v ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) := by
    have hUT : ContinuousOn (fun z : WithLp 2 (F × ℝ) => U (z₀ + L z))
        ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) :=
      hcU.comp hTcont.continuousOn (Set.mapsTo_preimage _ _)
    have hsnd : ContinuousOn (fun z : WithLp 2 (F × ℝ) => (ofLp z).2)
        ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) := by fun_prop
    have : ContinuousOn
        (fun z : WithLp 2 (F × ℝ) => ((U (z₀ + L z) - U z₀) / (r * c) - (ofLp z).2) / lam)
        ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) := by
      exact (((hUT.sub continuousOn_const).div_const _).sub hsnd).div_const _
    exact this.congr fun z _ => hvformula z
  -- Step 1: adjoint identities.  `S` is self-adjoint and `Φ` preserves the inner product,
  -- so `⟪L u, L w⟫ = r² ⟪S u, S w⟫`.
  have hsa : ∀ u w : WithLp 2 (F × ℝ), (inner ℝ (S u) w : ℝ) = inner ℝ u (S w) := by
    intro u w
    simp only [hS, WithLp.prod_inner_apply, real_inner_smul_left, real_inner_smul_right,
      RCLike.inner_apply, starRingEnd_apply, star_trivial]
  have hLinner : ∀ u w : WithLp 2 (F × ℝ),
      (inner ℝ (L u) (L w) : ℝ) = r ^ 2 * inner ℝ (S u) (S w) := by
    intro u w
    rw [hLapp, hLapp, real_inner_smul_left, real_inner_smul_right, Φ.inner_map_map]
    ring
  have hSS : ∀ z : WithLp 2 (F × ℝ), S (S z) = toLp 2 (lam • (ofLp z).1, (ofLp z).2) := by
    intro z; rw [hS, hS]; simp only [smul_smul, Real.mul_self_sqrt hlam.le]
  -- the key inner-product identity: `⟪L ((c/r) • w), L b⟫ = ⟪(rc) • S² w, b⟫`
  have hkeyinner : ∀ w b : WithLp 2 (F × ℝ),
      (inner ℝ (L ((c / r) • w)) (L b) : ℝ)
        = inner ℝ ((r * c) • toLp 2 (lam • (ofLp w).1, (ofLp w).2)) b := by
    intro w b
    calc (inner ℝ (L ((c / r) • w)) (L b) : ℝ)
        = r ^ 2 * inner ℝ (S ((c / r) • w)) (S b) := hLinner _ _
      _ = r ^ 2 * ((c / r) * inner ℝ (S w) (S b)) := by rw [map_smul, real_inner_smul_left]
      _ = r ^ 2 * ((c / r) * inner ℝ (S (S w)) b) := by rw [← hsa]
      _ = r * c * inner ℝ (toLp 2 (lam • (ofLp w).1, (ofLp w).2)) b := by
          rw [hSS]; field_simp
      _ = inner ℝ ((r * c) • toLp 2 (lam • (ofLp w).1, (ofLp w).2)) b := by
          rw [real_inner_smul_left]
  -- Step 2 preliminaries: the jet transfer along the affine equivalence, and the fact
  -- that an affine function has vanishing second derivative.
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
  have haff : ∀ (b : ℝ) (Tl : WithLp 2 (F × ℝ) →L[ℝ] ℝ) (x : WithLp 2 (F × ℝ))
      (m : Fin 2 → WithLp 2 (F × ℝ)), iteratedFDeriv ℝ 2 (fun ζ => b + Tl ζ) x m = 0 := by
    intro b Tl x m
    have hfd : fderiv ℝ (fun ζ => b + Tl ζ) = fun _ => (Tl : WithLp 2 (F × ℝ) →L[ℝ] ℝ) := by
      funext ζ; rw [fderiv_const_add]; exact Tl.fderiv
    have hone : iteratedFDeriv ℝ 1 (fun ζ => b + Tl ζ)
        = fun _ : WithLp 2 (F × ℝ) => iteratedFDeriv ℝ 1 (fun ζ => b + Tl ζ) x := by
      funext y
      ext mm
      rw [iteratedFDeriv_one_apply, iteratedFDeriv_one_apply]
      simp only [hfd]
    rw [iteratedFDeriv_succ_apply_left, hone, fderiv_fun_const]
    simp
  obtain ⟨pit, hpit⟩ : ∃ pit : WithLp 2 (F × ℝ) →L[ℝ] ℝ,
      ∀ z : WithLp 2 (F × ℝ), pit z = (ofLp z).2 :=
    ⟨(ContinuousLinearMap.snd ℝ F ℝ).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap, fun _ => rfl⟩
  -- Step 3: the conversion factor.  For a `C²` test `φ` at `ζ`, the transferred test
  -- `Ψ` satisfies `Δ_∞ Ψ (T ζ) = (λ c³ / r) · F_λ[φ](ζ)`.
  have hfactor : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (ζ : WithLp 2 (F × ℝ)), ContDiffAt ℝ 2 φ ζ →
      InfLap (fun Z : WithLp 2 (F × ℝ) => U z₀ + r * c * ((ofLp (L.symm (Z - z₀))).2
          + lam * φ (L.symm (Z - z₀)))) (z₀ + L ζ)
        = lam * c ^ 3 / r * RescaledOp lam φ ζ := by
    intro φ ζ hφ
    have hdiff : DifferentiableAt ℝ φ ζ := hφ.differentiableAt (by norm_num)
    set w : WithLp 2 (F × ℝ) :=
      toLp 2 ((ofLp (gradient φ ζ)).1, 1 + lam * (ofLp (gradient φ ζ)).2) with hwdef
    set g : WithLp 2 (F × ℝ) → ℝ :=
      fun ν => U z₀ + r * c * ((ofLp ν).2 + lam * φ ν) with hgdef
    set Ψ : WithLp 2 (F × ℝ) → ℝ :=
      fun Z => U z₀ + r * c * ((ofLp (L.symm (Z - z₀))).2 + lam * φ (L.symm (Z - z₀)))
      with hΨdef
    have hΨfun : (fun ν : WithLp 2 (F × ℝ) => Ψ (z₀ + L ν)) = g := by
      funext ν; rw [hΨdef, hgdef]; simp only [hinvT]
    -- the differential of `g`, in Riesz form
    have hpitd : HasFDerivAt (fun ν : WithLp 2 (F × ℝ) => (ofLp ν).2) pit ζ := by
      have h : (fun ν : WithLp 2 (F × ℝ) => (ofLp ν).2) = pit := by funext ν; rw [hpit]
      rw [h]; exact pit.hasFDerivAt
    have hφd : HasFDerivAt (fun ν : WithLp 2 (F × ℝ) => lam * φ ν) (lam • fderiv ℝ φ ζ) ζ :=
      hdiff.hasFDerivAt.const_mul lam
    have h1 : HasFDerivAt (fun ν : WithLp 2 (F × ℝ) => (ofLp ν).2 + lam * φ ν)
        (pit + lam • fderiv ℝ φ ζ) ζ := hpitd.add hφd
    have hgd : HasFDerivAt g ((r * c) • (pit + lam • fderiv ℝ φ ζ)) ζ :=
      ((h1.const_mul (r * c)).const_add (U z₀))
    have hfdg : ∀ η : WithLp 2 (F × ℝ), fderiv ℝ g ζ η
        = inner ℝ ((r * c) • toLp 2 (lam • (ofLp w).1, (ofLp w).2)) η := by
      intro η
      rw [hgd.fderiv, real_inner_smul_left, hwdef]
      simp only [FunLike.coe_smul, Pi.smul_apply, add_apply, smul_eq_mul, hpit,
        ← inner_gradient_left (𝕜 := ℝ), WithLp.prod_inner_apply,
        real_inner_smul_left, RCLike.inner_apply, starRingEnd_apply, star_trivial]
      ring
    -- the gradient of the transferred test: `∇Ψ(Tζ) = L ((c/r) • w)`
    have hTinvd : HasFDerivAt (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀))
        (L.symm : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ)) (z₀ + L ζ) := by
      have hd : HasFDerivAt (fun Z : WithLp 2 (F × ℝ) => Z - z₀)
          (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))) (z₀ + L ζ) :=
        (hasFDerivAt_id _).sub_const z₀
      have hcomp :=
        (L.symm : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ)).hasFDerivAt.comp (z₀ + L ζ) hd
      rw [ContinuousLinearMap.comp_id] at hcomp
      exact hcomp
    have hgdζ : HasFDerivAt g (fderiv ℝ g ζ)
        ((fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) (z₀ + L ζ)) := by
      show HasFDerivAt g (fderiv ℝ g ζ) (L.symm (z₀ + L ζ - z₀))
      rw [hinvT]; exact hgd.differentiableAt.hasFDerivAt
    have hΨeq : Ψ = g ∘ (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) := by
      rw [hΨdef, hgdef]; rfl
    have hΨd : HasFDerivAt Ψ
        ((fderiv ℝ g ζ).comp (L.symm : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ))) (z₀ + L ζ) := by
      rw [hΨeq]; exact hgdζ.comp (z₀ + L ζ) hTinvd
    have hDeq : (fderiv ℝ g ζ).comp (L.symm : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ))
        = (InnerProductSpace.toDual ℝ (WithLp 2 (F × ℝ))) (L ((c / r) • w)) := by
      ext ξ
      simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
        ContinuousLinearEquiv.coe_coe]
      rw [hfdg, ← hkeyinner w (L.symm ξ), L.apply_symm_apply]
    have hgradΨ : gradient Ψ (z₀ + L ζ) = L ((c / r) • w) := by
      refine HasGradientAt.gradient ?_
      rw [hasGradientAt_iff_hasFDerivAt, ← hDeq]
      exact hΨd
    -- the second derivative of `g` is `rcλ` times that of `φ`
    have hgsplit : g = (fun ν : WithLp 2 (F × ℝ) => U z₀ + ((r * c) • pit) ν)
        + ((r * c * lam) • φ) := by
      funext ν
      simp only [hgdef, Pi.add_apply, Pi.smul_apply, FunLike.coe_smul, smul_eq_mul, hpit]
      ring
    have hcd1 : ContDiffAt ℝ 2 (fun ν : WithLp 2 (F × ℝ) => U z₀ + ((r * c) • pit) ν) ζ := by
      fun_prop
    have hcd2 : ContDiffAt ℝ 2 ((r * c * lam) • φ) ζ := hφ.const_smul (r * c * lam)
    have hg2 : ∀ η : WithLp 2 (F × ℝ), iteratedFDeriv ℝ 2 g ζ (fun _ => η)
        = r * c * lam * iteratedFDeriv ℝ 2 φ ζ (fun _ => η) := by
      intro η
      rw [hgsplit, iteratedFDeriv_add_apply hcd1 hcd2, iteratedFDeriv_const_smul_apply hφ]
      rw [add_apply, haff (U z₀) ((r * c) • pit) ζ (fun _ => η)]
      simp only [smul_apply, smul_eq_mul]
      ring
    -- assemble: the factor is `λ c³ / r`
    have hsm : iteratedFDeriv ℝ 2 φ ζ (fun _ => (c / r) • w)
        = c ^ 2 / r ^ 2 * iteratedFDeriv ℝ 2 φ ζ (fun _ => w) := by
      simpa using (iteratedFDeriv ℝ 2 φ ζ).map_smul_univ (fun _ : Fin 2 => c / r)
        (fun _ : Fin 2 => w)
    rw [InfLap, hgradΨ, ← hjet Ψ ζ ((c / r) • w), hΨfun, hg2, hsm, RescaledOp, ← hwdef]
    field_simp
  -- Step 2: the transferred test is `C²`, and `U - Ψ` is a positive multiple of
  -- `(v - φ) ∘ T⁻¹`, so local maxima and minima correspond.
  have hZeq : ∀ Z : WithLp 2 (F × ℝ), z₀ + L (L.symm (Z - z₀)) = Z := by
    intro Z; rw [L.apply_symm_apply]; abel
  have hΨcd : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (ζ : WithLp 2 (F × ℝ)), ContDiffAt ℝ 2 φ ζ →
      ContDiffAt ℝ 2 (fun Z : WithLp 2 (F × ℝ) => U z₀ + r * c * ((ofLp (L.symm (Z - z₀))).2
        + lam * φ (L.symm (Z - z₀)))) (z₀ + L ζ) := by
    intro φ ζ hφ
    have hmap : ContDiffAt ℝ 2 (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) (z₀ + L ζ) := by
      fun_prop
    have hφ' : ContDiffAt ℝ 2 φ ((fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) (z₀ + L ζ)) := by
      show ContDiffAt ℝ 2 φ (L.symm (z₀ + L ζ - z₀))
      rw [hinvT]; exact hφ
    have hcomp : ContDiffAt ℝ 2 (fun Z : WithLp 2 (F × ℝ) => φ (L.symm (Z - z₀))) (z₀ + L ζ) :=
      hφ'.comp (z₀ + L ζ) hmap
    have hsnd : ContDiffAt ℝ 2 (fun Z : WithLp 2 (F × ℝ) => (ofLp (L.symm (Z - z₀))).2)
        (z₀ + L ζ) := by
      have hpf : (fun Z : WithLp 2 (F × ℝ) => (ofLp (L.symm (Z - z₀))).2)
          = fun Z : WithLp 2 (F × ℝ) => pit (L.symm (Z - z₀)) := by funext Z; rw [hpit]
      rw [hpf]
      exact pit.contDiff.contDiffAt.comp (z₀ + L ζ) hmap
    exact contDiffAt_const.add ((hsnd.add (hcomp.const_smul lam)).const_smul (r * c))
  have hdiffid : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (Z : WithLp 2 (F × ℝ)),
      U Z - (U z₀ + r * c * ((ofLp (L.symm (Z - z₀))).2 + lam * φ (L.symm (Z - z₀))))
        = r * c * lam * (v (L.symm (Z - z₀)) - φ (L.symm (Z - z₀))) := by
    intro φ Z
    have h := hvL (L.symm (Z - z₀))
    rw [hZeq] at h
    rw [h]; ring
  have hrcl : (0 : ℝ) < r * c * lam := by positivity
  refine ⟨hopen, hvcont, ?_, ?_⟩
  · -- upper tests: `Ψ` is a `C²` upper test for `U` at `T ζ`
    intro ζ hζ φ hφ hmax
    have hζΩ : z₀ + L ζ ∈ Ω := hζ
    have hmax' : IsLocalMaxOn (fun Z : WithLp 2 (F × ℝ) => U Z
        - (U z₀ + r * c * ((ofLp (L.symm (Z - z₀))).2
          + lam * φ (L.symm (Z - z₀))))) Ω (z₀ + L ζ) := by
      have htr : ContinuousWithinAt (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) Ω
          (z₀ + L ζ) := by fun_prop
      have hmaps : Set.MapsTo (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) Ω
          ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) := by
        intro Z hZ; simpa [hZeq Z] using hZ
      have htend := htr.tendsto_nhdsWithin hmaps
      simp only [hinvT] at htend
      refine Filter.Eventually.mono (htend.eventually hmax) fun Z hZ => ?_
      have hZ' : v (L.symm (Z - z₀)) - φ (L.symm (Z - z₀)) ≤ v ζ - φ ζ := hZ
      simp only [hdiffid]
      rw [hinvT]
      exact mul_le_mul_of_nonneg_left hZ' hrcl.le
    have h := hsub (z₀ + L ζ) hζΩ _ (hΨcd φ ζ hφ) hmax'
    rw [hfactor φ ζ hφ] at h
    have hpos : (0 : ℝ) < lam * c ^ 3 / r := by positivity
    exact nonneg_of_mul_nonneg_right h hpos
  · -- lower tests: the mirror argument with minima
    intro ζ hζ φ hφ hmin
    have hζΩ : z₀ + L ζ ∈ Ω := hζ
    have hmin' : IsLocalMinOn (fun Z : WithLp 2 (F × ℝ) => U Z
        - (U z₀ + r * c * ((ofLp (L.symm (Z - z₀))).2
          + lam * φ (L.symm (Z - z₀))))) Ω (z₀ + L ζ) := by
      have htr : ContinuousWithinAt (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) Ω
          (z₀ + L ζ) := by fun_prop
      have hmaps : Set.MapsTo (fun Z : WithLp 2 (F × ℝ) => L.symm (Z - z₀)) Ω
          ((fun z : WithLp 2 (F × ℝ) => z₀ + L z) ⁻¹' Ω) := by
        intro Z hZ; simpa [hZeq Z] using hZ
      have htend := htr.tendsto_nhdsWithin hmaps
      simp only [hinvT] at htend
      refine Filter.Eventually.mono (htend.eventually hmin) fun Z hZ => ?_
      have hZ' : v ζ - φ ζ ≤ v (L.symm (Z - z₀)) - φ (L.symm (Z - z₀)) := hZ
      simp only [hdiffid]
      rw [hinvT]
      exact mul_le_mul_of_nonneg_left hZ' hrcl.le
    have h := hsup (z₀ + L ζ) hζΩ _ (hΨcd φ ζ hφ) hmin'
    rw [hfactor φ ζ hφ] at h
    have hpos : (0 : ℝ) < lam * c ^ 3 / r := by positivity
    exact nonpos_of_mul_nonpos_right h hpos
