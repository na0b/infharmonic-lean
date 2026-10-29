module

public import InfHarmonic.ClosedSuperjet
public import InfHarmonic.IsLimitSubOn

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A subsolution of the limiting equation satisfies the operator inequality on
its closed superjets, not only at `C²` upper tests. -/
theorem LimitSubClosedSuperjet (Ω : Set (WithLp 2 (F × ℝ)))
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsLimitSubOn Ω v)
    (z : WithLp 2 (F × ℝ)) (hz : z ∈ Ω)
    (p : WithLp 2 (F × ℝ)) (X : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ)
    (hpX : (p, X) ∈ ClosedSuperjet v z) :
    0 ≤ X (toLp 2 ((ofLp p).1, (1 : ℝ))) (toLp 2 ((ofLp p).1, (1 : ℝ))) := by
  -- the toolkit, inlined (reviewer's three verbatim, then mine)
  have rdiag1 : ∀ (A : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ)
      (x : WithLp 2 (F × ℝ)), HasFDerivAt (fun w => A w w) (A x + A.flip x) x := by
    intro A x
    have hb := A.isBoundedBilinearMap
    have hd : HasFDerivAt (fun p : WithLp 2 (F × ℝ) × WithLp 2 (F × ℝ) => A p.1 p.2)
        (hb.deriv (x, x)) (x, x) := hb.hasFDerivAt (x, x)
    have hdiag : HasFDerivAt (fun w : WithLp 2 (F × ℝ) => (w, w))
        ((ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))).prod
          (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ)))) x :=
      (hasFDerivAt_id x).prodMk (hasFDerivAt_id x)
    have hcomp : HasFDerivAt
        ((fun p : WithLp 2 (F × ℝ) × WithLp 2 (F × ℝ) => A p.1 p.2) ∘
          (fun w : WithLp 2 (F × ℝ) => (w, w)))
        ((hb.deriv (x, x)).comp
          ((ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))).prod
            (ContinuousLinearMap.id ℝ (WithLp 2 (F × ℝ))))) x := HasFDerivAt.comp x hd hdiag
    refine hcomp.congr_fderiv (ContinuousLinearMap.ext fun u => ?_)
    simp [IsBoundedBilinearMap.deriv]
  have rdiag2 : ∀ (A : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ)
      (x h k : WithLp 2 (F × ℝ)),
      fderiv ℝ (fderiv ℝ (fun w => A w w)) x h k = A h k + A k h := by
    intro A x h k
    have hfd : fderiv ℝ (fun w : WithLp 2 (F × ℝ) => A w w)
        = ((A + A.flip : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ) :
            WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ) →L[ℝ] ℝ) := by
      funext w; rw [(rdiag1 A w).fderiv]; ext u; simp
    rw [hfd, ContinuousLinearMap.fderiv]; simp
  have rdiagIt : ∀ (A : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ)
      (x ζ : WithLp 2 (F × ℝ)),
      iteratedFDeriv ℝ 2 (fun w => A w w) x (fun _ => ζ) = A ζ ζ + A ζ ζ := by
    intro A x ζ; rw [iteratedFDeriv_two_apply, rdiag2]
  have shifted : ∀ (A : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ)
      (c x ζ : WithLp 2 (F × ℝ)),
      iteratedFDeriv ℝ 2 (fun w => A (w - c) (w - c)) x (fun _ => ζ) = A ζ ζ + A ζ ζ := by
    intro A c x ζ
    have hfun : (fun w : WithLp 2 (F × ℝ) => A (w - c) (w - c))
        = fun z : WithLp 2 (F × ℝ) => (fun u : WithLp 2 (F × ℝ) => A u u) (z + (-c)) := by
      funext w; simp [sub_eq_add_neg]
    rw [hfun, iteratedFDeriv_comp_add_right
      (f := fun u : WithLp 2 (F × ℝ) => A u u) 2 (-c) x, rdiagIt]
  have cdiag : ∀ A : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ,
      ContDiff ℝ 2 (fun w : WithLp 2 (F × ℝ) => A w w) :=
    fun A => A.isBoundedBilinearMap.contDiff.comp (contDiff_id.prodMk contDiff_id)
  -- STEP 1: the inequality at a plain superjet.
  have step1 : ∀ (z' q : WithLp 2 (F × ℝ))
      (Y : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ),
      z' ∈ Ω → (q, Y) ∈ Superjet v z' →
      0 ≤ Y (toLp 2 ((ofLp q).1, (1 : ℝ))) (toLp 2 ((ofLp q).1, (1 : ℝ))) := by
    intro z' q Y hz' hjet
    obtain ⟨-, hYjet⟩ := hjet
    -- an opaque name for the operator direction
    obtain ⟨ξ, hξ⟩ : ∃ ξ : WithLp 2 (F × ℝ), ξ = toLp 2 ((ofLp q).1, (1 : ℝ)) := ⟨_, rfl⟩
    rw [← hξ]
    have key : ∀ ε : ℝ, 0 < ε → 0 ≤ Y ξ ξ + 2 * ε * ‖ξ‖ ^ 2 := by
      intro ε hε
      -- ONE bilinear form carrying both quadratic pieces
      obtain ⟨Q, hQ⟩ : ∃ Q : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ,
          ∀ u w : WithLp 2 (F × ℝ), Q u w = inner ℝ u w := ⟨innerSL ℝ, fun u w => rfl⟩
      obtain ⟨B, hBdef⟩ : ∃ B : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ,
          B = (2⁻¹ : ℝ) • Y + ε • Q := ⟨_, rfl⟩
      have hBdiag : ∀ u : WithLp 2 (F × ℝ), B u u = Y u u / 2 + ε * ‖u‖ ^ 2 := by
        intro u
        rw [hBdef]
        simp only [add_apply, smul_apply, smul_eq_mul, hQ, real_inner_self_eq_norm_sq]
        ring
      -- phi = affine + shifted diagonal of B
      obtain ⟨φ₁, hφ1⟩ : ∃ f : WithLp 2 (F × ℝ) → ℝ,
          f = fun w => v z' + inner ℝ q (w - z') := ⟨_, rfl⟩
      obtain ⟨φ₂, hφ2⟩ : ∃ f : WithLp 2 (F × ℝ) → ℝ,
          f = fun w => B (w - z') (w - z') := ⟨_, rfl⟩
      have htr : ContDiff ℝ 2 (fun u : WithLp 2 (F × ℝ) => u - z') :=
        contDiff_id.sub contDiff_const
      have hφ1C : ContDiff ℝ 2 φ₁ := by
        rw [hφ1]
        exact contDiff_const.add ((innerSL ℝ q).contDiff.comp htr)
      have hφ2C : ContDiff ℝ 2 φ₂ := by
        rw [hφ2]; exact (cdiag B).comp htr
      -- first derivatives
      have hφ1d : ∀ w : WithLp 2 (F × ℝ), HasFDerivAt φ₁ (innerSL ℝ q) w := by
        intro w
        rw [hφ1]
        have h0 : HasFDerivAt (fun u : WithLp 2 (F × ℝ) => inner ℝ q (u - z') : _ → ℝ)
            (innerSL ℝ q) w := by
          exact ((innerSL ℝ q).hasFDerivAt (x := w - z')).comp w
            ((hasFDerivAt_id w).sub_const z')
        refine ((hasFDerivAt_const (v z') w).add h0).congr_fderiv ?_
        simp
      have hφ2d0 : fderiv ℝ φ₂ z' = 0 := by
        have hfun : φ₂ = fun z : WithLp 2 (F × ℝ) =>
            (fun u : WithLp 2 (F × ℝ) => B u u) (z + (-z')) := by
          rw [hφ2]; funext w; simp [sub_eq_add_neg]
        rw [hfun, fderiv_comp_add_right (f := fun u : WithLp 2 (F × ℝ) => B u u) (-z')]
        rw [(rdiag1 B (z' + -z')).fderiv]
        ext u; simp
      -- the gradient is q, so the operator direction is exactly xi
      have hgrad : gradient (φ₁ + φ₂) z' = q := by
        have hgr : HasGradientAt (φ₁ + φ₂) q z' := by
          rw [hasGradientAt_iff_hasFDerivAt]
          have he : (InnerProductSpace.toDual ℝ (WithLp 2 (F × ℝ))) q = innerSL ℝ q := by
            ext u; simp
          rw [he]
          have h2 : HasFDerivAt φ₂ (0 : WithLp 2 (F × ℝ) →L[ℝ] ℝ) z' := by
            have hd := (hφ2C.differentiable (by norm_num)).differentiableAt (x := z')
            simpa [hφ2d0] using hd.hasFDerivAt
          simpa using (hφ1d z').add h2
        exact hgr.gradient
      -- the operator value
      have hop : LimitOp (φ₁ + φ₂) z' = Y ξ ξ + 2 * ε * ‖ξ‖ ^ 2 := by
        unfold LimitOp
        rw [hgrad, ← hξ, iteratedFDeriv_add_apply hφ1C.contDiffAt hφ2C.contDiffAt]
        have hj1 : iteratedFDeriv ℝ 2 φ₁ z' (fun _ => ξ) = 0 := by
          have hfd : fderiv ℝ φ₁ = fun _ => innerSL ℝ q := funext fun w => (hφ1d w).fderiv
          have hD2 : fderiv ℝ (fderiv ℝ φ₁) z' = 0 := by
            rw [hfd]; exact (hasFDerivAt_const (innerSL ℝ q) z').fderiv
          rw [iteratedFDeriv_two_apply, hD2]; simp
        have hj2 : iteratedFDeriv ℝ 2 φ₂ z' (fun _ => ξ) = B ξ ξ + B ξ ξ := by
          rw [hφ2]; exact shifted B z' z' ξ
        simp only [add_apply, hj1, hj2, hBdiag]
        ring
      -- phi is an upper test for v at z'
      obtain ⟨δ, hδ, hball⟩ := hYjet ε hε
      have hval : ∀ w : WithLp 2 (F × ℝ), (φ₁ + φ₂) w
          = v z' + inner ℝ q (w - z') + (Y (w - z') (w - z') / 2 + ε * ‖w - z'‖ ^ 2) := by
        intro w; simp only [Pi.add_apply, hφ1, hφ2, hBdiag]
      have hmax : IsLocalMaxOn (fun w => v w - (φ₁ + φ₂) w) Ω z' := by
        refine Filter.eventually_of_mem
          (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds z' hδ)) ?_
        intro w hw
        have hd : ‖w - z'‖ < δ := by rw [← dist_eq_norm]; exact hw
        have h1 := hball (w - z') hd
        have hw' : z' + (w - z') = w := by abel
        rw [hw'] at h1
        have hz'val : (φ₁ + φ₂) z' = v z' := by rw [hval]; simp
        show v w - (φ₁ + φ₂) w ≤ v z' - (φ₁ + φ₂) z'
        rw [hz'val, hval w]
        linarith
      have hcd : ContDiffAt ℝ 2 (φ₁ + φ₂) z' := (hφ1C.add hφ2C).contDiffAt
      have hres := hv.2.2 z' hz' (φ₁ + φ₂) hcd hmax
      rw [hop] at hres
      exact hres
    -- epsilon down to zero, no limit
    refine le_of_forall_pos_le_add ?_
    intro η hη
    have hD : (0:ℝ) < 2 * (2 * ‖ξ‖ ^ 2 + 1) := by positivity
    have h := key (η / (2 * (2 * ‖ξ‖ ^ 2 + 1))) (by positivity)
    have hid : η / (2 * (2 * ‖ξ‖ ^ 2 + 1)) * (2 * (2 * ‖ξ‖ ^ 2 + 1)) = η :=
      div_mul_cancel₀ _ (ne_of_gt hD)
    have ht0 : (0:ℝ) ≤ η / (2 * (2 * ‖ξ‖ ^ 2 + 1)) := by positivity
    nlinarith [h, hid, ht0, sq_nonneg ‖ξ‖]
  -- STEP 2: passing to the closure.
  obtain ⟨zs, ps, Xs, hjets, hzt, -, hpt, hXt⟩ := hpX
  obtain ⟨dir, hdirapp⟩ : ∃ d : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ),
      ∀ u, d u = toLp 2 ((ofLp u).1, (1 : ℝ)) := ⟨_, fun u => rfl⟩
  have hdirC : Continuous dir := by
    have hfun : dir = fun u : WithLp 2 (F × ℝ) => (toLp 2 ((ofLp u).1, (1 : ℝ))) :=
      funext hdirapp
    rw [hfun]; fun_prop
  have hζ : Filter.Tendsto (fun k => dir (ps k)) Filter.atTop (nhds (dir p)) :=
    (hdirC.tendsto p).comp hpt
  -- Omega is open and z_k -> z, so z_k is eventually in Omega
  obtain ⟨δ₀, hδ₀, hsub⟩ := Metric.isOpen_iff.mp hv.1 z hz
  have hev : ∀ᶠ k in Filter.atTop, zs k ∈ Ω := by
    have hb : ∀ᶠ k in Filter.atTop, zs k ∈ Metric.ball z δ₀ :=
      hzt (Metric.ball_mem_nhds z hδ₀)
    exact hb.mono fun k hk => hsub hk
  have hstep : ∀ᶠ k in Filter.atTop, 0 ≤ Xs k (dir (ps k)) (dir (ps k)) := by
    refine hev.mono fun k hk => ?_
    rw [hdirapp]
    exact step1 (zs k) (ps k) (Xs k) hk (hjets k)
  -- the limit, by joint continuity of the bilinear application
  rw [← hdirapp p]
  have hXt' : Filter.Tendsto Xs Filter.atTop (nhds X) := hXt
  -- joint continuity of the bilinear application, applied twice.  The types are left to
  -- inference: ascribing them re-triggers the WithLp CLM-valued instance diamond.
  have hpair : Filter.Tendsto (fun k => (Xs k, dir (ps k))) Filter.atTop
      (nhds ((X, dir p) :
        (WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) →L[ℝ] ℝ) × WithLp 2 (F × ℝ))) :=
    Filter.Tendsto.prodMk_nhds hXt' hζ
  have h1 := Filter.Tendsto.comp
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := WithLp 2 (F × ℝ))
      (F := WithLp 2 (F × ℝ) →L[ℝ] ℝ)).continuous.tendsto (X, dir p)) hpair
  have hpair2 := Filter.Tendsto.prodMk_nhds h1 hζ
  have h2 := Filter.Tendsto.comp
    ((isBoundedBilinearMap_apply (𝕜 := ℝ) (E := WithLp 2 (F × ℝ))
      (F := ℝ)).continuous.tendsto (X (dir p), dir p)) hpair2
  exact ge_of_tendsto h2 hstep
