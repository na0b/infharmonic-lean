module

public import InfHarmonic.TimeFlip
public import InfHarmonic.IsFitClass
public import InfHarmonic.QuadEnvP
public import InfHarmonic.QuadEnvM
public import InfHarmonic.HasJensenBound

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The time reversal `f̃(x,t) = -f(x,-t)` exchanges subsolutions and
supersolutions of the limiting equation, exchanges the two quadratic envelopes,
preserves the class `A_{m,C₀}` while sending a fit `(p,a)` to `(-p,a)`,
and reverses the sign of a horizontal Jensen defect. -/
theorem TimeReversal (C₀ : ℝ) (f : WithLp 2 (F × ℝ) → ℝ) :
    (∀ Ω : Set (WithLp 2 (F × ℝ)), IsLimitSubOn Ω f →
        IsLimitSuperOn ((fun z => toLp 2 ((ofLp z).1, -(ofLp z).2)) ⁻¹' Ω) (TimeFlip f)) ∧
    (∀ Ω : Set (WithLp 2 (F × ℝ)), IsLimitSuperOn Ω f →
        IsLimitSubOn ((fun z => toLp 2 ((ofLp z).1, -(ofLp z).2)) ⁻¹' Ω) (TimeFlip f)) ∧
    (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)),
        QuadEnvP (TimeFlip f) l z = -QuadEnvM f l (toLp 2 ((ofLp z).1, -(ofLp z).2))) ∧
    (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)),
        QuadEnvM (TimeFlip f) l z = -QuadEnvP f l (toLp 2 ((ofLp z).1, -(ofLp z).2))) ∧
    (∀ (z : WithLp 2 (F × ℝ)) (R : ℝ) (p : F) (a : ℝ), IsFit C₀ f z R p a →
        IsFit C₀ (TimeFlip f) (toLp 2 ((ofLp z).1, -(ofLp z).2)) R (-p) a) ∧
    (IsFitClass C₀ f → IsFitClass C₀ (TimeFlip f)) ∧
    (∀ κ : ℝ, HasJensenBound Set.univ (TimeFlip f) κ ↔
        ∀ (t : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
          IsBaryConfig n θ y x →
            f (toLp 2 (x, t)) - (∑ i, θ i * f (toLp 2 (y i, t)))
              ≤ κ * BaryRadius n θ y x) := by
  classical
  -- Π, the time reflection of space-time: an involutive, self-adjoint linear equivalence.
  let PiL : WithLp 2 (F × ℝ) →L[ℝ] WithLp 2 (F × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
      (((ContinuousLinearMap.fst ℝ F ℝ).prod
        (-(ContinuousLinearMap.snd ℝ F ℝ))).comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap)
  have hPiL : ∀ z : WithLp 2 (F × ℝ), PiL z = toLp 2 ((ofLp z).1, -(ofLp z).2) := by
    intro z; simp [PiL]
  have hflipfun :
      (fun z : WithLp 2 (F × ℝ) => toLp 2 ((ofLp z).1, -(ofLp z).2)) = (PiL : _ → _) := by
    funext z; exact (hPiL z).symm
  have hPiPi : ∀ z : WithLp 2 (F × ℝ), PiL (PiL z) = z := by
    intro z; simp only [hPiL, neg_neg]
  have hself : ∀ u v : WithLp 2 (F × ℝ), inner ℝ (PiL u) v = inner ℝ u (PiL v) := by
    intro u v; simp [hPiL, WithLp.prod_inner_apply]
  let PiE : WithLp 2 (F × ℝ) ≃L[ℝ] WithLp 2 (F × ℝ) :=
    ContinuousLinearEquiv.equivOfInverse PiL PiL hPiPi hPiPi
  have hPiE : ∀ z : WithLp 2 (F × ℝ), PiE z = PiL z := by intro z; simp [PiE]
  -- Step 1a: the chain rule gives `∇(-φ∘Π)(Πz) = -Π ∇φ(z)`, using self-adjointness of `Π`.
  have hgrad : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)),
      DifferentiableAt ℝ φ z →
      gradient (fun w => -(φ (PiL w))) (PiL z) = -(PiL (gradient φ z)) := by
    intro φ z hφ
    have hg : HasFDerivAt φ (fderiv ℝ φ z) (PiL (PiL z)) := by
      rw [hPiPi]; exact hφ.hasFDerivAt
    have hchain : HasFDerivAt (fun w : WithLp 2 (F × ℝ) => φ (PiL w))
        ((fderiv ℝ φ z).comp PiL) (PiL z) := hg.comp (PiL z) PiL.hasFDerivAt
    have hd : ∀ w : WithLp 2 (F × ℝ), fderiv ℝ φ z w = inner ℝ (gradient φ z) w := by
      intro w; rw [← toDual_gradient (f := φ) (x := z)]; rfl
    have hgr : HasGradientAt (fun w => -(φ (PiL w))) (-(PiL (gradient φ z))) (PiL z) := by
      rw [hasGradientAt_iff_hasFDerivAt]
      have he : (InnerProductSpace.toDual ℝ (WithLp 2 (F × ℝ))) (-(PiL (gradient φ z)))
          = -((fderiv ℝ φ z).comp PiL) := by
        ext v
        simp only [InnerProductSpace.toDual_apply_apply, neg_apply,
          ContinuousLinearMap.comp_apply, inner_neg_left, hd, hself]
      rw [he]
      exact hchain.neg
    exact hgr.gradient
  -- Step 1b: `Π` is linear, so `D²(-φ∘Π)(Πz)[ξ,ξ] = -D²φ(z)[Πξ,Πξ]`.
  have hsnd : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (z ξ : WithLp 2 (F × ℝ)),
      iteratedFDeriv ℝ 2 (fun w => -(φ (PiL w))) (PiL z) (fun _ => ξ)
        = -iteratedFDeriv ℝ 2 φ z (fun _ => PiL ξ) := by
    intro φ z ξ
    have hfun : (fun w : WithLp 2 (F × ℝ) => -(φ (PiL w))) = (-φ) ∘ PiE := by
      funext w; simp [hPiE w]
    have hstep := PiE.iteratedFDerivWithin_comp_right (-φ) (s := univ)
      uniqueDiffOn_univ (x := PiL z) (Set.mem_univ _) 2
    simp only [Set.preimage_univ, iteratedFDerivWithin_univ] at hstep
    rw [hfun, hstep]
    simp only [ContinuousLinearEquiv.coe_coe, hPiE, hPiPi, iteratedFDeriv_neg_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply, neg_apply]
  -- a bilinear form is unchanged by negating both of its slots
  have hnegslot : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (z v : WithLp 2 (F × ℝ)),
      iteratedFDeriv ℝ 2 φ z (fun _ => -v) = iteratedFDeriv ℝ 2 φ z (fun _ => v) := by
    intro φ z v
    simpa using (iteratedFDeriv ℝ 2 φ z).map_smul_univ (fun _ : Fin 2 => (-1 : ℝ))
      (fun _ : Fin 2 => v)
  -- Step 1c: the operator transfer `F[-φ∘Π](Πz) = -F[φ](z)`.
  have hop : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)),
      DifferentiableAt ℝ φ z →
      LimitOp (fun w => -(φ (PiL w))) (PiL z) = -LimitOp φ z := by
    intro φ z hφ
    have h2 : (ofLp (-(PiL (gradient φ z)))).1 = -(ofLp (gradient φ z)).1 := by
      simp [hPiL]
    simp only [LimitOp, hgrad φ z hφ, h2]
    rw [hsnd φ z (toLp 2 (-(ofLp (gradient φ z)).1, (1 : ℝ)))]
    have h3 : PiL (toLp 2 (-(ofLp (gradient φ z)).1, (1 : ℝ)))
        = -(toLp 2 ((ofLp (gradient φ z)).1, (1 : ℝ))) := by
      simp only [hPiL]; rfl
    rw [h3, hnegslot]
  -- Step 1d: the reflection maps `Ω` into its own preimage, and `f̃ = -f∘Π`.
  have hmapsTo : ∀ Ω : Set (WithLp 2 (F × ℝ)), Set.MapsTo PiL Ω (PiL ⁻¹' Ω) := by
    intro Ω w hw; simp only [Set.mem_preimage, hPiPi]; exact hw
  have hTF : ∀ (g : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)),
      TimeFlip g z = -g (PiL z) := by
    intro g z; simp only [TimeFlip, hPiL]
  have hcontTF : ∀ Ω : Set (WithLp 2 (F × ℝ)), ContinuousOn f Ω →
      ContinuousOn (TimeFlip f) (PiL ⁻¹' Ω) := by
    intro Ω hcf
    have hc : ContinuousOn (fun z : WithLp 2 (F × ℝ) => f (PiL z)) (PiL ⁻¹' Ω) :=
      hcf.comp PiL.continuous.continuousOn (Set.mapsTo_preimage _ _)
    have heq : TimeFlip f = fun z : WithLp 2 (F × ℝ) => -f (PiL z) := by
      funext w; exact hTF f w
    rw [heq]
    exact hc.neg
  have hψcd : ∀ (φ : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)), ContDiffAt ℝ 2 φ z →
      ContDiffAt ℝ 2 (fun w : WithLp 2 (F × ℝ) => -(φ (PiL w))) (PiL z) := by
    intro φ z hφ
    have h1 : ContDiffAt ℝ 2 φ (PiL (PiL z)) := by rw [hPiPi]; exact hφ
    simpa [Function.comp_def] using (h1.comp (PiL z) PiL.contDiff.contDiffAt).neg
  -- Part (1): subsolutions go to supersolutions, and conversely.
  have hsub2super : ∀ Ω : Set (WithLp 2 (F × ℝ)), IsLimitSubOn Ω f →
      IsLimitSuperOn (PiL ⁻¹' Ω) (TimeFlip f) := by
    intro Ω hf
    obtain ⟨hΩ, hcf, hsub⟩ := hf
    refine ⟨hΩ.preimage PiL.continuous, hcontTF Ω hcf, ?_⟩
    intro z hz φ hφ hmin
    have hzΩ : PiL z ∈ Ω := hz
    have hmax : IsLocalMaxOn (fun w => f w - (fun u => -(φ (PiL u))) w) Ω (PiL z) := by
      have hSc : ContinuousWithinAt (fun w : WithLp 2 (F × ℝ) => PiL w) Ω (PiL z) :=
        PiL.continuous.continuousWithinAt
      have htend := hSc.tendsto_nhdsWithin (hmapsTo Ω)
      simp only [hPiPi] at htend
      refine Filter.Eventually.mono (htend.eventually hmin) fun w hw => ?_
      simp only [hTF, hPiPi] at hw
      simp only [hPiPi]
      linarith
    have h0 := hsub (PiL z) hzΩ (fun w => -(φ (PiL w))) (hψcd φ z hφ) hmax
    rw [hop φ z (hφ.differentiableAt (by norm_num))] at h0
    linarith
  have hsuper2sub : ∀ Ω : Set (WithLp 2 (F × ℝ)), IsLimitSuperOn Ω f →
      IsLimitSubOn (PiL ⁻¹' Ω) (TimeFlip f) := by
    intro Ω hf
    obtain ⟨hΩ, hcf, hsup⟩ := hf
    refine ⟨hΩ.preimage PiL.continuous, hcontTF Ω hcf, ?_⟩
    intro z hz φ hφ hmax
    have hzΩ : PiL z ∈ Ω := hz
    have hmin : IsLocalMinOn (fun w => f w - (fun u => -(φ (PiL u))) w) Ω (PiL z) := by
      have hSc : ContinuousWithinAt (fun w : WithLp 2 (F × ℝ) => PiL w) Ω (PiL z) :=
        PiL.continuous.continuousWithinAt
      have htend := hSc.tendsto_nhdsWithin (hmapsTo Ω)
      simp only [hPiPi] at htend
      refine Filter.Eventually.mono (htend.eventually hmax) fun w hw => ?_
      simp only [hTF, hPiPi] at hw
      simp only [hPiPi]
      linarith
    have h0 := hsup (PiL z) hzΩ (fun w => -(φ (PiL w))) (hψcd φ z hφ) hmin
    rw [hop φ z (hφ.differentiableAt (by norm_num))] at h0
    linarith
  -- Part (3): the fit transfer.
  have hfit : ∀ (z : WithLp 2 (F × ℝ)) (R : ℝ) (p : F) (a : ℝ), IsFit C₀ f z R p a →
      IsFit C₀ (TimeFlip f) (toLp 2 ((ofLp z).1, -(ofLp z).2)) R (-p) a := by
    intro z R p a hf h l hl hh
    have hh' : ‖h - (-l) • p‖ ≤ R := by simpa using hh
    have h1 := hf h (-l) (by rwa [abs_neg]) hh'
    have e1 : (toLp 2 ((ofLp z).1, -(ofLp z).2) + toLp 2 (h, l) : WithLp 2 (F × ℝ))
        = toLp 2 ((ofLp z).1 + h, -(ofLp z).2 + l) := rfl
    have e2 : (z + toLp 2 (h, -l) : WithLp 2 (F × ℝ))
        = toLp 2 ((ofLp z).1 + h, (ofLp z).2 + -l) := rfl
    have e3 : TimeFlip f (toLp 2 ((ofLp z).1, -(ofLp z).2) + toLp 2 (h, l))
        = -f (z + toLp 2 (h, -l)) := by
      simp only [TimeFlip, e1, e2, WithLp.ofLp_toLp]
      rw [show -(-(ofLp z).2 + l) = (ofLp z).2 + -l by ring]
    have e4 : TimeFlip f (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ)) = -f z := by
      simp only [TimeFlip, neg_neg]
    rw [e3, e4, inner_neg_left, norm_neg,
      show -f (z + toLp 2 (h, -l)) - -f z - -inner ℝ p h - (a - ‖p‖ ^ 2 / 2) * l
        = -(f (z + toLp 2 (h, -l)) - f z - inner ℝ p h - (a - ‖p‖ ^ 2 / 2) * (-l)) by ring,
      abs_neg]
    exact h1
  -- Part (2): the envelope identities, via `sSup (-S) = -sInf S`.
  have henvP : ∀ (l : ℝ) (z : WithLp 2 (F × ℝ)),
      QuadEnvP (TimeFlip f) l z = -QuadEnvM f l (toLp 2 ((ofLp z).1, -(ofLp z).2)) := by
    intro l z
    by_cases hl : l = 0
    · simp [QuadEnvP, QuadEnvM, hl, TimeFlip]
    · have hset : {w : ℝ | ∃ y : F, w = TimeFlip f (toLp 2 (y, (ofLp z).2 + l))
          - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}
          = -{w : ℝ | ∃ y : F,
              w = f (toLp 2 (y, (ofLp (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ))).2 - l))
                + ‖y - (ofLp (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ))).1‖ ^ 2
                  / (2 * l)} := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_neg, TimeFlip]
        constructor
        · rintro ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          rw [show -(ofLp z).2 - l = -((ofLp z).2 + l) by ring]
          ring
        · rintro ⟨y, hy⟩
          refine ⟨y, ?_⟩
          rw [show -(ofLp z).2 - l = -((ofLp z).2 + l) by ring] at hy
          linarith
      simp only [QuadEnvP, QuadEnvM, hl, if_false]
      rw [hset, Real.sSup_neg]
  have henvM : ∀ (l : ℝ) (z : WithLp 2 (F × ℝ)),
      QuadEnvM (TimeFlip f) l z = -QuadEnvP f l (toLp 2 ((ofLp z).1, -(ofLp z).2)) := by
    intro l z
    by_cases hl : l = 0
    · simp [QuadEnvP, QuadEnvM, hl, TimeFlip]
    · have hset : {w : ℝ | ∃ y : F, w = TimeFlip f (toLp 2 (y, (ofLp z).2 - l))
          + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}
          = -{w : ℝ | ∃ y : F,
              w = f (toLp 2 (y, (ofLp (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ))).2 + l))
                - ‖y - (ofLp (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ))).1‖ ^ 2
                  / (2 * l)} := by
        ext w
        simp only [Set.mem_ofPred_eq, Set.mem_neg, TimeFlip]
        constructor
        · rintro ⟨y, rfl⟩
          refine ⟨y, ?_⟩
          rw [show -(ofLp z).2 + l = -((ofLp z).2 - l) by ring]
          ring
        · rintro ⟨y, hy⟩
          refine ⟨y, ?_⟩
          rw [show -(ofLp z).2 + l = -((ofLp z).2 - l) by ring] at hy
          linarith
      simp only [QuadEnvP, QuadEnvM, hl, if_false]
      rw [hset, Real.sInf_neg]
  -- Part (3), second half: the class is preserved.
  have hclass : IsFitClass C₀ f → IsFitClass C₀ (TimeFlip f) := by
    rintro ⟨⟨hsol1, hsol2⟩, hfits⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simpa using hsuper2sub univ hsol2
    · simpa using hsub2super univ hsol1
    · intro z R hR
      obtain ⟨p, a, hpa⟩ := hfits (PiL z) R hR
      refine ⟨-p, a, ?_⟩
      have h := hfit (PiL z) R p a hpa
      rwa [← hPiL, hPiPi] at h
  -- Part (4): the Jensen defect changes sign.
  have hjensen : ∀ κ : ℝ, HasJensenBound Set.univ (TimeFlip f) κ ↔
      ∀ (t : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
        IsBaryConfig n θ y x →
          f (toLp 2 (x, t)) - (∑ i, θ i * f (toLp 2 (y i, t)))
            ≤ κ * BaryRadius n θ y x := by
    intro κ
    have key : ∀ (t : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
        (∑ i, θ i * TimeFlip f (toLp 2 (y i, t))) - TimeFlip f (toLp 2 (x, t))
          = f (toLp 2 (x, -t)) - (∑ i, θ i * f (toLp 2 (y i, -t))) := by
      intro t n θ y x
      simp only [TimeFlip, mul_neg, Finset.sum_neg_distrib, sub_neg_eq_add]
      ring
    constructor
    · intro hb t n θ y x hc
      have h := hb (-t) (Set.mem_univ _) n θ y x hc
      rw [key] at h
      simpa using h
    · intro hb t _ n θ y x hc
      rw [key]
      exact hb (-t) n θ y x hc
  refine ⟨?_, ?_, henvP, henvM, hfit, hclass, hjensen⟩
  · intro Ω hΩf
    have h := hsub2super Ω hΩf
    rwa [← hflipfun] at h
  · intro Ω hΩf
    have h := hsuper2sub Ω hΩf
    rwa [← hflipfun] at h
