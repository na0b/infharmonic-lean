import InfHarmonic.IsInfHarmonicOn
open Set WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma 2.1: the linear lift `U(y,b) = u(y) + b` of an infinity-harmonic
function is infinity-harmonic on the lifted domain. -/
theorem LinearLift (Ω : Set E) (u : E → ℝ) (hu : IsInfHarmonicOn Ω u) :
    IsInfHarmonicOn ((fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω)
      (fun z : WithLp 2 (E × ℝ) => u (ofLp z).1 + (ofLp z).2) := by
  obtain ⟨hΩ, huc, -⟩ := hu.1
  -- The second-derivative test at a local extremum.  Mathlib's `LocalExtr` file stops at the
  -- first derivative (`IsLocalMax.deriv_eq_zero`, `IsLocalMax.fderiv_eq_zero`) and has no
  -- second-derivative test, so it is proved here from `hasDerivAt_iff_tendsto_slope` and
  -- `strictMonoOn_of_deriv_pos`.  The `p = 0` branch below is exactly this test on the
  -- vertical restriction.
  have sdMax : ∀ (g : ℝ → ℝ) (b : ℝ), ContDiffAt ℝ 2 g b → IsLocalMax g b →
      deriv (deriv g) b ≤ 0 := by
    intro g b hg hmax
    by_contra hc
    rw [not_le] at hc
    have hd0 : deriv g b = 0 := hmax.deriv_eq_zero
    have h1 : ContDiffAt ℝ 1 (deriv g) b := hg.derivWithin (m := 1) (by norm_num)
    have hdd : HasDerivAt (deriv g) (deriv (deriv g) b) b :=
      (h1.differentiableAt (by norm_num)).hasDerivAt
    have hpos : ∀ᶠ x in nhdsWithin b {b}ᶜ, 0 < slope (deriv g) b x :=
      (hasDerivAt_iff_tendsto_slope.1 hdd).eventually (eventually_gt_nhds hc)
    have hmono : nhdsWithin b (Ioi b) ≤ nhdsWithin b {b}ᶜ :=
      nhdsWithin_mono _ fun x hx => ne_of_gt hx
    have hright : ∀ᶠ x in nhdsWithin b (Ioi b), 0 < deriv g x := by
      filter_upwards [hmono hpos, self_mem_nhdsWithin] with x hx hxgt
      have hdiff : (0 : ℝ) < x - b := sub_pos.2 hxgt
      rw [slope_def_field, hd0, sub_zero, div_pos_iff] at hx
      rcases hx with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · linarith
    obtain ⟨uu, hu1, hgu⟩ := hg.contDiffOn (m := 1) (by norm_num) (by simp)
    obtain ⟨w, hwu, hwopen, hbw⟩ := _root_.mem_nhds_iff.1 (by simpa using hu1)
    have hcomb : ∀ᶠ x in nhdsWithin b (Ioi b), (0 < deriv g x ∧ g x ≤ g b) ∧ x ∈ w := by
      filter_upwards [hright, nhdsWithin_le_nhds (s := Ioi b) hmax,
        nhdsWithin_le_nhds (s := Ioi b) (hwopen.mem_nhds hbw)] with x h1 h2 h3
      exact ⟨⟨h1, h2⟩, h3⟩
    obtain ⟨c, hbc, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hcomb
    rw [mem_Ioi] at hbc
    obtain ⟨x₁, hx₁mem⟩ : ∃ x : ℝ, x ∈ Ioo b c :=
      ⟨(b + c) / 2, by constructor <;> linarith⟩
    have hIcc : Icc b x₁ ⊆ insert b w := by
      intro y hy
      rcases eq_or_lt_of_le hy.1 with h | h
      · exact mem_insert_iff.2 (Or.inl h.symm)
      · exact mem_insert_iff.2 (Or.inr (hsub ⟨h, lt_of_le_of_lt hy.2 hx₁mem.2⟩).2)
    have hcont : ContinuousOn g (Icc b x₁) :=
      (hgu.continuousOn).mono (hIcc.trans (insert_subset (hwu hbw) hwu))
    have hderiv : ∀ y ∈ interior (Icc b x₁), 0 < deriv g y := by
      intro y hy
      rw [interior_Icc] at hy
      exact (hsub ⟨hy.1, lt_trans hy.2 hx₁mem.2⟩).1.1
    have hsm := strictMonoOn_of_deriv_pos (convex_Icc b x₁) hcont hderiv
    have hlt : g b < g x₁ := hsm (left_mem_Icc.2 (le_of_lt hx₁mem.1))
      (right_mem_Icc.2 (le_of_lt hx₁mem.1)) hx₁mem.1
    have hle : g x₁ ≤ g b := (hsub hx₁mem).1.2
    linarith
  have sdMin : ∀ (g : ℝ → ℝ) (b : ℝ), ContDiffAt ℝ 2 g b → IsLocalMin g b →
      0 ≤ deriv (deriv g) b := by
    intro g b hg hmin
    have h := sdMax (fun x => -g x) b hg.neg (by simpa using hmin.neg)
    rw [show (fun x => -g x) = -g from rfl, deriv.neg',
      show (fun x => -deriv g x) = -(deriv g) from rfl, deriv.neg] at h
    linarith
  -- Step 0: the projections and the vertical embedding, as continuous linear maps.
  obtain ⟨Pr, hPr⟩ : ∃ P : WithLp 2 (E × ℝ) →L[ℝ] E, ∀ z, P z = (ofLp z).1 :=
    ⟨(ContinuousLinearMap.fst ℝ E ℝ).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ) : WithLp 2 (E × ℝ) →L[ℝ] E × ℝ), fun _ => rfl⟩
  obtain ⟨Ps, hPs⟩ : ∃ P : WithLp 2 (E × ℝ) →L[ℝ] ℝ, ∀ z, P z = (ofLp z).2 :=
    ⟨(ContinuousLinearMap.snd ℝ E ℝ).comp
      ((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ) : WithLp 2 (E × ℝ) →L[ℝ] E × ℝ), fun _ => rfl⟩
  obtain ⟨Vt, hVt⟩ : ∃ V : ℝ →L[ℝ] WithLp 2 (E × ℝ), ∀ t : ℝ, V t = toLp 2 (0, t) :=
    ⟨((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm :
        (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ)).comp
      ((0 : ℝ →L[ℝ] E).prod (ContinuousLinearMap.id ℝ ℝ)), fun _ => rfl⟩
  obtain ⟨Bd, hBd⟩ : ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∀ q v : E, B q v = inner ℝ q v :=
    ⟨(InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap, fun _ _ => rfl⟩
  have hPrc : Continuous (fun z : WithLp 2 (E × ℝ) => (ofLp z).1) := by
    have h : (fun z : WithLp 2 (E × ℝ) => (ofLp z).1) = Pr := (funext hPr).symm
    rw [h]; exact Pr.continuous
  have hPsc : Continuous (fun z : WithLp 2 (E × ℝ) => (ofLp z).2) := by
    have h : (fun z : WithLp 2 (E × ℝ) => (ofLp z).2) = Ps := (funext hPs).symm
    rw [h]; exact Ps.continuous
  have hΩ' : IsOpen ((fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω) := hΩ.preimage hPrc
  have hUc : ContinuousOn (fun z : WithLp 2 (E × ℝ) => u (ofLp z).1 + (ofLp z).2)
      ((fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω) :=
    (huc.comp hPrc.continuousOn (fun z hz => hz)).add hPsc.continuousOn
  -- the order-2 jet chain rule for a continuous linear map, from `ContDiffAt`; stated twice
  -- because the two source spaces (ℝ for the vertical line, E for the affine lift) differ.
  have jetR : ∀ (L : ℝ →L[ℝ] WithLp 2 (E × ℝ)) (f : WithLp 2 (E × ℝ) → ℝ) (x : ℝ),
      ContDiffAt ℝ 2 f (L x) → ∀ v : ℝ,
      iteratedFDeriv ℝ 2 (f ∘ L) x (fun _ => v)
        = iteratedFDeriv ℝ 2 f (L x) (fun _ => L v) := by
    intro L f x hf v
    obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
    obtain ⟨t, hts, htopen, hxt⟩ := _root_.mem_nhds_iff.1 hs
    have hfo : ContDiffOn ℝ 2 f t := hfs.mono hts
    have hpre : IsOpen (L ⁻¹' t) := htopen.preimage L.continuous
    have hstep := L.iteratedFDerivWithin_comp_right hfo htopen.uniqueDiffOn
      hpre.uniqueDiffOn (x := x) hxt (i := 2) le_rfl
    rw [iteratedFDerivWithin_of_isOpen (f := f ∘ L) 2 hpre hxt,
        iteratedFDerivWithin_of_isOpen (f := f) 2 htopen hxt] at hstep
    rw [hstep]; simp
  have jetE : ∀ (L : E →L[ℝ] WithLp 2 (E × ℝ)) (f : WithLp 2 (E × ℝ) → ℝ) (x : E),
      ContDiffAt ℝ 2 f (L x) → ∀ v : E,
      iteratedFDeriv ℝ 2 (f ∘ L) x (fun _ => v)
        = iteratedFDeriv ℝ 2 f (L x) (fun _ => L v) := by
    intro L f x hf v
    obtain ⟨s, hs, hfs⟩ := hf.contDiffOn (m := 2) le_rfl (by simp)
    obtain ⟨t, hts, htopen, hxt⟩ := _root_.mem_nhds_iff.1 hs
    have hfo : ContDiffOn ℝ 2 f t := hfs.mono hts
    have hpre : IsOpen (L ⁻¹' t) := htopen.preimage L.continuous
    have hstep := L.iteratedFDerivWithin_comp_right hfo htopen.uniqueDiffOn
      hpre.uniqueDiffOn (x := x) hxt (i := 2) le_rfl
    rw [iteratedFDerivWithin_of_isOpen (f := f ∘ L) 2 hpre hxt,
        iteratedFDerivWithin_of_isOpen (f := f) 2 htopen hxt] at hstep
    rw [hstep]; simp
  -- the vertical derivative is the gradient's second coordinate, unconditionally
  have hgrad2 : ∀ (φ : WithLp 2 (E × ℝ) → ℝ) (z : WithLp 2 (E × ℝ)),
      (ofLp (gradient φ z)).2 = fderiv ℝ φ z (toLp 2 (0, 1)) := by
    intro φ z
    rw [← inner_gradient_left (𝕜 := ℝ) (f := φ) (x := z) (y := toLp 2 (0, 1)),
      WithLp.prod_inner_apply]
    simp only [inner_zero_right, zero_add, RCLike.inner_apply, starRingEnd_apply,
      star_trivial, one_mul]
  -- the sign-parameterized viscosity property of `u`
  have husign : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ y ∈ Ω, ∀ ψ : E → ℝ, ContDiffAt ℝ 2 ψ y →
      IsLocalMaxOn (fun x => s * (u x - ψ x)) Ω y → 0 ≤ s * InfLap ψ y := by
    intro s hs y hy ψ hψ hmax
    rcases hs with rfl | rfl
    · have h : IsLocalMaxOn (fun x => u x - ψ x) Ω y := by
        filter_upwards [hmax] with x hx; linarith
      have := hu.1.2.2 y hy ψ hψ h; linarith
    · have h : IsLocalMinOn (fun x => u x - ψ x) Ω y := by
        filter_upwards [hmax] with x hx; linarith
      have := hu.2.2.2 y hy ψ hψ h; linarith
  -- the core, in the sign `s = ±1`
  have core : ∀ s : ℝ, s = 1 ∨ s = -1 →
      ∀ z ∈ (fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω,
      ∀ φ : WithLp 2 (E × ℝ) → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMaxOn (fun x => s * ((u (ofLp x).1 + (ofLp x).2) - φ x))
        ((fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω) z →
      0 ≤ s * InfLap φ z := by
    intro s hs z hz φ hφ hmax
    have hs0 : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
    have hy₀ : (ofLp z).1 ∈ Ω := hz
    -- Step 1: the vertical line through `z`, packaged with its coordinates.
    obtain ⟨cV, hcV0, hcV⟩ : ∃ c : WithLp 2 (E × ℝ), c + Vt (ofLp z).2 = z ∧
        ∀ t : ℝ, (ofLp (c + Vt t)).1 = (ofLp z).1 ∧ (ofLp (c + Vt t)).2 = t :=
      ⟨z - Vt (ofLp z).2, by abel, fun t => ⟨by simp [hVt], by simp [hVt]⟩⟩
    have hmemline : ∀ t : ℝ,
        cV + Vt t ∈ (fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω := by
      intro t
      show (ofLp (cV + Vt t)).1 ∈ Ω
      rw [(hcV t).1]; exact hy₀
    -- the whole line lies in the domain, so the restriction has a genuine local max on ℝ
    have htend : Filter.Tendsto (fun t : ℝ => cV + Vt t)
        (nhds (ofLp z).2) (nhdsWithin z ((fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
        (Filter.Eventually.of_forall hmemline)
      have hc : Continuous (fun t : ℝ => cV + Vt t) := continuous_const.add Vt.continuous
      have h := hc.tendsto (ofLp z).2
      rwa [hcV0] at h
    have hmaxline : ∀ᶠ t in nhds (ofLp z).2,
        s * ((u (ofLp z).1 + t) - φ (cV + Vt t))
          ≤ s * ((u (ofLp z).1 + (ofLp z).2) - φ z) := by
      filter_upwards [htend.eventually hmax] with t ht
      rwa [(hcV t).1, (hcV t).2] at ht
    -- Step 2: the vertical first derivative, giving `φ_b = 1`.
    have hzpt : (fun t : ℝ => cV + Vt t) (ofLp z).2 = z := hcV0
    have hdV : HasDerivAt (fun t : ℝ => φ (cV + Vt t)) (fderiv ℝ φ z (Vt 1)) (ofLp z).2 := by
      have hin : HasDerivAt (fun t : ℝ => cV + Vt t) (Vt 1) (ofLp z).2 :=
        (Vt.hasDerivAt).const_add cV
      have hout : HasFDerivAt φ (fderiv ℝ φ z) ((fun t : ℝ => cV + Vt t) (ofLp z).2) := by
        rw [hzpt]; exact (hφ.differentiableAt (by norm_num)).hasFDerivAt
      simpa only [Function.comp_def] using hout.comp_hasDerivAt (ofLp z).2 hin
    have hdg : HasDerivAt (fun t : ℝ => s * ((u (ofLp z).1 + t) - φ (cV + Vt t)))
        (s * (1 - fderiv ℝ φ z (Vt 1))) (ofLp z).2 :=
      (((hasDerivAt_id ((ofLp z).2)).const_add (u (ofLp z).1)).sub hdV).const_mul s
    have hgmax : IsLocalMax (fun t : ℝ => s * ((u (ofLp z).1 + t) - φ (cV + Vt t)))
        (ofLp z).2 := by
      filter_upwards [hmaxline] with t ht
      show s * ((u (ofLp z).1 + t) - φ (cV + Vt t))
        ≤ s * ((u (ofLp z).1 + (ofLp z).2) - φ (cV + Vt (ofLp z).2))
      rw [hcV0]; exact ht
    have hfb : fderiv ℝ φ z (Vt 1) = 1 := by
      have h0 : deriv (fun t : ℝ => s * ((u (ofLp z).1 + t) - φ (cV + Vt t))) (ofLp z).2 = 0 :=
        hgmax.deriv_eq_zero
      rw [hdg.deriv] at h0
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd h hs0
      · linarith
    have hg2 : (ofLp (gradient φ z)).2 = 1 := by
      rw [hgrad2 φ z, ← hVt 1]; exact hfb
    have hgradeq : gradient φ z = toLp 2 ((ofLp (gradient φ z)).1, (1 : ℝ)) := by rw [← hg2]
    -- the vertical restriction is `C²` at `b₀`
    have hVC : ContDiffAt ℝ 2 (fun t : ℝ => φ (cV + Vt t)) (ofLp z).2 := by
      have h1 : ContDiffAt ℝ 2 φ ((fun t : ℝ => cV + Vt t) (ofLp z).2) := by
        show ContDiffAt ℝ 2 φ (cV + Vt (ofLp z).2)
        rw [hcV0]; exact hφ
      simpa only [Function.comp_def] using
        h1.comp (ofLp z).2 (by fun_prop : ContDiffAt ℝ 2 (fun t : ℝ => cV + Vt t) (ofLp z).2)
    rcases eq_or_ne ((ofLp (gradient φ z)).1) 0 with hp | hp
    · -- Case `p = 0`: the gradient is vertical and the claim is the second-derivative test.
      have hgV : gradient φ z = Vt 1 := by rw [hgradeq, hp, hVt]
      have hfC : ContDiffAt ℝ 2 (fun w : WithLp 2 (E × ℝ) => φ (cV + w)) (Vt (ofLp z).2) := by
        have h1 : ContDiffAt ℝ 2 φ ((fun w : WithLp 2 (E × ℝ) => cV + w) (Vt (ofLp z).2)) := by
          show ContDiffAt ℝ 2 φ (cV + Vt (ofLp z).2)
          rw [hcV0]; exact hφ
        simpa only [Function.comp_def] using h1.comp (Vt (ofLp z).2)
          (by fun_prop : ContDiffAt ℝ 2 (fun w : WithLp 2 (E × ℝ) => cV + w) (Vt (ofLp z).2))
      have hjet := jetR Vt (fun w : WithLp 2 (E × ℝ) => φ (cV + w)) (ofLp z).2 hfC 1
      rw [iteratedFDeriv_comp_add_left 2 cV (Vt (ofLp z).2), hcV0] at hjet
      have hIL : InfLap φ z = deriv (deriv (fun t : ℝ => φ (cV + Vt t))) (ofLp z).2 := by
        unfold InfLap
        rw [hgV, ← hjet, ← iteratedDeriv_eq_iteratedFDeriv,
          show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
        rfl
      -- the function to which the second-derivative test applies, for either sign
      have hkC : ContDiffAt ℝ 2 (fun t : ℝ => s * (φ (cV + Vt t) - t)) (ofLp z).2 :=
        (hVC.sub contDiffAt_id).const_smul s
      have hkmin : IsLocalMin (fun t : ℝ => s * (φ (cV + Vt t) - t)) (ofLp z).2 := by
        filter_upwards [hmaxline] with t ht
        have he : φ (cV + Vt (ofLp z).2) = φ z := by rw [hcV0]
        show s * (φ (cV + Vt (ofLp z).2) - (ofLp z).2) ≤ s * (φ (cV + Vt t) - t)
        rw [he]; nlinarith [ht]
      have h2 := sdMin _ _ hkC hkmin
      -- `deriv (deriv k) b₀ = s * deriv (deriv (vertical restriction)) b₀`
      have hVdiffev : ∀ᶠ t in nhds (ofLp z).2,
          DifferentiableAt ℝ (fun r : ℝ => φ (cV + Vt r)) t := by
        filter_upwards [hVC.eventually (by norm_num)] with t ht
        exact ht.differentiableAt (by norm_num)
      have hkev : deriv (fun t : ℝ => s * (φ (cV + Vt t) - t))
          =ᶠ[nhds (ofLp z).2] fun t => s * deriv (fun r : ℝ => φ (cV + Vt r)) t - s := by
        filter_upwards [hVdiffev] with t ht
        have hd : HasDerivAt (fun r : ℝ => s * (φ (cV + Vt r) - r))
            (s * (deriv (fun r : ℝ => φ (cV + Vt r)) t - 1)) t :=
          ((ht.hasDerivAt).sub (hasDerivAt_id t)).const_mul s
        rw [hd.deriv]; ring
      have hd2 : DifferentiableAt ℝ (deriv (fun r : ℝ => φ (cV + Vt r))) (ofLp z).2 :=
        (hVC.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have hk2 : deriv (deriv (fun t : ℝ => s * (φ (cV + Vt t) - t))) (ofLp z).2
          = s * deriv (deriv (fun r : ℝ => φ (cV + Vt r))) (ofLp z).2 := by
        rw [hkev.deriv_eq, deriv_sub_const, deriv_const_mul _ hd2]
      rw [hIL]
      rw [hk2] at h2
      exact h2
    · -- Case `p ≠ 0`: the affine lift and the viscosity inequality for `u`.
      obtain ⟨Lf, hLf⟩ : ∃ L : E →L[ℝ] WithLp 2 (E × ℝ), ∀ v : E,
          L v = toLp 2 (v, (‖(ofLp (gradient φ z)).1‖ ^ 2)⁻¹ *
            inner ℝ (ofLp (gradient φ z)).1 v) := by
        obtain ⟨Fp, hFp⟩ : ∃ F : E →L[ℝ] ℝ, ∀ v : E,
            F v = (‖(ofLp (gradient φ z)).1‖ ^ 2)⁻¹ * inner ℝ (ofLp (gradient φ z)).1 v :=
          ⟨(‖(ofLp (gradient φ z)).1‖ ^ 2)⁻¹ • Bd (ofLp (gradient φ z)).1,
            fun v => by simp [hBd]⟩
        refine ⟨((WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm :
            (E × ℝ) →L[ℝ] WithLp 2 (E × ℝ)).comp
          ((ContinuousLinearMap.id ℝ E).prod Fp), fun v => ?_⟩
        show toLp 2 (v, Fp v) = _
        rw [hFp]
      have hnp : (0 : ℝ) < ‖(ofLp (gradient φ z)).1‖ ^ 2 := by positivity
      have hLfp : Lf (ofLp (gradient φ z)).1 = gradient φ z := by
        rw [hLf, hgradeq]
        congr 1
        rw [real_inner_self_eq_norm_sq]
        field_simp
      obtain ⟨cE, hcE0, hcE1⟩ : ∃ c : WithLp 2 (E × ℝ), c + Lf (ofLp z).1 = z ∧
          ∀ y : E, (ofLp (c + Lf y)).1 = y :=
        ⟨z - Lf (ofLp z).1, by abel, fun y => by simp [hLf]⟩
      -- the affine lift is a local upper/lower test for `u` at `y₀`
      have hAc : Continuous (fun y : E => cE + Lf y) := continuous_const.add Lf.continuous
      have htendA : Filter.Tendsto (fun y : E => cE + Lf y) (nhdsWithin (ofLp z).1 Ω)
          (nhdsWithin z ((fun z : WithLp 2 (E × ℝ) => (ofLp z).1) ⁻¹' Ω)) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · have h : Filter.Tendsto (fun y : E => cE + Lf y) (nhds (ofLp z).1) (nhds z) := by
            have h0 := hAc.tendsto (ofLp z).1
            rwa [hcE0] at h0
          exact h.mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with y hy
          show (ofLp (cE + Lf y)).1 ∈ Ω
          rw [hcE1]; exact hy
      have hψtest : IsLocalMaxOn (fun y : E => s * (u y -
          (φ (cE + Lf y) - (ofLp (cE + Lf y)).2))) Ω (ofLp z).1 := by
        filter_upwards [htendA.eventually hmax] with y hy
        rw [hcE1] at hy
        show s * (u y - (φ (cE + Lf y) - (ofLp (cE + Lf y)).2))
          ≤ s * (u (ofLp z).1 -
              (φ (cE + Lf (ofLp z).1) - (ofLp (cE + Lf (ofLp z).1)).2))
        rw [hcE0]
        nlinarith [hy]
      -- `ψ` is `C²` at `y₀`
      have hφAC : ContDiffAt ℝ 2 (fun y : E => φ (cE + Lf y)) (ofLp z).1 := by
        have h1 : ContDiffAt ℝ 2 φ ((fun y : E => cE + Lf y) (ofLp z).1) := by
          show ContDiffAt ℝ 2 φ (cE + Lf (ofLp z).1)
          rw [hcE0]; exact hφ
        simpa only [Function.comp_def] using
          h1.comp (ofLp z).1 (by fun_prop : ContDiffAt ℝ 2 (fun y : E => cE + Lf y) (ofLp z).1)
      have hPsL : (fun y : E => (ofLp (cE + Lf y)).2) = fun y : E => Ps (cE + Lf y) := by
        funext y; rw [hPs]
      have hψC : ContDiffAt ℝ 2 (fun y : E => φ (cE + Lf y) - (ofLp (cE + Lf y)).2)
          (ofLp z).1 := by
        refine hφAC.sub ?_
        rw [hPsL]; fun_prop
      -- the gradient of `ψ` at `y₀` is `p`, because `φ_b = 1` and `∇ℓ · p = 1`
      have hA : HasFDerivAt (fun y : E => cE + Lf y) (Lf : E →L[ℝ] WithLp 2 (E × ℝ))
          (ofLp z).1 := (Lf.hasFDerivAt).const_add cE
      have hφA : HasFDerivAt (fun y : E => φ (cE + Lf y))
          ((fderiv ℝ φ z).comp Lf) (ofLp z).1 := by
        have hout : HasFDerivAt φ (fderiv ℝ φ z) ((fun y : E => cE + Lf y) (ofLp z).1) := by
          show HasFDerivAt φ (fderiv ℝ φ z) (cE + Lf (ofLp z).1)
          rw [hcE0]; exact (hφ.differentiableAt (by norm_num)).hasFDerivAt
        simpa only [Function.comp_def] using hout.comp (ofLp z).1 hA
      have hℓd : HasFDerivAt (fun y : E => (ofLp (cE + Lf y)).2) (Ps.comp Lf) (ofLp z).1 := by
        have h := (Ps.hasFDerivAt (x := cE + Lf (ofLp z).1)).comp (ofLp z).1 hA
        simpa only [Function.comp_def, hPs] using h
      have hψd : HasFDerivAt (fun y : E => φ (cE + Lf y) - (ofLp (cE + Lf y)).2)
          ((fderiv ℝ φ z).comp Lf - Ps.comp Lf) (ofLp z).1 := hφA.sub hℓd
      have hgψ : gradient (fun y : E => φ (cE + Lf y) - (ofLp (cE + Lf y)).2) (ofLp z).1
          = (ofLp (gradient φ z)).1 := by
        refine ext_inner_right ℝ (fun v => ?_)
        rw [inner_gradient_left, hψd.fderiv]
        simp only [sub_apply, ContinuousLinearMap.comp_apply]
        rw [← inner_gradient_left (𝕜 := ℝ) (f := φ) (x := z) (y := Lf v), hgradeq, hPs, hLf,
          WithLp.prod_inner_apply]
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
        ring
      -- the second derivative is unchanged by subtracting the affine `ℓ`
      have hfdev : fderiv ℝ (fun y : E => φ (cE + Lf y) - (ofLp (cE + Lf y)).2)
          =ᶠ[nhds (ofLp z).1]
            fun y => fderiv ℝ (fun w : E => φ (cE + Lf w)) y - Ps.comp Lf := by
        filter_upwards [hφAC.eventually (by norm_num)] with y hy
        have hAy : HasFDerivAt (fun w : E => cE + Lf w) (Lf : E →L[ℝ] WithLp 2 (E × ℝ)) y :=
          (Lf.hasFDerivAt).const_add cE
        have hℓy : HasFDerivAt (fun w : E => (ofLp (cE + Lf w)).2) (Ps.comp Lf) y := by
          have h := (Ps.hasFDerivAt (x := cE + Lf y)).comp y hAy
          simpa only [Function.comp_def, hPs] using h
        have hfy := (hy.differentiableAt (by norm_num)).hasFDerivAt
        have hd : HasFDerivAt (fun w : E => φ (cE + Lf w) - (ofLp (cE + Lf w)).2)
            (fderiv ℝ (fun w : E => φ (cE + Lf w)) y - Ps.comp Lf) y := hfy.sub hℓy
        rw [hd.fderiv, hfy.fderiv]
      have h2eq : iteratedFDeriv ℝ 2 (fun y : E => φ (cE + Lf y) - (ofLp (cE + Lf y)).2)
          (ofLp z).1 (fun _ => (ofLp (gradient φ z)).1)
          = iteratedFDeriv ℝ 2 (fun y : E => φ (cE + Lf y)) (ofLp z).1
              (fun _ => (ofLp (gradient φ z)).1) := by
        rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, hfdev.fderiv_eq, fderiv_sub_const]
      -- and the order-2 jet of `φ ∘ A` in the direction `p` is the jet of `φ` at `Lf p = ∇φ(z)`
      have hfCE : ContDiffAt ℝ 2 (fun w : WithLp 2 (E × ℝ) => φ (cE + w)) (Lf (ofLp z).1) := by
        have h1 : ContDiffAt ℝ 2 φ ((fun w : WithLp 2 (E × ℝ) => cE + w) (Lf (ofLp z).1)) := by
          show ContDiffAt ℝ 2 φ (cE + Lf (ofLp z).1)
          rw [hcE0]; exact hφ
        simpa only [Function.comp_def] using h1.comp (Lf (ofLp z).1)
          (by fun_prop : ContDiffAt ℝ 2 (fun w : WithLp 2 (E × ℝ) => cE + w) (Lf (ofLp z).1))
      have hjetE := jetE Lf (fun w : WithLp 2 (E × ℝ) => φ (cE + w)) (ofLp z).1 hfCE
        (ofLp (gradient φ z)).1
      rw [iteratedFDeriv_comp_add_left 2 cE (Lf (ofLp z).1), hcE0] at hjetE
      have hILψ : InfLap (fun y : E => φ (cE + Lf y) - (ofLp (cE + Lf y)).2) (ofLp z).1
          = InfLap φ z := by
        unfold InfLap
        rw [hgψ, h2eq,
          show (fun y : E => φ (cE + Lf y))
            = (fun w : WithLp 2 (E × ℝ) => φ (cE + w)) ∘ Lf from rfl,
          hjetE, hLfp]
      have hfin := husign s hs (ofLp z).1 hy₀ _ hψC hψtest
      rwa [hILψ] at hfin
  refine ⟨⟨hΩ', hUc, ?_⟩, ⟨hΩ', hUc, ?_⟩⟩
  · intro z hz φ hφ hmax
    have := core 1 (Or.inl rfl) z hz φ hφ
      (by filter_upwards [hmax] with x hx; linarith)
    linarith
  · intro z hz φ hφ hmin
    have := core (-1) (Or.inr rfl) z hz φ hφ
      (by filter_upwards [hmin] with x hx; linarith)
    linarith
