import InfHarmonic.EnvelopeSlopeOrder
import InfHarmonic.EnvHamiltonian
import InfHarmonic.TimeReversal
import InfHarmonic.QuadEnvAttained
import Mathlib.Topology.Instances.EReal.Lemmas
open Set WithLp Topology

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.4, solution case: for a solution of the limiting equation both
envelope slopes are nondecreasing, their common small-length limit is the
envelope Hamiltonian `H_f ∈ [-∞, ∞)`, and `H_f` is upper semicontinuous. -/
theorem EnvHamiltonianSolution (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f)
    (hsol : IsLimitSolutionOn ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) f) :
    (∀ (z : WithLp 2 (F × ℝ)) (l l' : ℝ), 0 < l → l ≤ l' →
        (∀ σ ∈ Set.Icc (-l') l', (ofLp z).2 + σ ∈ I) →
        EnvSlopeP f l z ≤ EnvSlopeP f l' z ∧ EnvSlopeM f l z ≤ EnvSlopeM f l' z) ∧
    (∀ z : WithLp 2 (F × ℝ), (∀ σ : ℝ, (ofLp z).2 + σ ∈ I) →
        (⨅ l ∈ Set.Ioi (0 : ℝ), ((EnvSlopeM f l z : ℝ) : EReal)) = EnvHamiltonian f z) ∧
    (∀ z : WithLp 2 (F × ℝ), EnvHamiltonian f z ≠ ⊤) ∧
    ((∀ t ∈ I, ∀ σ : ℝ, t + σ ∈ I) →
      UpperSemicontinuousOn (EnvHamiltonian f)
        ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I)) := by
  classical
  obtain ⟨hsub, hsuper⟩ := hsol
  -- ===== an infimum over the positive lengths lies below each of its members =====
  have hbinf : ∀ (g : ℝ → ℝ) (l : ℝ), 0 < l →
      (⨅ s ∈ Set.Ioi (0 : ℝ), ((g s : ℝ) : EReal)) ≤ ((g l : ℝ) : EReal) := by
    intro g l hl
    exact le_trans (iInf_le _ l) (iInf_le _ hl)
  -- ===== an `EReal` below every real `c + ε` is below `c` =====
  have hEle : ∀ (c : ℝ) (X : EReal), (∀ ε : ℝ, 0 < ε → X ≤ ((c + ε : ℝ) : EReal)) →
      X ≤ ((c : ℝ) : EReal) := by
    intro c X hX
    induction X with
    | bot => exact bot_le
    | coe a =>
        rw [EReal.coe_le_coe_iff]
        by_contra hlt
        rw [not_le] at hlt
        have h2 := hX ((a - c) / 2) (by linarith)
        rw [EReal.coe_le_coe_iff] at h2
        linarith
    | top => exact absurd (top_le_iff.mp (hX 1 one_pos)) (EReal.coe_ne_top _)
  -- ===== the time reversal is a subsolution on the reflected time set =====
  obtain ⟨-, hrev2, hrev3, hrev4, -, -, -⟩ := TimeReversal (0 : ℝ) f
  obtain ⟨Jm, hJmd⟩ : ∃ s : Set ℝ, s = (fun σ : ℝ => -σ) ⁻¹' I := ⟨_, rfl⟩
  have hJmopen : IsOpen Jm := by rw [hJmd]; exact hI.preimage continuous_neg
  obtain ⟨R, hRd⟩ : ∃ r : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ),
      r = fun ζ => toLp 2 ((ofLp ζ).1, -(ofLp ζ).2) := ⟨_, rfl⟩
  have hR2 : ∀ ζ : WithLp 2 (F × ℝ), (ofLp (R ζ)).2 = -(ofLp ζ).2 := by
    intro ζ; rw [hRd]
  have hpre : ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' Jm)
      = R ⁻¹' ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' I) := by
    rw [hJmd, hRd]
    rfl
  have hTFsub : IsLimitSubOn ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' Jm)
      (TimeFlip f) := by
    rw [hpre, hRd]
    exact hrev2 _ hsuper
  have hTFcont : ContinuousOn (TimeFlip f)
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' Jm) := hTFsub.2.1
  have hTFgrow : SubquadraticGrowth Jm (TimeFlip f) := by
    intro K hKJ hKc ε hε
    have hnegK : (fun σ : ℝ => -σ) '' K ⊆ I := by
      rintro σ ⟨r, hr, rfl⟩
      have hr' := hKJ hr
      rw [hJmd] at hr'
      exact hr'
    obtain ⟨M, hM0, hMb⟩ := hgrow ((fun σ : ℝ => -σ) '' K) hnegK
      (hKc.image continuous_neg) ε hε
    refine ⟨M, hM0, fun ζ hζ hζK => ?_⟩
    have hb := hMb (R ζ) (by rw [hRd]; exact hζ) (by rw [hRd]; exact ⟨(ofLp ζ).2, hζK, rfl⟩)
    simp only [hRd] at hb
    rw [TimeFlip, abs_neg]
    exact hb
  -- the two slope identities under time reversal
  have hidP : ∀ (l : ℝ) (ζ : WithLp 2 (F × ℝ)),
      EnvSlopeP (TimeFlip f) l (R ζ) = EnvSlopeM f l ζ := by
    intro l ζ
    have e1 : QuadEnvP (TimeFlip f) l (R ζ) = -QuadEnvM f l ζ := by
      rw [hrev3 l (R ζ), hRd]
      show -QuadEnvM f l (toLp 2 ((ofLp ζ).1, -(-(ofLp ζ).2))) = -QuadEnvM f l ζ
      rw [neg_neg]
    have e2 : TimeFlip f (R ζ) = -f ζ := by
      rw [TimeFlip, hRd]
      show -f (toLp 2 ((ofLp ζ).1, -(-(ofLp ζ).2))) = -f ζ
      rw [neg_neg]
    rw [EnvSlopeP, EnvSlopeM, e1, e2]
    ring
  have hidM : ∀ (l : ℝ) (ζ : WithLp 2 (F × ℝ)),
      EnvSlopeM (TimeFlip f) l (R ζ) = EnvSlopeP f l ζ := by
    intro l ζ
    have e1 : QuadEnvM (TimeFlip f) l (R ζ) = -QuadEnvP f l ζ := by
      rw [hrev4 l (R ζ), hRd]
      show -QuadEnvP f l (toLp 2 ((ofLp ζ).1, -(-(ofLp ζ).2))) = -QuadEnvP f l ζ
      rw [neg_neg]
    have e2 : TimeFlip f (R ζ) = -f ζ := by
      rw [TimeFlip, hRd]
      show -f (toLp 2 ((ofLp ζ).1, -(-(ofLp ζ).2))) = -f ζ
      rw [neg_neg]
    rw [EnvSlopeM, EnvSlopeP, e1, e2]
    ring
  -- the envelope-slope lemma for `f` and for its time reversal
  have hESO := EnvelopeSlopeOrder I hI f hcont hgrow hsub
  have hESOm := EnvelopeSlopeOrder Jm hJmopen (TimeFlip f) hTFcont hTFgrow hTFsub
  refine ⟨?_, ?_, ?_, ?_⟩
  -- ===================== (1): both slopes are nondecreasing ========================
  · intro z l l' hl hll' hadm
    refine ⟨hESO.1 z l l' hl hll' fun σ hσ => hadm σ ⟨by linarith [hσ.1], hσ.2⟩, ?_⟩
    have hadmR : ∀ σ ∈ Set.Icc (0 : ℝ) l', (ofLp (R z)).2 + σ ∈ Jm := by
      intro σ hσ
      rw [hR2 z, hJmd]
      show -(-(ofLp z).2 + σ) ∈ I
      rw [show -(-(ofLp z).2 + σ) = (ofLp z).2 + -σ from by ring]
      exact hadm (-σ) ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    have hm := hESOm.1 (R z) l l' hl hll' hadmR
    rw [hidP l z, hidP l' z] at hm
    exact hm
  -- ===================== (2): the two infima agree with `H_f` ======================
  · intro z hadm
    have hBdef : EnvHamiltonian f z
        = ⨅ l ∈ Set.Ioi (0 : ℝ), ((EnvSlopeP f l z : ℝ) : EReal) := by
      rw [EnvHamiltonian]
    have hadmR : ∀ (r : ℝ), ∀ σ ∈ Set.Icc (-r) r, (ofLp (R z)).2 + σ ∈ Jm := by
      intro r σ _
      rw [hR2 z, hJmd]
      show -(-(ofLp z).2 + σ) ∈ I
      rw [show -(-(ofLp z).2 + σ) = (ofLp z).2 + -σ from by ring]
      exact hadm (-σ)
    refine le_antisymm ?_ ?_
    · -- `inf S⁻ ≤ inf S⁺`: the cross inequality of EnvelopeSlopeOrder for `f`
      rw [hBdef]
      refine le_iInf fun hh => le_iInf fun hhmem => ?_
      refine hEle (EnvSlopeP f hh z) _ fun ε hε => ?_
      obtain ⟨δ, hδ, hδp⟩ := hESO.2 z hh ε hhmem hε fun σ _ => hadm σ
      have hmin : 0 < min δ 1 := lt_min hδ one_pos
      have hlpos : 0 < min δ 1 / 2 := by linarith
      have hlt : min δ 1 / 2 < δ := by
        have h1 : min δ 1 ≤ δ := min_le_left _ _
        linarith
      calc (⨅ l ∈ Set.Ioi (0 : ℝ), ((EnvSlopeM f l z : ℝ) : EReal))
          ≤ ((EnvSlopeM f (min δ 1 / 2) z : ℝ) : EReal) :=
            hbinf (fun s => EnvSlopeM f s z) _ hlpos
        _ ≤ ((EnvSlopeP f hh z + ε : ℝ) : EReal) :=
            EReal.coe_le_coe (hδp _ hlpos hlt)
    · -- `inf S⁺ ≤ inf S⁻`: the same cross inequality for the time reversal
      rw [hBdef]
      refine le_iInf fun hh => le_iInf fun hhmem => ?_
      refine hEle (EnvSlopeM f hh z) _ fun ε hε => ?_
      obtain ⟨δ, hδ, hδp⟩ := hESOm.2 (R z) hh ε hhmem hε (hadmR hh)
      have hmin : 0 < min δ 1 := lt_min hδ one_pos
      have hlpos : 0 < min δ 1 / 2 := by linarith
      have hlt : min δ 1 / 2 < δ := by
        have h1 : min δ 1 ≤ δ := min_le_left _ _
        linarith
      have hstep := hδp _ hlpos hlt
      rw [hidM _ z, hidP _ z] at hstep
      calc (⨅ l ∈ Set.Ioi (0 : ℝ), ((EnvSlopeP f l z : ℝ) : EReal))
          ≤ ((EnvSlopeP f (min δ 1 / 2) z : ℝ) : EReal) :=
            hbinf (fun s => EnvSlopeP f s z) _ hlpos
        _ ≤ ((EnvSlopeM f hh z + ε : ℝ) : EReal) := EReal.coe_le_coe hstep
  -- ===================== (3): `H_f` never takes the value `+∞` =====================
  -- No admissibility is needed: the infimum is over the NONEMPTY set of positive
  -- lengths, and each `S⁺_l f z` is a real number -- by the preamble's `sup`
  -- convention `P_l f z` is a real number whether or not the competitor set is
  -- bounded above, so no attainment statement is invoked at an inadmissible `z`.
  · intro z htop
    have h1 : EnvHamiltonian f z ≤ ((EnvSlopeP f 1 z : ℝ) : EReal) := by
      rw [EnvHamiltonian]
      exact hbinf (fun s => EnvSlopeP f s z) 1 one_pos
    rw [htop] at h1
    exact EReal.coe_ne_top _ (top_le_iff.mp h1)
  -- ===================== (4): upper semicontinuity =================================
  · intro hall
    obtain ⟨-, -, hattcP, -, -, -⟩ := QuadEnvAttained I hI f hcont hgrow
    have hOopen : IsOpen ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' I) :=
      hI.preimage (continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous)
    -- each fixed forward slope is continuous on the slab, hence upper semicontinuous
    have husc : ∀ l : ℝ, l ∈ Set.Ioi (0 : ℝ) →
        UpperSemicontinuousOn
          (fun ζ : WithLp 2 (F × ℝ) => ((EnvSlopeP f l ζ : ℝ) : EReal))
          ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' I) := by
      intro l hl
      refine ContinuousOn.upperSemicontinuousOn ?_
      refine continuous_coe_real_ereal.comp_continuousOn ?_
      intro ζ hζ
      have hτI : (ofLp ζ).2 ∈ I := hζ
      have hτlI : (ofLp ζ).2 + l ∈ I := hall _ hτI l
      have hcA := hattcP l hl ζ hτI hτlI
      have hmap : ContinuousAt
          (fun ξ : WithLp 2 (F × ℝ) => ((l, ξ) : ℝ × WithLp 2 (F × ℝ))) ζ :=
        (continuous_const.prodMk continuous_id).continuousAt
      have hQA : ContinuousAt (fun ξ : WithLp 2 (F × ℝ) => QuadEnvP f l ξ) ζ :=
        Filter.Tendsto.comp hcA hmap
      have hfA : ContinuousAt f ζ := hcont.continuousAt (hOopen.mem_nhds hτI)
      have hdiv : ContinuousAt
          (fun ξ : WithLp 2 (F × ℝ) => (QuadEnvP f l ξ - f ξ) / l) ζ :=
        (hQA.sub hfA).div_const l
      exact hdiv.continuousWithinAt
    have hH : EnvHamiltonian f = fun ζ : WithLp 2 (F × ℝ) =>
        ⨅ l ∈ Set.Ioi (0 : ℝ), ((EnvSlopeP f l ζ : ℝ) : EReal) := by
      funext ζ; rw [EnvHamiltonian]
    rw [hH]
    exact upperSemicontinuousOn_biInf fun l hl => husc l hl
