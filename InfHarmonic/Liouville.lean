module

public import InfHarmonic.EnvelopeContact
public import InfHarmonic.ContactPropagation
public import InfHarmonic.FrameEnvelopeCovariance
public import InfHarmonic.FrameGapCovariance
public import InfHarmonic.ClassCompactness
public import InfHarmonic.QuadEnvStability
public import InfHarmonic.BaryEnvStability
public import InfHarmonic.SlopeRigidity
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.EnvHamiltonianSolution

@[expose] public section
open Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Theorem 3.1 (Liouville Theorem): every member of the class `A_{m,C₀}` is
affine on space-time. The constant is universally quantified with `0 ≤ C₀`, as
in the paper; no centering and no Jensen bound are assumed, both being produced
inside the proof. -/
theorem Liouville (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : IsFitClass C₀ v) : IsSpaceTimeAffine v := by
  classical
  -- ===========================================================================
  -- THE WHOLE PROOF IS BY CONTRADICTION: assume `v` is not affine and derive a
  -- contradiction from the extremal contact pair it produces.
  -- ===========================================================================
  by_contra hna
  -- ===== Step 0: we may assume the constant is at least one =====
  obtain ⟨C₁, hC₁def⟩ : ∃ c : ℝ, c = max C₀ 1 := ⟨_, rfl⟩
  have hC₁ : 1 ≤ C₁ := by rw [hC₁def]; exact le_max_right _ _
  have hC₀C₁ : C₀ ≤ C₁ := by rw [hC₁def]; exact le_max_left _ _
  have hvC₁ : IsFitClass C₁ v := by
    refine ⟨hv.1, ?_⟩
    intro z R hR
    obtain ⟨p, a, hfit⟩ := hv.2 z R hR
    refine ⟨p, a, ?_⟩
    intro h l hl hhl
    exact le_trans (hfit h l hl hhl) (mul_le_mul_of_nonneg_right hC₀C₁ hR.le)
  -- ===== Step 1: the extremal contact pair =====
  obtain ⟨κ, H, u, hκ0, huclass, hucent, huJ, hWcont, hWgrow, hWsub, hsand, hW0, hu0,
    hconc, hgap, hham, hslope⟩ := EnvelopeContact C₁ hC₁ v hvC₁ hna
  -- ===== Step 2: the terminal point, the levels and the contacts with fits =====
  obtain ⟨Kb, xend, Jset, hKb0, hJinf, -, hHend, hJdata⟩ :=
    ContactPropagation C₁ κ H hC₁ hκ0 u huclass hucent huJ hWcont hWgrow hWsub hsand
      hW0 hu0 hconc hgap hham hslope
  choose jj hjjmem hjjgt using fun k : ℕ => hJinf.exists_gt k
  have hjjge : ∀ k : ℕ, k ≤ jj k := fun k => (hjjgt k).le
  choose ξ q α hfit0 hcon0 hdist0 using fun k : ℕ => hJdata (jj k) (hjjmem k)
  obtain ⟨rr, hrr⟩ : ∃ f : ℕ → ℝ, ∀ k, f k = (1 / 2 : ℝ) ^ jj k := ⟨_, fun _ => rfl⟩
  have hrrpos : ∀ k, 0 < rr k := by
    intro k
    rw [hrr k]
    exact pow_pos (by norm_num) _
  have hrrle : ∀ k, rr k ≤ (1 / 2 : ℝ) ^ k := by
    intro k
    rw [hrr k]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (hjjge k)
  have hrrtend : Tendsto rr atTop (𝓝 (0 : ℝ)) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun k => (hrrpos k).le) hrrle
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hfitk : ∀ k, IsFit C₁ u (toLp 2 (ξ k, rr k)) (rr k) (q k) (α k) := by
    intro k
    rw [hrr k]
    exact hfit0 k
  have hcontactk : ∀ k, ContactEnv u κ (toLp 2 (ξ k, rr k)) = u (toLp 2 (ξ k, rr k)) := by
    intro k
    rw [hrr k]
    exact hcon0 k
  have hdistk : ∀ k, ‖xend - ξ k + (rr k) • q k‖ ≤ Kb * rr k := by
    intro k
    rw [hrr k]
    exact hdist0 k
  -- ===== Step 3: the fitted frames =====
  obtain ⟨vb, hvb⟩ : ∃ f : ℕ → WithLp 2 (F × ℝ) → ℝ, ∀ k, f k = fun ζ =>
      FrameChange u (toLp 2 (ξ k, rr k)) (rr k) (q k) (α k)
        (ζ - toLp 2 ((0 : F), (1 : ℝ))) := ⟨_, fun _ => rfl⟩
  have hFEC : ∀ k, IsFitClass C₁ (vb k)
      ∧ IsCenteredAt C₁ (vb k) (toLp 2 ((0 : F), (1 : ℝ)))
      ∧ HasJensenBound Set.univ (vb k) κ
      ∧ (∀ (l : ℝ) (ζ : WithLp 2 (F × ℝ)), 0 < l →
          EnvSlopeP (vb k) l ζ
            = EnvSlopeP u (rr k * l)
                (toLp 2 (ξ k + (rr k) • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • q k),
                  rr k * (ofLp ζ).2)) - α k ∧
          EnvSlopeM (vb k) l ζ
            = EnvSlopeM u (rr k * l)
                (toLp 2 (ξ k + (rr k) • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • q k),
                  rr k * (ofLp ζ).2)) - α k) := by
    intro k
    rw [hvb k]
    exact FrameEnvelopeCovariance C₁ κ hC₁ hκ0.le u huclass huJ (rr k) (hrrpos k)
      (ξ k) (q k) (α k) (hfitk k)
  have hFGC : ∀ k, (∀ (σ : ℝ) (ζ : WithLp 2 (F × ℝ)), 0 < σ →
      BaryEnv (vb k) σ ζ - vb k ζ
        = (BaryEnv u (rr k * σ)
              (toLp 2 (ξ k + (rr k) • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • q k),
                rr k * (ofLp ζ).2))
            - u (toLp 2 (ξ k + (rr k) • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • q k),
                rr k * (ofLp ζ).2))) / rr k) := by
    intro k
    rw [hvb k]
    exact (FrameGapCovariance C₁ κ hC₁ hκ0.le u huclass huJ (rr k) (hrrpos k)
      (ξ k) (q k) (α k) (hfitk k)).1
  obtain ⟨bb, hbb⟩ : ∃ f : ℕ → F, ∀ k, f k = (rr k)⁻¹ • (xend - ξ k + (rr k) • q k) :=
    ⟨_, fun _ => rfl⟩
  have hbbnorm : ∀ k, ‖bb k‖ ≤ Kb := by
    intro k
    rw [hbb k, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (hrrpos k)]
    rw [inv_mul_le_iff₀ (hrrpos k)]
    calc ‖xend - ξ k + (rr k) • q k‖ ≤ Kb * rr k := hdistk k
      _ = rr k * Kb := by ring
  -- the point `(bb k, 0)` is the one that corresponds to `(xend, 0)` in frame `k`
  have hcorr : ∀ k, ξ k + (rr k) • ((ofLp (toLp 2 (bb k, (0 : ℝ)) : WithLp 2 (F × ℝ))).1
        + ((ofLp (toLp 2 (bb k, (0 : ℝ)) : WithLp 2 (F × ℝ))).2 - 1) • q k) = xend := by
    intro k
    have h1 : (ofLp (toLp 2 (bb k, (0 : ℝ)) : WithLp 2 (F × ℝ))).1 = bb k := rfl
    have h2 : (ofLp (toLp 2 (bb k, (0 : ℝ)) : WithLp 2 (F × ℝ))).2 = (0 : ℝ) := rfl
    rw [h1, h2, hbb k, smul_add, smul_smul, mul_inv_cancel₀ (ne_of_gt (hrrpos k)), one_smul]
    rw [show ((0 : ℝ) - 1) • q k = -q k from by module]
    rw [smul_neg]
    abel
  -- ===== Step 4: one limit function and one limit point =====
  have hballcpt : IsCompact (Metric.closedBall (0 : F) Kb) := isCompact_closedBall 0 Kb
  obtain ⟨bL, hbLmem, φ, hφmono, hbφ⟩ :=
    hballcpt.tendsto_subseq (x := bb) (fun k => by
      simp only [Metric.mem_closedBall, dist_zero_right]
      exact hbbnorm k)
  obtain ⟨ι, vinf, hιmono, hunif0, hvinfclass, hvinfcent⟩ :=
    ClassCompactness C₁ hC₁ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl)
      (fun k => vb (φ k)) (fun k => (hFEC (φ k)).1) (fun k => (hFEC (φ k)).2.1)
  obtain ⟨ψ, hψ⟩ : ∃ f : ℕ → ℕ, ∀ k, f k = φ (ι k) := ⟨_, fun _ => rfl⟩
  have hψmono : StrictMono ψ := by
    intro a b hab
    rw [hψ a, hψ b]
    exact hφmono (hιmono hab)
  have hunif : ∀ Kc : Set (WithLp 2 (F × ℝ)), IsCompact Kc →
      TendstoUniformlyOn (fun k => vb (ψ k)) vinf atTop Kc := by
    intro Kc hKc
    have h := hunif0 Kc hKc
    simpa only [hψ] using h
  have hbψ : Tendsto (fun k => bb (ψ k)) atTop (𝓝 bL) := by
    have h := hbφ.comp hιmono.tendsto_atTop
    simpa only [hψ, Function.comp_def] using h
  have hrrψ : Tendsto (fun k => rr (ψ k)) atTop (𝓝 (0 : ℝ)) :=
    hrrtend.comp hψmono.tendsto_atTop
  have hbLnorm : ‖bL‖ ≤ Kb := by
    have h := hbLmem
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hvinf0 : vinf (toLp 2 ((0 : F), (1 : ℝ))) = 0 := hvinfcent.1
  -- ===== Step 5: the two growth hypotheses the stability lemmas need =====
  have hsubq : ∀ g : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₁ g →
      IsCenteredAt C₁ g (toLp 2 ((0 : F), (1 : ℝ))) →
      SubquadraticGrowth (Set.univ : Set ℝ) g := by
    intro g hgc hgcent J _ hJc ε hε
    obtain ⟨M, hM0, hMbd⟩ :=
      UniformSubquadratic C₁ hC₁ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc ε hε
    exact ⟨M, hM0, fun z h1 h2 => hMbd g hgc hgcent z h1 h2⟩
  have hvinfgrow : SubquadraticGrowth (Set.univ : Set ℝ) vinf :=
    hsubq vinf hvinfclass hvinfcent
  have hvinfcont : ContinuousOn vinf
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hvinfclass.1.1.2.1
  have hvbcont : ∀ k, ContinuousOn (vb (ψ k))
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    intro k
    simpa using (hFEC (ψ k)).1.1.1.2.1
  have hunifgrow : UnifSubquadraticGrowth (Set.univ : Set ℝ) (fun k => vb (ψ k)) := by
    intro J _ hJc ε hε
    obtain ⟨M, hM0, hMbd⟩ :=
      UniformSubquadratic C₁ hC₁ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc ε hε
    exact ⟨M, hM0, fun k z h1 h2 =>
      hMbd (vb (ψ k)) (hFEC (ψ k)).1 (hFEC (ψ k)).2.1 z h1 h2⟩
  have hconvall : ∀ Kc ⊆ ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ),
      IsCompact Kc → TendstoUniformlyOn (fun k => vb (ψ k)) vinf atTop Kc :=
    fun Kc _ hKc => hunif Kc hKc
  have hQS : ∀ l : ℝ, 0 < l →
      (∀ Kc : Set (WithLp 2 (F × ℝ)), IsCompact Kc →
          TendstoUniformlyOn (fun k => QuadEnvP (vb (ψ k)) l) (QuadEnvP vinf l) atTop Kc) ∧
      (∀ Kc : Set (WithLp 2 (F × ℝ)), IsCompact Kc →
          TendstoUniformlyOn (fun k => QuadEnvM (vb (ψ k)) l) (QuadEnvM vinf l)
            atTop Kc) := by
    intro l hl
    obtain ⟨h1, h2⟩ := QuadEnvStability Set.univ isOpen_univ vinf (fun k => vb (ψ k))
      hvinfcont hvbcont hconvall hunifgrow hvinfgrow l hl
    exact ⟨fun Kc hKc => h1 Kc hKc (fun z _ => ⟨Set.mem_univ _, Set.mem_univ _⟩),
      fun Kc hKc => h2 Kc hKc (fun z _ => ⟨Set.mem_univ _, Set.mem_univ _⟩)⟩
  have hBS : ∀ Kc : Set (WithLp 2 (F × ℝ)), IsCompact Kc →
      TendstoUniformlyOn (fun k => BaryEnv (vb (ψ k)) 1) (BaryEnv vinf 1) atTop Kc :=
    fun Kc hKc => BaryEnvStability Set.univ isOpen_univ vinf (fun k => vb (ψ k))
      hvinfcont hvbcont hconvall hunifgrow hvinfgrow 1 one_pos Kc hKc
      (fun z _ => Set.mem_univ _)
  obtain ⟨hQA1, -, hQA3, hQA4, -, -⟩ :=
    QuadEnvAttained Set.univ isOpen_univ vinf hvinfcont hvinfgrow
  -- ===== Step 6: evaluation along the moving points =====
  obtain ⟨Cpt, hCpt⟩ : ∃ S : Set (WithLp 2 (F × ℝ)),
      S = (fun x : F => (toLp 2 (x, (0 : ℝ)) : WithLp 2 (F × ℝ))) ''
        Metric.closedBall (0 : F) Kb := ⟨_, rfl⟩
  have htoLpcont : Continuous (fun x : F => (toLp 2 (x, (0 : ℝ)) : WithLp 2 (F × ℝ))) := by
    fun_prop
  have hCptcpt : IsCompact Cpt := by
    rw [hCpt]
    exact hballcpt.image htoLpcont
  have hCptmem : ∀ k, (toLp 2 (bb (ψ k), (0 : ℝ)) : WithLp 2 (F × ℝ)) ∈ Cpt := by
    intro k
    rw [hCpt]
    exact ⟨bb (ψ k), by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hbbnorm (ψ k), rfl⟩
  have hCptmemL : (toLp 2 (bL, (0 : ℝ)) : WithLp 2 (F × ℝ)) ∈ Cpt := by
    rw [hCpt]
    exact ⟨bL, by simpa only [Metric.mem_closedBall, dist_zero_right] using hbLnorm, rfl⟩
  have hptend : Tendsto (fun k => (toLp 2 (bb (ψ k), (0 : ℝ)) : WithLp 2 (F × ℝ)))
      atTop (𝓝[Cpt] (toLp 2 (bL, (0 : ℝ)))) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall hCptmem)
    exact (htoLpcont.tendsto bL).comp hbψ
  have heval : ∀ (gs : ℕ → WithLp 2 (F × ℝ) → ℝ) (g : WithLp 2 (F × ℝ) → ℝ),
      (∀ Kc : Set (WithLp 2 (F × ℝ)), IsCompact Kc → TendstoUniformlyOn gs g atTop Kc) →
      ContinuousWithinAt g Cpt (toLp 2 (bL, (0 : ℝ))) →
      Tendsto (fun k => gs k (toLp 2 (bb (ψ k), (0 : ℝ)))) atTop
        (𝓝 (g (toLp 2 (bL, (0 : ℝ))))) :=
    fun gs g hgs hcw => (hgs Cpt hCptcpt).tendsto_comp hcw hptend
  have hcontV : ContinuousWithinAt vinf Cpt (toLp 2 (bL, (0 : ℝ))) :=
    (hvinfclass.1.1.2.1.mono (Set.subset_univ Cpt)) _ hCptmemL
  have hcontQP : ∀ l : ℝ, 0 < l →
      ContinuousWithinAt (QuadEnvP vinf l) Cpt (toLp 2 (bL, (0 : ℝ))) := by
    intro l hl
    refine ContinuousAt.continuousWithinAt ?_
    have h1 := hQA3 l hl (toLp 2 (bL, (0 : ℝ))) (Set.mem_univ _) (Set.mem_univ _)
    have h2 : Continuous (fun z : WithLp 2 (F × ℝ) => (l, z)) := by fun_prop
    have h := Filter.Tendsto.comp h1 (h2.continuousAt (x := toLp 2 (bL, (0 : ℝ))))
    exact h
  have hcontQM : ∀ l : ℝ, 0 < l →
      ContinuousWithinAt (QuadEnvM vinf l) Cpt (toLp 2 (bL, (0 : ℝ))) := by
    intro l hl
    refine ContinuousAt.continuousWithinAt ?_
    have h1 := hQA4 l hl (toLp 2 (bL, (0 : ℝ))) (Set.mem_univ _) (Set.mem_univ _)
    have h2 : Continuous (fun z : WithLp 2 (F × ℝ) => (l, z)) := by fun_prop
    have h := Filter.Tendsto.comp h1 (h2.continuousAt (x := toLp 2 (bL, (0 : ℝ))))
    exact h
  have hslopePlim : ∀ l : ℝ, 0 < l →
      Tendsto (fun k => EnvSlopeP (vb (ψ k)) l (toLp 2 (bb (ψ k), (0 : ℝ)))) atTop
        (𝓝 (EnvSlopeP vinf l (toLp 2 (bL, (0 : ℝ))))) := by
    intro l hl
    have hQ := heval (fun k => QuadEnvP (vb (ψ k)) l) (QuadEnvP vinf l) (hQS l hl).1
      (hcontQP l hl)
    have hV := heval (fun k => vb (ψ k)) vinf hunif hcontV
    have h := (hQ.sub hV).div_const l
    simpa only [EnvSlopeP] using h
  have hslopeMlim : ∀ l : ℝ, 0 < l →
      Tendsto (fun k => EnvSlopeM (vb (ψ k)) l (toLp 2 (bb (ψ k), (0 : ℝ)))) atTop
        (𝓝 (EnvSlopeM vinf l (toLp 2 (bL, (0 : ℝ))))) := by
    intro l hl
    have hQ := heval (fun k => QuadEnvM (vb (ψ k)) l) (QuadEnvM vinf l) (hQS l hl).2
      (hcontQM l hl)
    have hV := heval (fun k => vb (ψ k)) vinf hunif hcontV
    have h := (hV.sub hQ).div_const l
    simpa only [EnvSlopeM] using h
  -- ===== Step 7: the shifts cancel and the limiting slopes are constant =====
  have hugrow : SubquadraticGrowth (Set.univ : Set ℝ) u := hsubq u huclass hucent
  have hucont : ContinuousOn u
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using huclass.1.1.2.1
  have husol : IsLimitSolutionOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) u := by
    rw [Set.preimage_univ]
    exact huclass.1
  obtain ⟨hEHS1, hEHS2, hEHS3, -⟩ :=
    EnvHamiltonianSolution Set.univ isOpen_univ u hucont hugrow husol
  obtain ⟨Hs, hHseq⟩ : ∃ r : ℝ,
      EnvHamiltonian u (toLp 2 (xend, (0 : ℝ))) = (r : EReal) :=
    ⟨_, (EReal.coe_toReal (hEHS3 _) hHend.ne').symm⟩
  -- a nondecreasing real family whose EReal infimum is finite tends to that infimum
  have hmonoinf : ∀ (S : ℝ → ℝ) (Hs' : ℝ),
      (∀ l l' : ℝ, 0 < l → l ≤ l' → S l ≤ S l') →
      (⨅ l ∈ Set.Ioi (0 : ℝ), ((S l : ℝ) : EReal)) = (Hs' : EReal) →
      Tendsto S (𝓝[>] (0 : ℝ)) (𝓝 Hs') := by
    intro S Hs' hmono hinf
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      refine eventually_nhdsWithin_of_forall ?_
      intro x hx
      have h1 : (⨅ l ∈ Set.Ioi (0 : ℝ), ((S l : ℝ) : EReal)) ≤ ((S x : ℝ) : EReal) :=
        iInf₂_le x hx
      rw [hinf] at h1
      exact lt_of_lt_of_le ha (EReal.coe_le_coe_iff.mp h1)
    · intro a ha
      obtain ⟨l, hl0, hlb⟩ : ∃ l : ℝ, 0 < l ∧ S l < a := by
        by_contra hcon
        push Not at hcon
        have h2 : ((a : ℝ) : EReal) ≤ (⨅ l ∈ Set.Ioi (0 : ℝ), ((S l : ℝ) : EReal)) := by
          refine le_iInf₂_iff.mpr ?_
          intro l hl
          exact EReal.coe_le_coe_iff.mpr (hcon l hl)
        rw [hinf] at h2
        have h3 := EReal.coe_le_coe_iff.mp h2
        linarith
      filter_upwards [Ioo_mem_nhdsGT hl0] with x hx
      exact lt_of_le_of_lt (hmono x l hx.1 (le_of_lt hx.2)) hlb
  have htendP : Tendsto (fun l => EnvSlopeP u l (toLp 2 (xend, (0 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 Hs) := by
    refine hmonoinf _ Hs (fun l l' hl hll' =>
      (hEHS1 _ l l' hl hll' (fun σ _ => Set.mem_univ _)).1) ?_
    rw [← hHseq, EnvHamiltonian]
  have htendM : Tendsto (fun l => EnvSlopeM u l (toLp 2 (xend, (0 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 Hs) := by
    refine hmonoinf _ Hs (fun l l' hl hll' =>
      (hEHS1 _ l l' hl hll' (fun σ _ => Set.mem_univ _)).2) ?_
    rw [hEHS2 _ (fun _ => Set.mem_univ _)]
    exact hHseq
  have hrrl : ∀ l : ℝ, 0 < l → Tendsto (fun k => rr (ψ k) * l) atTop (𝓝[>] (0 : ℝ)) := by
    intro l hl
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
      (Filter.Eventually.of_forall
        (fun k => Set.mem_Ioi.mpr (mul_pos (hrrpos (ψ k)) hl)))
    simpa using hrrψ.mul_const l
  have hRP : ∀ l : ℝ, 0 < l →
      Tendsto (fun k => EnvSlopeP u (rr (ψ k) * l) (toLp 2 (xend, (0 : ℝ)))) atTop
        (𝓝 Hs) := fun l hl => htendP.comp (hrrl l hl)
  have hRM : ∀ l : ℝ, 0 < l →
      Tendsto (fun k => EnvSlopeM u (rr (ψ k) * l) (toLp 2 (xend, (0 : ℝ)))) atTop
        (𝓝 Hs) := fun l hl => htendM.comp (hrrl l hl)
  have htime : ∀ k, rr k * (ofLp (toLp 2 (bb k, (0 : ℝ)) : WithLp 2 (F × ℝ))).2
      = (0 : ℝ) := by
    intro k
    show rr k * (0 : ℝ) = 0
    ring
  have hcovP : ∀ (k : ℕ) (l : ℝ), 0 < l →
      EnvSlopeP (vb k) l (toLp 2 (bb k, (0 : ℝ)))
        = EnvSlopeP u (rr k * l) (toLp 2 (xend, (0 : ℝ))) - α k := by
    intro k l hl
    have h := ((hFEC k).2.2.2 l (toLp 2 (bb k, (0 : ℝ))) hl).1
    rw [hcorr k, htime k] at h
    exact h
  have hcovM : ∀ (k : ℕ) (l : ℝ), 0 < l →
      EnvSlopeM (vb k) l (toLp 2 (bb k, (0 : ℝ)))
        = EnvSlopeM u (rr k * l) (toLp 2 (xend, (0 : ℝ))) - α k := by
    intro k l hl
    have h := ((hFEC k).2.2.2 l (toLp 2 (bb k, (0 : ℝ))) hl).2
    rw [hcorr k, htime k] at h
    exact h
  have hB : ∀ l : ℝ, 0 < l →
      EnvSlopeP vinf l (toLp 2 (bL, (0 : ℝ)))
          = EnvSlopeP vinf 1 (toLp 2 (bL, (0 : ℝ)))
        ∧ EnvSlopeM vinf l (toLp 2 (bL, (0 : ℝ)))
          = EnvSlopeP vinf 1 (toLp 2 (bL, (0 : ℝ))) := by
    intro l hl
    constructor
    · have h1 := (hslopePlim l hl).sub (hslopePlim 1 one_pos)
      have h3 := (hRP l hl).sub (hRP 1 one_pos)
      rw [sub_self] at h3
      have h2 : Tendsto (fun k => EnvSlopeP (vb (ψ k)) l (toLp 2 (bb (ψ k), (0 : ℝ)))
            - EnvSlopeP (vb (ψ k)) 1 (toLp 2 (bb (ψ k), (0 : ℝ)))) atTop (𝓝 (0 : ℝ)) := by
        refine h3.congr (fun k => ?_)
        rw [hcovP (ψ k) l hl, hcovP (ψ k) 1 one_pos]
        ring
      have h := tendsto_nhds_unique h1 h2
      linarith
    · have h1 := (hslopeMlim l hl).sub (hslopePlim 1 one_pos)
      have h3 := (hRM l hl).sub (hRP 1 one_pos)
      rw [sub_self] at h3
      have h2 : Tendsto (fun k => EnvSlopeM (vb (ψ k)) l (toLp 2 (bb (ψ k), (0 : ℝ)))
            - EnvSlopeP (vb (ψ k)) 1 (toLp 2 (bb (ψ k), (0 : ℝ)))) atTop (𝓝 (0 : ℝ)) := by
        refine h3.congr (fun k => ?_)
        rw [hcovM (ψ k) l hl, hcovP (ψ k) 1 one_pos]
        ring
      have h := tendsto_nhds_unique h1 h2
      linarith
  -- ===== Step 8: the limit is affine =====
  have hvinfaff : IsSpaceTimeAffine vinf :=
    SlopeRigidity C₁ hC₁ vinf hvinfclass bL 0 (EnvSlopeP vinf 1 (toLp 2 (bL, (0 : ℝ))))
      (fun l hl => hB l hl)
  -- ===== Step 9: the contacts keep a positive envelope gap in the limit =====
  have hz1 : (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1 = (0 : F) := rfl
  have hz2 : (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 = (1 : ℝ) := rfl
  have hgapk : ∀ k, BaryEnv (vb k) 1 (toLp 2 ((0 : F), (1 : ℝ))) = κ ^ 2 / 2 := by
    intro k
    have hpt : ξ k + (rr k) • ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1
        + ((ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 - 1) • q k) = ξ k := by
      rw [hz1, hz2, show ((1 : ℝ) - 1) • q k = (0 : F) from by module, add_zero,
        smul_zero, add_zero]
    have htm : rr k * (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 = rr k := by
      rw [hz2]
      ring
    have h := hFGC k 1 (toLp 2 ((0 : F), (1 : ℝ))) one_pos
    rw [hpt, htm] at h
    have hzz : (ofLp (toLp 2 (ξ k, rr k) : WithLp 2 (F × ℝ))).2 = rr k := rfl
    have hg := hgap (toLp 2 (ξ k, rr k)) (by rw [hzz]; exact hrrpos k) (hcontactk k)
    rw [hzz] at hg
    rw [hg, (hFEC k).2.1.1] at h
    linarith
  have hgaplimit : BaryEnv vinf 1 (toLp 2 ((0 : F), (1 : ℝ))) = κ ^ 2 / 2 := by
    have h := (hBS ({toLp 2 ((0 : F), (1 : ℝ))} : Set (WithLp 2 (F × ℝ)))
      isCompact_singleton).tendsto_at rfl
    have hconst : Tendsto (fun k : ℕ => BaryEnv (vb (ψ k)) 1 (toLp 2 ((0 : F), (1 : ℝ))))
        atTop (𝓝 (κ ^ 2 / 2)) :=
      tendsto_const_nhds.congr (fun k => (hgapk (ψ k)).symm)
    exact tendsto_nhds_unique h hconst
  -- ===== Step 10: an affine function has no barycentric gap, and the contradiction =====
  obtain ⟨ρ, β, cc, hvinfform⟩ := hvinfaff
  have hbaryaff : ∀ z : WithLp 2 (F × ℝ), BaryEnv vinf 1 z = vinf z := by
    intro z
    rw [BaryEnv]
    refine IsGreatest.csSup_eq ⟨?_, ?_⟩
    · refine ⟨1, fun _ => (1 : ℝ), fun _ => (ofLp z).1,
        ⟨fun _ => one_pos, by simp, by simp⟩, ?_⟩
      have hrad : BaryRadius 1 (fun _ => (1 : ℝ)) (fun _ => (ofLp z).1) (ofLp z).1 = 0 := by
        rw [BaryRadius]
        simp
      have hzz : (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := rfl
      rw [hrad, Fin.sum_univ_one, hzz]
      norm_num
    · rintro w ⟨n, θ, y, hcfg, rfl⟩
      have hsum : (∑ i, θ i * vinf (toLp 2 (y i, (ofLp z).2))) = vinf z := by
        have hstep : ∀ i : Fin n, θ i * vinf (toLp 2 (y i, (ofLp z).2))
            = θ i * inner ℝ ρ (y i) + θ i * (β * (ofLp z).2 + cc) := by
          intro i
          have h1 : (ofLp (toLp 2 (y i, (ofLp z).2) : WithLp 2 (F × ℝ))).1 = y i := rfl
          have h2 : (ofLp (toLp 2 (y i, (ofLp z).2) : WithLp 2 (F × ℝ))).2
              = (ofLp z).2 := rfl
          rw [hvinfform, h1, h2]
          ring
        rw [Finset.sum_congr rfl (fun i _ => hstep i), Finset.sum_add_distrib]
        have hA : (∑ i, θ i * inner ℝ ρ (y i)) = inner ℝ ρ (∑ i, θ i • y i) := by
          rw [inner_sum]
          exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_smul_right])
        rw [hA, hcfg.2.2, ← Finset.sum_mul, hcfg.2.1, one_mul, hvinfform]
        ring
      rw [hsum]
      have hnn : (0 : ℝ) ≤ BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * 1) :=
        div_nonneg (sq_nonneg _) (by norm_num)
      linarith
  have hfinal := hbaryaff (toLp 2 ((0 : F), (1 : ℝ)))
  rw [hgaplimit, hvinf0] at hfinal
  have hpos : (0 : ℝ) < κ ^ 2 / 2 := div_pos (pow_pos hκ0 2) two_pos
  linarith
