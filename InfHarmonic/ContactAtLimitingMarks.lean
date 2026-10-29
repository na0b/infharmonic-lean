import InfHarmonic.JGap
set_option maxHeartbeats 500000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 9 of paper Proposition 6.8: under the limiting law, almost every state
has a contact of `v` with its contact envelope at every one of its marks.

The walk family enters only through the data listed below, and the compact
state space of Step 3 only as an abstract topological measurable space `St`
with a mark map `mk`. Concretely: `lam k` are the laws of the pre-limit states
on `St`, pushed forward from the walk spaces `Ωf k` by `Ψ k`; `lam (ns h)`
converges weakly to `lmt`; `Acl j` are the closed level-and-fit events, of full
limiting mass; `mk q j` is the `j`-th mark point of the state `q`, continuous in
`q`; and the pre-limit walks satisfy a uniform upper bound `UB` for the gap
`J_ε` on the compact box `Bx` together with the averaged lower bound `H - 1`
along the marks (`hmean`). The contact-gap limit of \noderef{ContactGapLimit}
enters as `hgap2`.

The argument is the paper's. If the defect `v - W` were larger than `1/(n+1)`
on a set of positive limiting mass, that set would sit inside an open set `O`
of positive mass on which the defect exceeds `α = 1/(2(n+1))` and the time is
bounded below, so the mark points of `O` lie in a compact set `Kc` on which
`hgap2` forces `J_ε ≤ -α/(4ε)` for all small `ε`. Weak convergence transfers a
positive fraction of that mass to `lam (ns h)` for large `h`, hence to the walk
space by `hpush`; averaging the pointwise bound there contradicts `H - 1 ≤ ∫
J_ε` once `εf (ns h)` is small enough. So every defect level is null, and the
sandwich `W ≤ v` closes the contact. -/
theorem ContactAtLimitingMarks (v : WithLp 2 (F × ℝ) → ℝ) (κ H UB : ℝ)
    (hvcont : Continuous v)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWle : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z ≤ v z)
    (hgap2 : ∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K → (∀ z ∈ K, 0 < (ofLp z).2) →
      ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ z ∈ K,
        |2 * ε * JGap v κ ε z - (ContactEnv v κ z - v z)| ≤ δ)
    (Bx : Set (WithLp 2 (F × ℝ))) (hBxcpt : IsCompact Bx)
    (hUB : ∀ z ∈ Bx, 0 < (ofLp z).2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → JGap v κ ε z ≤ UB)
    {St : Type*} [TopologicalSpace St] [MeasurableSpace St] [OpensMeasurableSpace St]
    [HasOuterApproxClosed St]
    (mk : St → ℕ → WithLp 2 (F × ℝ))
    (hmkcont : ∀ j : ℕ, Continuous fun q : St => mk q j)
    (lmt : ProbabilityMeasure St) (lam : ℕ → ProbabilityMeasure St) (ns : ℕ → ℕ)
    (hns : ∀ h : ℕ, h ≤ ns h)
    (hnstend : Tendsto (fun h => lam (ns h)) atTop (𝓝 lmt))
    (Acl : ℕ → Set St) (hAclosed : ∀ j : ℕ, IsClosed (Acl j))
    (hAlmt : ∀ j : ℕ, 1 ≤ j → (lmt : Measure St) (Acl j) = 1)
    (hAtimeAll : ∀ (j : ℕ) (q : St), q ∈ Acl j → (1 / 2 : ℝ) ^ j ≤ (ofLp (mk q j)).2)
    {Ωf : ℕ → Type} [m0f : ∀ k : ℕ, MeasurableSpace (Ωf k)]
    (μf : ∀ k : ℕ, Measure (Ωf k)) (hprob : ∀ k : ℕ, IsProbabilityMeasure (μf k))
    (Ψ : ∀ k : ℕ, Ωf k → St) (hΨm : ∀ k : ℕ, Measurable (Ψ k))
    (hpush : ∀ (k : ℕ) (A : Set St), MeasurableSet A →
      (lam k : Measure St) A = μf k (Ψ k ⁻¹' A))
    (zf : ∀ k : ℕ, ℕ → Ωf k → WithLp 2 (F × ℝ)) (smarkf : ∀ k : ℕ, ℕ → Ωf k → ℕ)
    (εf : ℕ → ℝ) (hεpos : ∀ k : ℕ, 0 < εf k)
    (hεsmall : ∀ k : ℕ, εf k ≤ (1 / 2 : ℝ) ^ (k + 1) / 4)
    (htpos : ∀ (k n : ℕ) (ω : Ωf k), 0 < (ofLp (zf k n ω)).2)
    (hmkpush : ∀ (k j : ℕ) (ω : Ωf k), 1 ≤ j → j ≤ k + 1 →
      mk (Ψ k ω) j = zf k (smarkf k j ω) ω)
    (hmkBx : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 → ∀ ω : Ωf k,
      zf k (smarkf k j ω) ω ∈ Bx)
    (hmean : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 →
      Integrable (fun ω => JGap v κ (εf k) (zf k (smarkf k j ω) ω)) (μf k) ∧
      H - 1 ≤ ∫ ω, JGap v κ (εf k) (zf k (smarkf k j ω) ω) ∂(μf k)) :
    ∀ᵐ q ∂(lmt : Measure St), ∀ j : ℕ, 1 ≤ j →
      ContactEnv v κ (mk q j) = v (mk q j) := by
  have hdivtrick : ∀ (x e a : ℝ), 0 < e → 0 < a → (4 * e) * x ≤ -a →
      x ≤ -(a / (4 * e)) := by
    intro x e a he ha hx
    have h5 : (0 : ℝ) < 4 * e := by linarith only [he]
    have h6 := mul_le_mul_of_nonneg_left hx (le_of_lt (inv_pos.mpr h5))
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt h5), one_mul] at h6
    calc x ≤ (4 * e)⁻¹ * (-a) := h6
      _ = -(a / (4 * e)) := by field_simp
  have hlmtprob : IsProbabilityMeasure (lmt : Measure St) := lmt.2
  have hmktime : ∀ i : ℕ, Continuous fun q : St => (ofLp (mk q i)).2 :=
    fun i => (by fun_prop : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).2).comp
      (hmkcont i)
  rw [MeasureTheory.ae_all_iff]
  intro j
  by_cases hj : 1 ≤ j
  swap
  · exact Filter.Eventually.of_forall (fun q hjj => absurd hjj hj)
  -- the j-th level set has full measure, so `v - W ≥ 0` almost surely there
  have hAfull : (lmt : Measure St) (Acl j)ᶜ = 0 := by
    rw [prob_compl_eq_one_sub (hAclosed j).measurableSet, hAlmt j hj]
    simp
  have hδj : (0 : ℝ) < (1 / 2 : ℝ) ^ j := by positivity
  have hAtime : ∀ q ∈ Acl j, (1 / 2 : ℝ) ^ j ≤ (ofLp (mk q j)).2 :=
    fun q hq => hAtimeAll j q hq
  -- the bad set is a countable union, so it is enough to kill each piece
  have hzero : ∀ n : ℕ, (lmt : Measure St)
      {q : St | (1 : ℝ) / (n + 1) <
        v (mk q j) - ContactEnv v κ (mk q j)} = 0 := by
    intro n
    by_contra hne
    set α : ℝ := (1 : ℝ) / (2 * ((n : ℝ) + 1)) with hα
    have hαpos : 0 < α := by
      rw [hα]
      positivity
    have hα2 : (2 : ℝ) * α = (1 : ℝ) / ((n : ℝ) + 1) := by
      rw [hα]
      have : ((n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
    -- the open set `O`
    obtain ⟨fq, hfq⟩ : ∃ f : St → ℝ,
        f = fun q => v (mk q j) - ContactEnv v κ (mk q j) := ⟨_, rfl⟩
    obtain ⟨Vo, hVo⟩ : ∃ W : Set St,
        W = {q : St | (1 / 2 : ℝ) ^ j / 2 < (ofLp (mk q j)).2} := ⟨_, rfl⟩
    have hVoopen : IsOpen Vo := by
      rw [hVo]
      exact isOpen_lt continuous_const (hmktime j)
    have hVopos : ∀ q ∈ Vo, 0 < (ofLp (mk q j)).2 := by
      intro q hq
      rw [hVo] at hq
      have : (0 : ℝ) < (1 / 2 : ℝ) ^ j / 2 := by positivity
      exact lt_trans this hq
    have hfqc : ContinuousOn fq Vo := by
      rw [hfq]
      refine (hvcont.comp (hmkcont j)).continuousOn.sub ?_
      refine ContinuousOn.comp hWcont
        (hmkcont j).continuousOn (fun q hq => ?_)
      exact hVopos q hq
    obtain ⟨Oo, hOo⟩ : ∃ O : Set St, O = Vo ∩ fq ⁻¹' Set.Ioi α := ⟨_, rfl⟩
    have hOoopen : IsOpen Oo := by
      rw [hOo]
      exact hfqc.isOpen_inter_preimage hVoopen isOpen_Ioi
    have hOopos : 0 < (lmt : Measure St) Oo := by
      have hsub : {q : St | (1 : ℝ) / (n + 1) <
          v (mk q j) - ContactEnv v κ (mk q j)} ∩ Acl j ⊆ Oo := by
        intro q hq
        rw [hOo, hVo, hfq]
        refine ⟨?_, ?_⟩
        · have h1 := hAtime q hq.2
          have h2 : (1 / 2 : ℝ) ^ j / 2 < (1 / 2 : ℝ) ^ j := by linarith only [hδj]
          exact lt_of_lt_of_le h2 h1
        · have h3 := hq.1
          rw [Set.mem_ofPred_eq] at h3
          rw [← hα2] at h3
          exact lt_trans (by linarith only [hαpos]) h3
      have heq := measure_inter_conull (μ := (lmt : Measure St))
        (s := {q : St | (1 : ℝ) / (n + 1) <
          v (mk q j) - ContactEnv v κ (mk q j)}) hAfull
      have := measure_mono (μ := (lmt : Measure St)) hsub
      rw [heq] at this
      exact lt_of_lt_of_le (pos_iff_ne_zero.mpr hne) this
    -- the compact set on which the envelope continuity is uniform
    obtain ⟨Kc, hKc⟩ : ∃ K : Set (WithLp 2 (F × ℝ)),
        K = (Bx ∩ {z : WithLp 2 (F × ℝ) | (1 / 2 : ℝ) ^ j / 2 ≤ (ofLp z).2}) ∩
          (fun z => v z - ContactEnv v κ z) ⁻¹' Set.Ici α := ⟨_, rfl⟩
    have hbase : IsClosed (Bx ∩ {z : WithLp 2 (F × ℝ) |
        (1 / 2 : ℝ) ^ j / 2 ≤ (ofLp z).2}) := by
      refine hBxcpt.isClosed.inter (isClosed_le continuous_const ?_)
      exact (by fun_prop : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).2)
    have hbasepos : ∀ z ∈ Bx ∩ {z : WithLp 2 (F × ℝ) |
        (1 / 2 : ℝ) ^ j / 2 ≤ (ofLp z).2}, 0 < (ofLp z).2 := by
      intro z hz
      have : (0 : ℝ) < (1 / 2 : ℝ) ^ j / 2 := by positivity
      exact lt_of_lt_of_le this hz.2
    have hKcclosed : IsClosed Kc := by
      rw [hKc]
      refine ContinuousOn.preimage_isClosed_of_isClosed ?_ hbase isClosed_Ici
      exact hvcont.continuousOn.sub (hWcont.mono (fun z hz => hbasepos z hz))
    have hKccpt : IsCompact Kc := by
      refine hBxcpt.of_isClosed_subset hKcclosed ?_
      intro z hz
      rw [hKc] at hz
      exact hz.1.1
    have hKcpos : ∀ z ∈ Kc, 0 < (ofLp z).2 := by
      intro z hz
      rw [hKc] at hz
      exact hbasepos z hz.1
    obtain ⟨ε₀, hε₀, hgapbd⟩ := hgap2 Kc hKccpt hKcpos (α / 2) (by positivity)
    have hJbad : ∀ e : ℝ, 0 < e → e < ε₀ → ∀ z ∈ Kc,
        JGap v κ e z ≤ -(α / (4 * e)) := by
      intro e he heε z hz
      have h1 := hgapbd e he heε z hz
      have h2 : α ≤ v z - ContactEnv v κ z := by
        rw [hKc] at hz
        exact hz.2
      have h3 := abs_le.mp h1
      refine hdivtrick _ _ _ he hαpos ?_
      have h4 : 2 * e * JGap v κ e z ≤ (ContactEnv v κ z - v z) + α / 2 := by
        linarith only [h3.2]
      linarith only [h2, h4]
    -- the pre-limit masses of `O` are bounded below
    have hOliminf := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hnstend hOoopen
    obtain ⟨aa, haa⟩ : ∃ a : ENNReal, a = (lmt : Measure St) Oo / 2 := ⟨_, rfl⟩
    have haane : aa ≠ 0 := by
      rw [haa]
      exact (ENNReal.half_pos (pos_iff_ne_zero.mp hOopos)).ne'
    have haatop : aa ≠ ⊤ := by
      rw [haa]
      exact (lt_of_le_of_lt ENNReal.half_le_self (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top)).ne
    have haalt : aa < (lmt : Measure St) Oo := by
      rw [haa]
      exact ENNReal.half_lt_self (pos_iff_ne_zero.mp hOopos)
        (lt_of_le_of_lt prob_le_one ENNReal.one_lt_top).ne
    have hpc : 0 < aa.toReal := ENNReal.toReal_pos haane haatop
    have hev : ∀ᶠ h in atTop, aa < (lam (ns h) : Measure St) Oo :=
      Filter.eventually_lt_of_lt_liminf (lt_of_lt_of_le haalt hOliminf)
    -- choose one index large enough for every requirement
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = max ((|UB| - H + 1) / 1) 1 := ⟨_, rfl⟩
    have hDpos : 0 < D := by
      rw [hD]
      exact lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one
      (div_pos (mul_pos hαpos hpc) (mul_pos (by norm_num : (0:ℝ) < 4) hDpos))
      (by norm_num : (1 : ℝ) / 2 < 1)
    obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one hε₀ (by norm_num : (1 : ℝ) / 2 < 1)
    obtain ⟨h, hhj, hhev, hhn0, hhn1⟩ :
        ∃ h : ℕ, j ≤ h ∧ aa < (lam (ns h) : Measure St) Oo ∧ n0 ≤ h ∧ n1 ≤ h := by
      have := (hev.and ((Filter.eventually_ge_atTop j).and
        ((Filter.eventually_ge_atTop n0).and (Filter.eventually_ge_atTop n1)))).exists
      obtain ⟨h, h1, h2, h3, h4⟩ := this
      exact ⟨h, h2, h1, h3, h4⟩
    have hhns : h ≤ ns h := hns h
    have hjk : j ≤ ns h + 1 := by omega
    have hεbound : εf (ns h) ≤ (1 / 2 : ℝ) ^ n0 := by
      refine le_trans (hεsmall (ns h)) ?_
      have h3 : (1 / 2 : ℝ) ^ (ns h + 1) ≤ (1 / 2 : ℝ) ^ n0 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h4 : (0 : ℝ) < (1 / 2 : ℝ) ^ (ns h + 1) := by positivity
      linarith only [h3, h4]
    have hεlt0 : εf (ns h) < ε₀ := by
      refine lt_of_le_of_lt (hεsmall (ns h)) (lt_of_le_of_lt ?_ hn1)
      have h3 : (1 / 2 : ℝ) ^ (ns h + 1) ≤ (1 / 2 : ℝ) ^ n1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h4 : (0 : ℝ) < (1 / 2 : ℝ) ^ (ns h + 1) := by positivity
      linarith only [h3, h4]
    have hεltD : εf (ns h) < α * aa.toReal / (4 * D) :=
      lt_of_le_of_lt hεbound hn0
    -- the divergent estimate at this index
    obtain ⟨hfi, hfb⟩ := hmean (ns h) j hj hjk
    have hprobk := hprob (ns h)
    have hprobl : IsProbabilityMeasure (lam (ns h) : Measure St) := (lam (ns h)).2
    have hAmeas : MeasurableSet[m0f (ns h)] (Ψ (ns h) ⁻¹' Oo) :=
      (hΨm (ns h)) hOoopen.measurableSet
    obtain ⟨pp, hpp⟩ : ∃ p : ℝ, p = (μf (ns h) (Ψ (ns h) ⁻¹' Oo)).toReal := ⟨_, rfl⟩
    have hppeq : pp = ((lam (ns h) : Measure St) Oo).toReal := by
      rw [hpp, hpush (ns h) Oo hOoopen.measurableSet]
    have hppge : aa.toReal ≤ pp := by
      rw [hppeq]
      exact ENNReal.toReal_mono (measure_ne_top _ _) hhev.le
    have hpple : pp ≤ 1 := by
      rw [hpp]
      have := ENNReal.toReal_mono (a := μf (ns h) (Ψ (ns h) ⁻¹' Oo)) ENNReal.one_ne_top
        prob_le_one
      simpa using this
    have hεk := hεpos (ns h)
    obtain ⟨cc, hcc⟩ : ∃ c : ℝ, c = UB + α / (4 * εf (ns h)) := ⟨_, rfl⟩
    have hpt : ∀ ω : Ωf (ns h),
        JGap v κ (εf (ns h)) (zf (ns h) (smarkf (ns h) j ω) ω)
          ≤ UB - cc * (Ψ (ns h) ⁻¹' Oo).indicator (fun _ => (1 : ℝ)) ω := by
      intro ω
      by_cases hmem : ω ∈ Ψ (ns h) ⁻¹' Oo
      · rw [Set.indicator_of_mem hmem, mul_one, hcc]
        have hmkval : mk (Ψ (ns h) ω) j = zf (ns h) (smarkf (ns h) j ω) ω :=
          hmkpush (ns h) j ω hj hjk
        have hOmem : Ψ (ns h) ω ∈ Oo := hmem
        rw [hOo, hVo, hfq] at hOmem
        have hz1 : zf (ns h) (smarkf (ns h) j ω) ω ∈ Kc := by
          rw [hKc]
          refine ⟨⟨hmkBx (ns h) j hj hjk ω, ?_⟩, ?_⟩
          · have h7 := hOmem.1
            simp only [Set.mem_ofPred_eq, hmkval] at h7
            exact h7.le
          · have h8 := hOmem.2
            simp only [Set.mem_preimage, Set.mem_Ioi, hmkval] at h8
            exact h8.le
        have := hJbad (εf (ns h)) hεk hεlt0 _ hz1
        linarith only [this]
      · rw [Set.indicator_of_notMem hmem, mul_zero, sub_zero]
        exact hUB _ (hmkBx (ns h) j hj hjk ω)
          (htpos (ns h) (smarkf (ns h) j ω) ω) (εf (ns h)) hεk
          (le_trans (hεsmall (ns h)) (by
            have : (0:ℝ) < (1/2:ℝ)^(ns h + 1) := by positivity
            have h5 : (1/2:ℝ)^(ns h + 1) ≤ 1 := by
              calc (1/2:ℝ)^(ns h + 1) ≤ (1/2:ℝ)^0 :=
                    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
                _ = 1 := by norm_num
            linarith only [this, h5]))
    have hrhsint : Integrable
        (fun ω : Ωf (ns h) => UB
          - cc * (Ψ (ns h) ⁻¹' Oo).indicator (fun _ => (1 : ℝ)) ω) (μf (ns h)) := by
      refine (integrable_const UB).sub ?_
      exact (((integrable_const (1 : ℝ)).integrableOn).integrable_indicator
        hAmeas).const_mul cc
    have hint := integral_mono hfi hrhsint hpt
    have hrhs : ∫ ω, (UB
        - cc * (Ψ (ns h) ⁻¹' Oo).indicator (fun _ => (1 : ℝ)) ω) ∂(μf (ns h))
        = UB - cc * pp := by
      rw [integral_sub (integrable_const UB)
        ((((integrable_const (1 : ℝ)).integrableOn).integrable_indicator
          hAmeas).const_mul cc),
        integral_const, integral_const_mul, integral_indicator_const (1 : ℝ) hAmeas]
      simp [hpp, measureReal_def]
    rw [hrhs] at hint
    have hlow := hfb
    have hUBterm : UB * (1 - pp) ≤ |UB| := by
      have h1 : (0 : ℝ) ≤ 1 - pp := by linarith only [hpple]
      have h2 : UB ≤ |UB| := le_abs_self UB
      nlinarith only [abs_nonneg UB, hppge, hpc, h1, h2]
    have hαterm : α * aa.toReal / (4 * εf (ns h))
        ≤ α / (4 * εf (ns h)) * pp := by
      have h1 : (0 : ℝ) < 4 * εf (ns h) := by linarith only [hεk]
      have h2 : (0 : ℝ) < α / (4 * εf (ns h)) := div_pos hαpos h1
      have h3 : α * aa.toReal / (4 * εf (ns h))
          = (α / (4 * εf (ns h))) * aa.toReal := by ring
      rw [h3]
      exact mul_le_mul_of_nonneg_left hppge h2.le
    have hcombine : H - 1 ≤ |UB| - α * aa.toReal / (4 * εf (ns h)) := by
      have hexp : UB - cc * pp = UB * (1 - pp) - α / (4 * εf (ns h)) * pp := by
        rw [hcc]
        ring
      rw [hexp] at hint
      linarith only [le_trans hlow hint, hUBterm, hαterm]
    have hfin : α * aa.toReal / (4 * εf (ns h)) ≤ D := by
      have h1 : (|UB| - H + 1) / 1 ≤ D := by
        rw [hD]
        exact le_max_left _ _
      have : α * aa.toReal / (4 * εf (ns h)) ≤ |UB| - H + 1 := by linarith only [hcombine]
      linarith only [this, h1]
    have h1 : (0 : ℝ) < 4 * εf (ns h) := by linarith only [hεk]
    rw [div_le_iff₀ h1] at hfin
    rw [lt_div_iff₀ (mul_pos (by norm_num : (0:ℝ) < 4) hDpos)] at hεltD
    nlinarith only [hεltD, hfin, hpc, hαpos, hDpos, hεk]
  -- assemble
  have hBad : (lmt : Measure St) {q : St | 0 <
      v (mk q j) - ContactEnv v κ (mk q j)} = 0 := by
    refine measure_mono_null ?_ (measure_iUnion_null (fun n => hzero n))
    intro q hq
    simp only [Set.mem_ofPred_eq] at hq
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hq
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hBadae : ∀ᵐ q ∂(lmt : Measure St),
      ¬ (0 < v (mk q j) - ContactEnv v κ (mk q j)) := by
    rw [MeasureTheory.ae_iff]
    simpa using hBad
  filter_upwards [hBadae, MeasureTheory.mem_ae_iff.mpr hAfull] with q hq1 hq2 _
  have h1 : ¬ (0 < v (mk q j) - ContactEnv v κ (mk q j)) := hq1
  have h2 := hWle (mk q j) (lt_of_lt_of_le hδj (hAtime q hq2))
  linarith only [not_lt.mp h1, h2]
