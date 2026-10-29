module

public import InfHarmonic.Preamble

@[expose] public section
open Set Filter Topology MeasureTheory

/-- The optional-stopping half of paper Proposition 6.7, part 1, as a statement
about an abstract submartingale rather than about the contact walk.

Let `J` and `E` be adapted real processes on a filtered probability space, `E`
nonnegative, let `τ` be a stopping time, let `c > 0` and suppose that

* `J` starts at the constant `J0` and is trapped between `-Jl` and `Ju`;
* `c * E n ω ≤ Lam` almost surely for every `n` strictly before the stop, with
  `0 ≤ Lam`; and
* `M n = J n - c * ∑_{k < n} 1_{k < τ} E k` is a submartingale.

Then (i) for every stopping time `σ ≤ τ` the stopped value `J (σ ·) ·` is
integrable with mean at least `J0`; (ii) the accumulated error
`∑_{k < τ} E k` is integrable; and (iii) its mean is at most `(Ju - J0) / c`.

The error budget is stated with the symbolic numerator `Ju - J0`: an
application supplies its own upper bound `Ju` for `J` and its own starting
value `J0`, and converts. Nothing here mentions the walk, the envelope or the
ambient inner-product space; the proof is the truncation of `σ` at a finite
horizon, optional stopping for the truncated times, dominated convergence for
conclusion (i), and monotone convergence of the lower integrals for (ii) and
(iii). -/
theorem OptionalStoppingErrorBudget {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (J E : ℕ → Ω → ℝ) (τ : Ω → ℕ) (c J0 Lam Ju Jl : ℝ) (hc0 : 0 < c)
    (hLam0 : (0 : ℝ) ≤ Lam)
    (hJSM : ∀ n, StronglyMeasurable[𝒢 n] (J n))
    (hESM : ∀ n, StronglyMeasurable[𝒢 n] (E n))
    (hE0 : ∀ (n : ℕ) (ω : Ω), 0 ≤ E n ω)
    (hτst : IsStoppingTime 𝒢 (fun ω => (τ ω : ℕ∞)))
    (hJ0 : ∀ ω : Ω, J 0 ω = J0)
    (hJu : ∀ (n : ℕ) (ω : Ω), J n ω ≤ Ju)
    (hJl : ∀ (n : ℕ) (ω : Ω), -Jl ≤ J n ω)
    (hEball : ∀ᵐ ω ∂μ, ∀ n : ℕ, n < τ ω → c * E n ω ≤ Lam)
    (hsub : Submartingale (fun n ω => J n ω
      - c * ∑ k ∈ Finset.range n, (if k < τ ω then E k ω else 0)) 𝒢 μ) :
    (∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → (∀ ω, σ ω ≤ τ ω) →
        Integrable (fun ω => J (σ ω) ω) μ ∧ J0 ≤ ∫ ω, J (σ ω) ω ∂μ) ∧
      Integrable (fun ω => ∑ k ∈ Finset.range (τ ω), E k ω) μ ∧
      (∫ ω, (∑ k ∈ Finset.range (τ ω), E k ω) ∂μ) ≤ (Ju - J0) / c := by
  classical
  have hμ1 : μ Set.univ = 1 := measure_univ
  set Mp : ℕ → Ω → ℝ := fun n ω => J n ω
    - c * ∑ k ∈ Finset.range n, (if k < τ ω then E k ω else 0) with hMpdef
  -- ## random indices are measurable
  have hJmeas : ∀ i : ℕ, Measurable (fun ω => J i ω) :=
    fun i => ((hJSM i).mono (𝒢.le i)).measurable
  have hEsummeas : ∀ i : ℕ, Measurable (fun ω => ∑ k ∈ Finset.range i, E k ω) := by
    intro i
    refine Finset.measurable_sum _ (fun k _ => ?_)
    exact ((hESM k).mono (𝒢.le k)).measurable
  have hfinidx : ∀ (hh : ℕ) (ρ : Ω → ℕ) (g : ℕ → Ω → ℝ), (∀ ω, ρ ω ≤ hh) →
      Measurable ρ → (∀ i, Measurable (g i)) → Measurable (fun ω => g (ρ ω) ω) := by
    intro hh ρ g hbd hρ hg
    have heq : (fun ω => g (ρ ω) ω)
        = fun ω => ∑ i ∈ Finset.range (hh + 1), (if ρ ω = i then g i ω else 0) := by
      funext ω
      rw [Finset.sum_eq_single_of_mem (ρ ω) (Finset.mem_range.mpr (by
        have := hbd ω
        omega))]
      · rw [if_pos rfl]
      · intro i _ hi
        rw [if_neg (fun hc => hi hc.symm)]
    rw [heq]
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact Measurable.ite (hρ (measurableSet_singleton i)) (hg i) measurable_const
  set Lam1 : ℝ := max Ju Jl with hLam1def
  have hJabs : ∀ (i : ℕ) (ω : Ω), |J i ω| ≤ Lam1 := by
    intro i ω
    rw [abs_le, hLam1def]
    constructor
    · exact le_trans (neg_le_neg (le_max_right _ _)) (hJl i ω)
    · exact le_trans (hJu i ω) (le_max_left _ _)
  have hJintrand : ∀ ρ : Ω → ℕ, Measurable (fun ω => J (ρ ω) ω) →
      Integrable (fun ω => J (ρ ω) ω) μ := by
    intro ρ hρ
    refine Integrable.mono' (integrable_const Lam1)
      hρ.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    exact hJabs (ρ ω) ω
  -- ## optional stopping for the truncated stopping times
  have hMp0 : ∀ ω : Ω, Mp 0 ω = J0 := by
    intro ω
    rw [hMpdef]
    simp [hJ0 ω]
  have hstmeas : ∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → Measurable σ := by
    intro σ hσst
    refine measurable_to_countable' (fun i => ?_)
    have h1 : MeasurableSet[𝒢 i] {ω | ((σ ω : ℕ∞)) = (i : ℕ∞)} :=
      hσst.measurableSet_eq_of_countable i
    have heq : {ω | ((σ ω : ℕ∞)) = (i : ℕ∞)} = {ω | σ ω = i} := by
      ext ω
      show ((σ ω : ℕ∞)) = (i : ℕ∞) ↔ σ ω = i
      exact Nat.cast_inj
    rw [heq] at h1
    exact 𝒢.le i _ h1
  have hidxmeas : ∀ (σ : Ω → ℕ), Measurable σ → ∀ hh : ℕ,
      Measurable (fun ω => min (σ ω) hh) := by
    intro σ hσ hh
    exact (Measurable.of_discrete : Measurable (fun j : ℕ => min j hh)).comp hσ
  have hJtrunc : ∀ (σ : Ω → ℕ), Measurable σ → ∀ hh : ℕ,
      Measurable (fun ω => J (min (σ ω) hh) ω) := by
    intro σ hσ hh
    exact hfinidx hh _ _ (fun ω => min_le_right _ _) (hidxmeas σ hσ hh) hJmeas
  have hEtrunc : ∀ (σ : Ω → ℕ), Measurable σ → ∀ hh : ℕ,
      Measurable (fun ω => ∑ k ∈ Finset.range (min (σ ω) hh), E k ω) := by
    intro σ hσ hh
    exact hfinidx hh _ _ (fun ω => min_le_right _ _) (hidxmeas σ hσ hh) hEsummeas
  have hkey : ∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → (∀ ω, σ ω ≤ τ ω) →
      ∀ hh : ℕ,
        J0
            + c * ∫ ω, (∑ k ∈ Finset.range (min (σ ω) hh), E k ω) ∂μ
          ≤ ∫ ω, J (min (σ ω) hh) ω ∂μ := by
    intro σ hσst hσle hh
    have hσmeas : Measurable σ := hstmeas σ hσst
    have hρmeas : Measurable (fun ω => min (σ ω) hh) :=
      (Measurable.of_discrete : Measurable (fun j : ℕ => min j hh)).comp hσmeas
    have hσle' : ∀ i : ℕ, MeasurableSet[𝒢 i] {ω | σ ω ≤ i} := by
      intro i
      have h1 : MeasurableSet[𝒢 i] {ω | ((σ ω : ℕ∞)) ≤ (i : ℕ∞)} := hσst i
      have heq : {ω | ((σ ω : ℕ∞)) ≤ (i : ℕ∞)} = {ω | σ ω ≤ i} := by
        ext ω
        show ((σ ω : ℕ∞)) ≤ (i : ℕ∞) ↔ σ ω ≤ i
        exact Nat.cast_le
      rw [heq] at h1
      exact h1
    -- the stopped value of the submartingale
    have hπst : IsStoppingTime 𝒢 (fun ω => ((min (σ ω) hh : ℕ) : ℕ∞)) := by
      intro i
      show MeasurableSet[𝒢 i] {ω | ((min (σ ω) hh : ℕ) : ℕ∞) ≤ (i : ℕ∞)}
      have heq : {ω | ((min (σ ω) hh : ℕ) : ℕ∞) ≤ (i : ℕ∞)}
          = {ω | σ ω ≤ i} ∪ {ω | hh ≤ i} := by
        ext ω
        show ((min (σ ω) hh : ℕ) : ℕ∞) ≤ (i : ℕ∞) ↔ (σ ω ≤ i ∨ hh ≤ i)
        rw [Nat.cast_le]
        exact min_le_iff
      rw [heq]
      refine MeasurableSet.union (hσle' i) ?_
      rcases le_or_gt hh i with hcc | hcc
      · have h2 : {_ω : Ω | hh ≤ i} = Set.univ := by
          ext ω
          show hh ≤ i ↔ True
          simp [hcc]
        rw [h2]
        exact @MeasurableSet.univ Ω (𝒢 i)
      · have h2 : {_ω : Ω | hh ≤ i} = (∅ : Set Ω) := by
          ext ω
          show hh ≤ i ↔ False
          simp
          omega
        rw [h2]
        exact @MeasurableSet.empty Ω (𝒢 i)
    have hzerost : IsStoppingTime 𝒢 (fun _ : Ω => ((0 : ℕ) : ℕ∞)) := isStoppingTime_const 𝒢 0
    have hos := hsub.expected_stoppedValue_mono hzerost hπst
      (fun ω => Nat.cast_le.mpr (Nat.zero_le _)) (N := hh)
      (fun ω => Nat.cast_le.mpr (min_le_right _ _))
    -- rewrite both stopped values
    have huntop : ∀ n : ℕ, (((n : ℕ) : ℕ∞)).untopA = n := by
      intro n
      simp
    have hsv0 : stoppedValue Mp (fun _ : Ω => ((0 : ℕ) : ℕ∞)) = Mp 0 := by
      funext ω
      show Mp (((0 : ℕ) : ℕ∞)).untopA ω = Mp 0 ω
      rw [huntop]
    have hsvπ : stoppedValue Mp (fun ω => ((min (σ ω) hh : ℕ) : ℕ∞))
        = fun ω => Mp (min (σ ω) hh) ω := by
      funext ω
      show Mp (((min (σ ω) hh : ℕ) : ℕ∞)).untopA ω = Mp (min (σ ω) hh) ω
      rw [huntop]
    rw [hsv0, hsvπ] at hos
    -- compute both integrals
    have hint0 : ∫ ω, Mp 0 ω ∂μ = J0 := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hMp0), integral_const]
      have h1 : μ.real Set.univ = 1 := by
        rw [Measure.real, hμ1]
        simp
      rw [h1, one_smul]
    have hsumeq : ∀ ω : Ω, ∑ k ∈ Finset.range (min (σ ω) hh), (if k < τ ω then E k ω else 0)
        = ∑ k ∈ Finset.range (min (σ ω) hh), E k ω := by
      intro ω
      refine Finset.sum_congr rfl (fun k hk => ?_)
      have hk1 : k < min (σ ω) hh := Finset.mem_range.mp hk
      have hk2 : k < τ ω := by
        have h1 : min (σ ω) hh ≤ σ ω := min_le_left _ _
        have h2 := hσle ω
        omega
      rw [if_pos hk2]
    have hMpπ : ∀ ω : Ω, Mp (min (σ ω) hh) ω
        = J (min (σ ω) hh) ω
          - c * ∑ k ∈ Finset.range (min (σ ω) hh), E k ω := by
      intro ω
      simp only [hMpdef]
      rw [hsumeq ω]
    have hJmeasπ : Measurable (fun ω => J (min (σ ω) hh) ω) :=
      hJtrunc σ hσmeas hh
    have hEmeasπ : Measurable (fun ω => ∑ k ∈ Finset.range (min (σ ω) hh), E k ω) :=
      hEtrunc σ hσmeas hh
    have hEintπ : Integrable (fun ω => ∑ k ∈ Finset.range (min (σ ω) hh), E k ω) μ := by
      refine Integrable.mono' (integrable_const (hh * (Lam / c)))
        hEmeasπ.aestronglyMeasurable ?_
      filter_upwards [hEball] with ω hω
      have h3 : 0 ≤ ∑ k ∈ Finset.range (min (σ ω) hh), E k ω :=
        Finset.sum_nonneg (fun k _ => hE0 k ω)
      have h4 : ∑ k ∈ Finset.range (min (σ ω) hh), E k ω ≤ hh * (Lam / c) := by
        have h5 : ∀ k ∈ Finset.range (min (σ ω) hh), E k ω ≤ Lam / c := by
          intro k hk
          have hk1 : k < min (σ ω) hh := Finset.mem_range.mp hk
          have hk2 : k < τ ω := by
            have h1 : min (σ ω) hh ≤ σ ω := min_le_left _ _
            have h2 := hσle ω
            omega
          have h6 := hω k hk2
          rw [le_div_iff₀ hc0]
          linarith only [h6]
        calc ∑ k ∈ Finset.range (min (σ ω) hh), E k ω
            ≤ ∑ _k ∈ Finset.range (min (σ ω) hh), (Lam / c) := Finset.sum_le_sum h5
          _ = ((min (σ ω) hh : ℕ) : ℝ) * (Lam / c) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ (hh : ℝ) * (Lam / c) := by
              have h7 : ((min (σ ω) hh : ℕ) : ℝ) ≤ (hh : ℝ) := by
                have : min (σ ω) hh ≤ hh := min_le_right _ _
                exact_mod_cast this
              have h8 : (0:ℝ) ≤ Lam / c := div_nonneg hLam0 hc0.le
              exact mul_le_mul_of_nonneg_right h7 h8
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have : (0:ℝ) ≤ hh * (Lam / c) :=
          mul_nonneg (Nat.cast_nonneg hh) (div_nonneg hLam0 hc0.le)
        linarith only [this, h3]
      · exact h4
    have hintπ : ∫ ω, Mp (min (σ ω) hh) ω ∂μ
        = (∫ ω, J (min (σ ω) hh) ω ∂μ)
          - c * ∫ ω, (∑ k ∈ Finset.range (min (σ ω) hh), E k ω) ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hMpπ)]
      rw [integral_sub (hJintrand _ hJmeasπ) (hEintπ.const_mul c), integral_const_mul]
    rw [hint0, hintπ] at hos
    linarith only [hos]
  -- ## conclusion (i)
  have hlimidx : ∀ (σ : Ω → ℕ) (ω : Ω) (g : ℕ → ℝ),
      Tendsto (fun hh => g (min (σ ω) hh)) atTop (𝓝 (g (σ ω))) := by
    intro σ ω g
    refine tendsto_atTop_of_eventually_const (i₀ := σ ω) (fun hh hhh => ?_)
    rw [min_eq_left hhh]
  have hconc1 : ∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → (∀ ω, σ ω ≤ τ ω) →
      Integrable (fun ω => J (σ ω) ω) μ ∧
      J0
        ≤ ∫ ω, J (σ ω) ω ∂μ := by
    intro σ hσst hσle
    have hσmeas : Measurable σ := hstmeas σ hσst
    have hJσmeas : Measurable (fun ω => J (σ ω) ω) := by
      refine measurable_of_tendsto_metrizable (fun hh => hJtrunc σ hσmeas hh)
        (tendsto_pi_nhds.mpr (fun ω => ?_))
      exact hlimidx σ ω (fun i => J i ω)
    refine ⟨hJintrand σ hJσmeas, ?_⟩
    have hdct : Tendsto (fun hh => ∫ ω, J (min (σ ω) hh) ω ∂μ) atTop
        (𝓝 (∫ ω, J (σ ω) ω ∂μ)) := by
      exact tendsto_integral_of_dominated_convergence (fun _ => Lam1)
        (fun hh => (hJtrunc σ hσmeas hh).aestronglyMeasurable) (integrable_const Lam1)
        (fun hh => Filter.Eventually.of_forall (fun ω => by
          rw [Real.norm_eq_abs]
          exact hJabs _ ω))
        (Filter.Eventually.of_forall (fun ω => hlimidx σ ω (fun i => J i ω)))
    refine ge_of_tendsto hdct (Filter.Eventually.of_forall (fun hh => ?_))
    have h1 := hkey σ hσst hσle hh
    have h2 : 0 ≤ ∫ ω, (∑ k ∈ Finset.range (min (σ ω) hh), E k ω) ∂μ :=
      integral_nonneg (fun ω => Finset.sum_nonneg (fun k _ => hE0 k ω))
    have h3 : 0 ≤ c * ∫ ω, (∑ k ∈ Finset.range (min (σ ω) hh), E k ω) ∂μ :=
      mul_nonneg hc0.le h2
    linarith only [h1, h3]
  -- ## conclusion (ii): the error budget
  have hτmeas : Measurable τ := hstmeas τ hτst
  have hSτmeas : Measurable (fun ω => ∑ k ∈ Finset.range (τ ω), E k ω) := by
    refine measurable_of_tendsto_metrizable (fun hh => hEtrunc τ hτmeas hh)
      (tendsto_pi_nhds.mpr (fun ω => ?_))
    exact hlimidx τ ω (fun i => ∑ k ∈ Finset.range i, E k ω)
  have hbnd : ∀ hh : ℕ, ∫ ω, (∑ k ∈ Finset.range (min (τ ω) hh), E k ω) ∂μ
      ≤ (Ju - J0) / c := by
    intro hh
    have h1 := hkey τ hτst (fun ω => le_rfl) hh
    have h2 : ∫ ω, J (min (τ ω) hh) ω ∂μ ≤ Ju := by
      have h3 : ∫ ω, J (min (τ ω) hh) ω ∂μ ≤ ∫ _ω : Ω, (Ju) ∂μ :=
        integral_mono (hJintrand _ (hJtrunc τ hτmeas hh)) (integrable_const _)
          (fun ω => hJu _ ω)
      rw [integral_const] at h3
      have h4 : μ.real Set.univ = 1 := by
        rw [Measure.real, hμ1]
        simp
      rw [h4, one_smul] at h3
      exact h3
    rw [le_div_iff₀ hc0]
    linarith only [h1, h2]
  have hdivnn : (0 : ℝ) ≤ (Ju - J0) / c := by
    refine le_trans ?_ (hbnd 0)
    exact integral_nonneg (fun ω => Finset.sum_nonneg (fun k _ => hE0 k ω))
  have hSτnn : ∀ ω : Ω, 0 ≤ ∑ k ∈ Finset.range (τ ω), E k ω :=
    fun ω => Finset.sum_nonneg (fun k _ => hE0 k ω)
  have hlint : ∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range (τ ω), E k ω) ∂μ
      ≤ ENNReal.ofReal ((Ju - J0) / c) := by
    have hmono : Monotone (fun hh : ℕ => fun ω : Ω =>
        ENNReal.ofReal (∑ k ∈ Finset.range (min (τ ω) hh), E k ω)) := by
      intro h1 h2 h12 ω
      have hsubset : Finset.range (min (τ ω) h1) ⊆ Finset.range (min (τ ω) h2) := by
        intro k hk
        have hk1 := Finset.mem_range.mp hk
        refine Finset.mem_range.mpr ?_
        have hmm : min (τ ω) h1 ≤ min (τ ω) h2 := min_le_min (le_refl (τ ω)) h12
        omega
      exact ENNReal.ofReal_le_ofReal
        (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => hE0 k ω))
    have hmeasf : ∀ hh : ℕ, Measurable (fun ω : Ω =>
        ENNReal.ofReal (∑ k ∈ Finset.range (min (τ ω) hh), E k ω)) :=
      fun hh => ENNReal.measurable_ofReal.comp (hEtrunc τ hτmeas hh)
    have hsup : ∀ ω : Ω, ENNReal.ofReal (∑ k ∈ Finset.range (τ ω), E k ω)
        = ⨆ hh : ℕ, ENNReal.ofReal (∑ k ∈ Finset.range (min (τ ω) hh), E k ω) := by
      intro ω
      refine le_antisymm ?_ ?_
      · refine le_iSup_of_le (τ ω) ?_
        rw [min_self]
      · refine iSup_le (fun hh => ?_)
        have hsubset : Finset.range (min (τ ω) hh) ⊆ Finset.range (τ ω) := by
          intro k hk
          have hk1 := Finset.mem_range.mp hk
          refine Finset.mem_range.mpr ?_
          have hmm : min (τ ω) hh ≤ τ ω := min_le_left _ _
          omega
        exact ENNReal.ofReal_le_ofReal
          (Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun k _ _ => hE0 k ω))
    rw [lintegral_congr hsup, lintegral_iSup hmeasf hmono]
    refine iSup_le (fun hh => ?_)
    have hint : Integrable (fun ω => ∑ k ∈ Finset.range (min (τ ω) hh), E k ω) μ := by
      refine Integrable.mono' (integrable_const ((hh : ℝ) * (Lam / c)))
        (hEtrunc τ hτmeas hh).aestronglyMeasurable ?_
      filter_upwards [hEball] with ω hω
      have h3 : 0 ≤ ∑ k ∈ Finset.range (min (τ ω) hh), E k ω :=
        Finset.sum_nonneg (fun k _ => hE0 k ω)
      have h4 : ∑ k ∈ Finset.range (min (τ ω) hh), E k ω ≤ (hh : ℝ) * (Lam / c) := by
        have h5 : ∀ k ∈ Finset.range (min (τ ω) hh), E k ω ≤ Lam / c := by
          intro k hk
          have hk1 : k < min (τ ω) hh := Finset.mem_range.mp hk
          have hk2 : k < τ ω := by
            have h1 : min (τ ω) hh ≤ τ ω := min_le_left _ _
            omega
          have h6 := hω k hk2
          rw [le_div_iff₀ hc0]
          linarith only [h6]
        calc ∑ k ∈ Finset.range (min (τ ω) hh), E k ω
            ≤ ∑ _k ∈ Finset.range (min (τ ω) hh), (Lam / c) := Finset.sum_le_sum h5
          _ = ((min (τ ω) hh : ℕ) : ℝ) * (Lam / c) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          _ ≤ (hh : ℝ) * (Lam / c) := by
              have h7 : ((min (τ ω) hh : ℕ) : ℝ) ≤ (hh : ℝ) := by
                have : min (τ ω) hh ≤ hh := min_le_right _ _
                exact_mod_cast this
              have h8 : (0 : ℝ) ≤ Lam / c := div_nonneg hLam0 hc0.le
              exact mul_le_mul_of_nonneg_right h7 h8
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have : (0 : ℝ) ≤ (hh : ℝ) * (Lam / c) :=
          mul_nonneg (Nat.cast_nonneg hh) (div_nonneg hLam0 hc0.le)
        linarith only [this, h3]
      · exact h4
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall (fun ω => Finset.sum_nonneg (fun k _ => hE0 k ω)))]
    exact ENNReal.ofReal_le_ofReal (hbnd hh)
  have hSτint : Integrable (fun ω => ∑ k ∈ Finset.range (τ ω), E k ω) μ := by
    refine ⟨hSτmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hSτnn)]
    exact lt_of_le_of_lt hlint (by finiteness)
  refine ⟨hconc1, hSτint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hSτnn)
    hSτmeas.aestronglyMeasurable]
  have h1 : (∫⁻ ω, ENNReal.ofReal (∑ k ∈ Finset.range (τ ω), E k ω) ∂μ).toReal
      ≤ (ENNReal.ofReal ((Ju - J0) / c)).toReal :=
    ENNReal.toReal_mono (by finiteness) hlint
  rw [ENNReal.toReal_ofReal hdivnn] at h1
  exact h1
