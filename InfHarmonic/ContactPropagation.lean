module

public import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
public import InfHarmonic.ContactWalkTimeRange
public import InfHarmonic.TailEventSelection
public import InfHarmonic.MonotoneLimitFiniteAE
public import InfHarmonic.JBoxUpperBound
public import InfHarmonic.ContactWalkMarkLevels
public import InfHarmonic.FitSetClosed
public import InfHarmonic.StoppedWalkBudgets
public import InfHarmonic.MarkLocalization
public import InfHarmonic.JUpperBound
public import InfHarmonic.ContactGapLimit
public import InfHarmonic.ContactAtLimitingMarks
public import InfHarmonic.EnvHamiltonianSolution
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.UniformSubquadratic

@[expose] public section
set_option maxHeartbeats 500000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.8: for the pair supplied by the extremal envelope contact
there are a constant `K`, a terminal point `x_end` and an infinite set of
levels `j` at each of which `v` has a contact with its contact envelope at a
point `(x_j, δ_j)` carrying a fit `(p_j, a_j)` of radius `δ_j`, such that the
same terminal point lies within `K δ_j` of the origin of every one of those
fitted frames, and the envelope Hamiltonian of `v` is finite at `(x_end, 0)`. -/
theorem ContactPropagation (C₀ κ H : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ))
    (hWsub : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} (ContactEnv v κ))
    (hsand : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧ ContactEnv v κ z ≤ v z)
    (hW0 : ContactEnv v κ (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hv0 : v (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hconc : ∀ t : ℝ, 0 < t → ConcaveOn ℝ (Set.univ : Set F)
      (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t)))
    (hgap : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z = v z →
      (BaryEnv v (ofLp z).2 z - v z) / (ofLp z).2 = κ ^ 2 / 2)
    (hham : EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal))
    (hslope : Tendsto (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 H)) :
    ∃ (K : ℝ) (xend : F) (Jset : Set ℕ),
      0 ≤ K ∧ Jset.Infinite ∧ (∀ j ∈ Jset, 1 ≤ j) ∧
      (⊥ : EReal) < EnvHamiltonian v (toLp 2 (xend, (0 : ℝ))) ∧
      ∀ j ∈ Jset, ∃ (xj pj : F) (aj : ℝ),
        IsFit C₀ v (toLp 2 (xj, (1 / 2 : ℝ) ^ j)) ((1 / 2 : ℝ) ^ j) pj aj ∧
        ContactEnv v κ (toLp 2 (xj, (1 / 2 : ℝ) ^ j)) = v (toLp 2 (xj, (1 / 2 : ℝ) ^ j)) ∧
        ‖xend - xj + ((1 / 2 : ℝ) ^ j) • pj‖ ≤ K * (1 / 2 : ℝ) ^ j := by
  classical
  -- Step 1: the constants, the box, and the walks.
  obtain ⟨Cstar, hCstar0, hbudget⟩ :=
    StoppedWalkBudgets C₀ κ H hC₀ hκ v hv hcent hJ hWcont hWgrow hWsub hsand hW0 hv0
      hconc hgap hham hslope
  obtain ⟨T, R, Kloc, CΓ, hT8, hR2, hK2, hCΓ0, hloc⟩ :=
    MarkLocalization C₀ κ H hC₀ hκ v hv hcent hJ hWcont hWgrow hWsub hsand hW0 hv0
      hconc hgap hham hslope Cstar hCstar0
  -- The walks are indexed by `k`, standing for the level `N = k + 1`, so that the
  -- hypothesis `1 ≤ N` never has to be carried through the choice.
  have hwalkex : ∀ k : ℕ, ∃ (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω)
      (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
      (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ),
      IsContactWalk κ H T R v (k + 1) ε μ 𝒢 ξ z zp zm Q₀ τ ∧
      (∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → (∀ ω, σ ω ≤ τ ω) →
        Integrable (fun ω => JGap v κ ε (z (σ ω) ω)) μ ∧
        JGap v κ ε (toLp 2 ((0 : F), (1 : ℝ)))
          ≤ ∫ ω, JGap v κ ε (z (σ ω) ω) ∂μ) ∧
      Integrable (fun ω => ∑ n ∈ Finset.range (τ ω),
        (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) μ ∧
      ∫ ω, (∑ n ∈ Finset.range (τ ω),
        (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ
        ≤ Cstar * (1 + Real.log (R + (T : ℝ) + 2)) ^ 4 ∧
      ∃ (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (aj : ℕ → Ω → ℝ),
        IsMarkData C₀ v (k + 1) 𝒢 z τ smark pj aj := by
    intro k
    exact hbudget T (by omega) R hR2 (k + 1) (by omega)
  choose εf Ωf m0f μf 𝒢f ξf zf zpf zmf Q₀f τf hcwf hstopf hintf hbdf hmarkf using hwalkex
  choose smarkf pjf ajf hmdf using hmarkf
  -- Step 2: the marks sit on their own time level.
  have hlevels : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 →
      (∀ ω, (1 / 2 : ℝ) ^ j ≤ (ofLp (zf k (smarkf k j ω) ω)).2) ∧
      (∀ ω, (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1) →
        (ofLp (zf k (smarkf k j ω) ω)).2 = (1 / 2 : ℝ) ^ j) := by
    intro k j hj1 hjk
    exact ContactWalkMarkLevels C₀ κ H v T R (k + 1) (εf k) (Ωf k) (m0f k) (μf k)
      (𝒢f k) (ξf k) (zf k) (zpf k) (zmf k) (Q₀f k) (τf k) (smarkf k) (pjf k) (ajf k)
      (hcwf k) (hmdf k) j hj1 hjk
  -- Step 3: one compact space carrying terminal point, flag and all marks.
  set Bq : ℝ := R + (T : ℝ) + 2 with hBq
  set LB : ℝ := 1 + Real.log Bq with hLB
  have hBq12 : (12 : ℝ) ≤ Bq := by
    have : (8 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT8
    rw [hBq]; linarith
  have hLBpos : 0 < LB := by
    have h1 : (0 : ℝ) ≤ Real.log Bq := Real.log_nonneg (by linarith)
    rw [hLB]; linarith
  set Γ : ℕ → ℝ := fun j => CΓ * (LB + (j : ℝ)) with hΓ
  have hΓpos : ∀ j, 0 < Γ j := by
    intro j
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    exact mul_pos hCΓ0 (by linarith)
  set Bx : Set (WithLp 2 (F × ℝ)) :=
    {z | ‖(ofLp z).1‖ ≤ R + 1 ∧ (ofLp z).2 ∈ Set.Icc (0 : ℝ) (T : ℝ)} with hBx
  have hBxcpt : IsCompact Bx := by
    have himg : Bx = (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
        (Metric.closedBall (0 : F) (R + 1) ×ˢ Set.Icc (0 : ℝ) (T : ℝ)) := by
      ext z
      simp only [hBx, Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod,
        Metric.mem_closedBall, dist_zero_right]
      constructor
      · intro hz
        exact ⟨ofLp z, ⟨hz.1, hz.2⟩, by simp⟩
      · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
        simpa using ⟨hp1, hp2⟩
    rw [himg]
    exact ((isCompact_closedBall (0 : F) (R + 1)).prod isCompact_Icc).image (by fun_prop)
  have hzstarB : toLp 2 ((0 : F), (1 : ℝ)) ∈ Bx := by
    have h1 : (1 : ℝ) ≤ (T : ℝ) := by
      have : (8 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT8
      linarith
    simp only [hBx, Set.mem_ofPred_eq, Set.mem_Icc]
    refine ⟨?_, by norm_num, h1⟩
    simpa using by linarith
  set Kbox : ℕ → Set (WithLp 2 (F × ℝ) × F × ℝ) := fun j =>
    Bx ×ˢ (Metric.closedBall (0 : F) (Γ j) ×ˢ Set.Icc (-(Γ j)) (Γ j)) with hKbox
  set St : Set (WithLp 2 (F × ℝ) × Bool × (ℕ → WithLp 2 (F × ℝ) × F × ℝ)) :=
    Bx ×ˢ (Set.univ ×ˢ Set.univ.pi Kbox) with hSt
  have hStcpt : IsCompact St := by
    rw [hSt]
    exact hBxcpt.prod (isCompact_univ.prod (isCompact_univ_pi fun j =>
      hBxcpt.prod ((isCompact_closedBall (0 : F) (Γ j)).prod isCompact_Icc)))
  have hStne : St.Nonempty := by
    refine ⟨(toLp 2 ((0 : F), (1 : ℝ)), false,
      fun _ => (toLp 2 ((0 : F), (1 : ℝ)), 0, 0)), ?_⟩
    refine Set.mk_mem_prod hzstarB (Set.mk_mem_prod (Set.mem_univ _) ?_)
    intro j _
    refine Set.mk_mem_prod hzstarB (Set.mk_mem_prod ?_ ?_)
    · simpa using (hΓpos j).le
    · exact Set.mem_Icc.mpr ⟨by simpa using (hΓpos j).le, (hΓpos j).le⟩
  -- The pointwise facts that make the state map of Step 3 well defined.
  have hxbd : ∀ (k n : ℕ) (ω : Ωf k), n ≤ τf k ω →
      ‖(ofLp (zf k n ω)).1‖ ≤ R + 1 := by
    intro k n ω hn
    obtain ⟨hμ1, hεpow, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
      hstep, hrec, hgradc, hτst, hτint, hlive, hexit, hxb, hstart⟩ := hcwf k
    exact hxb n ω hn
  have htr : ∀ (k n : ℕ) (ω : Ωf k),
      (1 / 2 : ℝ) ^ (k + 1) ≤ (ofLp (zf k n ω)).2 ∧ (ofLp (zf k n ω)).2 ≤ (T : ℝ) := by
    intro k
    exact ContactWalkTimeRange κ H v T R (k + 1) (εf k) (Ωf k) (m0f k) (μf k)
      (𝒢f k) (ξf k) (zf k) (zpf k) (zmf k) (Q₀f k) (τf k) (hcwf k) (by omega) (by omega)
  have hBxmem : ∀ (k n : ℕ) (ω : Ωf k), n ≤ τf k ω → zf k n ω ∈ Bx := by
    intro k n ω hn
    have h1 := htr k n ω
    have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    exact ⟨hxbd k n ω hn, Set.mem_Icc.mpr ⟨by linarith [h1.1], h1.2⟩⟩
  -- The fit-parameter bound and the localization event, from `MarkLocalization`.
  have hmark := fun (k j : ℕ) (hj1 : 1 ≤ j) (hjk : j ≤ k + 1) =>
    hloc (k + 1) (by omega) (εf k) (Ωf k) (m0f k) (μf k) (𝒢f k) (ξf k) (zf k) (zpf k)
      (zmf k) (Q₀f k) (τf k) (hcwf k) (hbdf k) (smarkf k) (pjf k) (ajf k) (hmdf k)
      j hj1 hjk
  have hΓeq : ∀ j : ℕ, Γ j = CΓ * ((1 + Real.log (R + (T : ℝ) + 2)) + (j : ℝ)) := by
    intro j
    simp only [hΓ, hLB, hBq]
  have hpΓ : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 → ∀ ω, ‖pjf k j ω‖ ≤ Γ j := by
    intro k j hj1 hjk ω
    have h := (hmark k j hj1 hjk).1 ω
    rw [hΓeq j]
    linarith [abs_nonneg (ajf k j ω)]
  have haΓ : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 → ∀ ω, |ajf k j ω| ≤ Γ j := by
    intro k j hj1 hjk ω
    have h := (hmark k j hj1 hjk).1 ω
    rw [hΓeq j]
    linarith [norm_nonneg (pjf k j ω)]
  -- Borel structures: the state space is a compact metrizable subspace of a
  -- second-countable product, so the Borel sigma-algebras of the factors and of
  -- the product agree and the subtype inherits both.
  let _iF : MeasurableSpace F := borel F
  have hFborel : BorelSpace F := ⟨rfl⟩
  let _iL : MeasurableSpace (WithLp 2 (F × ℝ)) := borel (WithLp 2 (F × ℝ))
  have hLborel : BorelSpace (WithLp 2 (F × ℝ)) := ⟨rfl⟩
  have hStCS : CompactSpace St := isCompact_iff_compactSpace.mp hStcpt
  have hStNE : Nonempty St := hStne.to_subtype
  have hStBorel : BorelSpace St := by infer_instance
  have hStOpens : OpensMeasurableSpace St := by infer_instance
  have hStMetr : TopologicalSpace.MetrizableSpace St := by infer_instance
  have hStT2 : T2Space St := by infer_instance
  -- The measurability device of Step 3: a stopped value of an adapted family is
  -- measurable, because `ℕ` is countable with measurable singletons. It is needed
  -- at two codomains, and a single polymorphic version cannot have its universe
  -- inferred inside a tactic block.
  have hdevZ : ∀ (k : ℕ) (σ : Ωf k → ℕ), (∀ n, MeasurableSet[m0f k] {ω | σ ω = n}) →
      ∀ Y : ℕ → Ωf k → WithLp 2 (F × ℝ),
      (∀ n, @Measurable (Ωf k) (WithLp 2 (F × ℝ)) (m0f k) _ (Y n)) →
      @Measurable (Ωf k) (WithLp 2 (F × ℝ)) (m0f k) _ (fun ω => Y (σ ω) ω) := by
    intro k σ hσ Y hY
    have hσm : @Measurable (Ωf k) ℕ (m0f k) _ σ := by
      refine @measurable_to_countable' ℕ (Ωf k) _ _ (m0f k) _ (fun n => ?_)
      exact hσ n
    have h1 : @Measurable ((Ωf k) × ℕ) (WithLp 2 (F × ℝ)) ((m0f k).prod _) _
        (fun p => Y p.2 p.1) := measurable_from_prod_countable_left hY
    exact h1.comp (Measurable.prodMk measurable_id hσm)
  have hdevM : ∀ (k : ℕ) (σ : Ωf k → ℕ), (∀ n, MeasurableSet[m0f k] {ω | σ ω = n}) →
      ∀ Y : ℕ → Ωf k → (WithLp 2 (F × ℝ) × F × ℝ),
      (∀ n, @Measurable (Ωf k) (WithLp 2 (F × ℝ) × F × ℝ) (m0f k) _ (Y n)) →
      @Measurable (Ωf k) (WithLp 2 (F × ℝ) × F × ℝ) (m0f k) _ (fun ω => Y (σ ω) ω) := by
    intro k σ hσ Y hY
    have hσm : @Measurable (Ωf k) ℕ (m0f k) _ σ := by
      refine @measurable_to_countable' ℕ (Ωf k) _ _ (m0f k) _ (fun n => ?_)
      exact hσ n
    have h1 : @Measurable ((Ωf k) × ℕ) (WithLp 2 (F × ℝ) × F × ℝ) ((m0f k).prod _) _
        (fun p => Y p.2 p.1) := measurable_from_prod_countable_left hY
    exact h1.comp (Measurable.prodMk measurable_id hσm)
  have hlevelset : ∀ (k : ℕ) (σ : Ωf k → ℕ),
      IsStoppingTime (𝒢f k) (fun ω => (σ ω : ℕ∞)) →
      ∀ n, MeasurableSet[m0f k] {ω | σ ω = n} := by
    intro k σ hσ n
    have h2 : {ω : Ωf k | σ ω = n} = {ω | (σ ω : ℕ∞) = (n : ℕ∞)} := by
      ext ω
      simp
    rw [h2]
    exact (𝒢f k).le n _ (hσ.measurableSet_eq_of_countable n)
  have hzm : ∀ (k n : ℕ), @Measurable (Ωf k) (WithLp 2 (F × ℝ)) (m0f k) _ (zf k n) := by
    intro k n
    obtain ⟨hμ1, hεpow, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
      hstep, hrec, hgradc, hτst, hτint, hlive, hexit, hxb, hstart⟩ := hcwf k
    exact ((hzSM n).measurable).mono ((𝒢f k).le n) le_rfl
  have hτst : ∀ k : ℕ, IsStoppingTime (𝒢f k) (fun ω => (τf k ω : ℕ∞)) := by
    intro k
    obtain ⟨hμ1, hεpow, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
      hstep, hrec, hgradc, hst, hτint, hlive, hexit, hxb, hstart⟩ := hcwf k
    exact hst
  have hμ1 : ∀ k : ℕ, μf k Set.univ = 1 := by
    intro k
    obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hcwf k
    exact h1
  -- The state map of Step 3, with the paper's dummy entry outside `1 ≤ j ≤ N`.
  obtain ⟨wmk, hwmk⟩ : ∃ w : (k : ℕ) → ℕ → Ωf k → WithLp 2 (F × ℝ) × F × ℝ,
      w = fun k j ω =>
        if 1 ≤ j ∧ j ≤ k + 1 then (zf k (smarkf k j ω) ω, pjf k j ω, ajf k j ω)
        else (toLp 2 ((0 : F), (1 : ℝ)), 0, 0) := ⟨_, rfl⟩
  obtain ⟨stp, hstp⟩ : ∃ q : (k : ℕ) → Ωf k →
      WithLp 2 (F × ℝ) × Bool × (ℕ → WithLp 2 (F × ℝ) × F × ℝ),
      q = fun k ω => (zf k (τf k ω) ω,
        (if (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1) then true else false),
        fun j => wmk k j ω) := ⟨_, rfl⟩
  have hstpmem : ∀ (k : ℕ) (ω : Ωf k), stp k ω ∈ St := by
    intro k ω
    rw [hstp, hSt]
    refine Set.mk_mem_prod (hBxmem k (τf k ω) ω le_rfl)
      (Set.mk_mem_prod (Set.mem_univ _) ?_)
    intro j _
    simp only [hKbox, hwmk]
    by_cases hj : 1 ≤ j ∧ j ≤ k + 1
    · rw [if_pos hj]
      refine Set.mk_mem_prod
        (hBxmem k (smarkf k j ω) ω ((hmdf k j hj.1 hj.2).2.1 ω))
        (Set.mk_mem_prod ?_ ?_)
      · simpa using hpΓ k j hj.1 hj.2 ω
      · exact Set.mem_Icc.mpr (abs_le.mp (haΓ k j hj.1 hj.2 ω))
    · rw [if_neg hj]
      refine Set.mk_mem_prod hzstarB (Set.mk_mem_prod ?_ ?_)
      · simpa using (hΓpos j).le
      · exact Set.mem_Icc.mpr ⟨by linarith [(hΓpos j).le], (hΓpos j).le⟩
  have hstpm : ∀ k : ℕ,
      @Measurable (Ωf k) (WithLp 2 (F × ℝ) × Bool × (ℕ → WithLp 2 (F × ℝ) × F × ℝ))
        (m0f k) _ (stp k) := by
    intro k
    have hτpart := hlevelset k (τf k) (hτst k)
    have hzτ : @Measurable (Ωf k) (WithLp 2 (F × ℝ)) (m0f k) _
        (fun ω => zf k (τf k ω) ω) :=
      hdevZ k (τf k) hτpart (fun n => zf k n) (fun n => hzm k n)
    have htproj : Measurable fun z : WithLp 2 (F × ℝ) => (ofLp z).2 :=
      (by fun_prop : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).2).measurable
    have hflagset : MeasurableSet[m0f k]
        {ω : Ωf k | (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1)} :=
      (htproj.comp hzτ) (measurableSet_singleton _)
    have hflag : @Measurable (Ωf k) Bool (m0f k) _
        (fun ω => if (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1) then true
          else false) :=
      Measurable.ite hflagset measurable_const measurable_const
    have hwmkm : ∀ j : ℕ,
        @Measurable (Ωf k) (WithLp 2 (F × ℝ) × F × ℝ) (m0f k) _ (wmk k j) := by
      intro j
      by_cases hj : 1 ≤ j ∧ j ≤ k + 1
      · obtain ⟨hsmst, hsmle, hsmlt, hsmalt, hpm5, hpm6, hfit7, hfit8⟩ :=
          hmdf k j hj.1 hj.2
        have hpart := hlevelset k (smarkf k j) hsmst
        have hYm : ∀ n, @Measurable (Ωf k) (WithLp 2 (F × ℝ) × F × ℝ) (m0f k) _
            (fun ω => (zf k n ω, (if smarkf k j ω ≤ n then pjf k j ω else 0),
              (if smarkf k j ω ≤ n then ajf k j ω else 0))) := by
          intro n
          refine (hzm k n).prodMk (Measurable.prodMk ?_ ?_)
          · exact ((hpm5 n).measurable).mono ((𝒢f k).le n) le_rfl
          · exact ((hpm6 n).measurable).mono ((𝒢f k).le n) le_rfl
        have hres := hdevM k (smarkf k j) hpart _ hYm
        have heq : (fun ω => (zf k (smarkf k j ω) ω,
            (if smarkf k j ω ≤ smarkf k j ω then pjf k j ω else 0),
            (if smarkf k j ω ≤ smarkf k j ω then ajf k j ω else 0))) = wmk k j := by
          funext ω
          simp only [hwmk]
          rw [if_pos hj]
          simp
        rw [← heq]
        exact hres
      · have heq : wmk k j = fun _ : Ωf k => (toLp 2 ((0 : F), (1 : ℝ)), (0 : F), (0 : ℝ)) := by
          funext ω
          simp only [hwmk]
          rw [if_neg hj]
        rw [heq]
        exact measurable_const
    rw [hstp]
    exact hzτ.prodMk (hflag.prodMk (Measurable.of_eval hwmkm))
  -- The laws of Step 3 and the pushforward identity.
  obtain ⟨Ψ, hΨ⟩ : ∃ P : (k : ℕ) → Ωf k → St, P = fun k ω => ⟨stp k ω, hstpmem k ω⟩ :=
    ⟨_, rfl⟩
  have hΨm : ∀ k : ℕ, @Measurable (Ωf k) St (m0f k) _ (Ψ k) := by
    intro k
    rw [hΨ]
    exact (hstpm k).subtype_mk
  have hprob : ∀ k : ℕ, IsProbabilityMeasure (μf k) := fun k => ⟨hμ1 k⟩
  obtain ⟨lam, hlam⟩ : ∃ L : ℕ → ProbabilityMeasure St,
      ∀ k, (L k : Measure St) = (μf k).map (Ψ k) := by
    refine ⟨fun k => ⟨(μf k).map (Ψ k), ?_⟩, fun k => rfl⟩
    have := hprob k
    exact (Measure.isProbabilityMeasure_map_iff (hΨm k).aemeasurable).mpr this
  have hpush : ∀ (k : ℕ) (A : Set St), MeasurableSet A →
      (lam k : Measure St) A = μf k (Ψ k ⁻¹' A) := by
    intro k A hA
    rw [hlam k]
    exact Measure.map_apply (hΨm k) hA
  -- Step 4: one limiting law, along a subsequence, by compactness of the space of
  -- probability measures on the compact metrizable state space.
  obtain ⟨lmt, ns, hnsmono, hnstend⟩ : ∃ (L : ProbabilityMeasure St) (ns : ℕ → ℕ),
      StrictMono ns ∧ Tendsto (fun h => lam (ns h)) atTop (𝓝 L) := by
    obtain ⟨L, -, ns, hmono, htend⟩ :=
      (isCompact_univ (X := ProbabilityMeasure St)).tendsto_subseq
        (x := lam) (fun n => Set.mem_univ _)
    exact ⟨L, ns, hmono, htend⟩
  -- Coordinates of the state map, and the box fact about a state.
  have hΨcoord : ∀ (k : ℕ) (ω : Ωf k),
      (Ψ k ω).1.1 = zf k (τf k ω) ω ∧
      ((Ψ k ω).1.2.1 = true ↔ (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1)) ∧
      (Ψ k ω).1.2.2 = fun j => wmk k j ω := by
    intro k ω
    simp only [hΨ, hstp]
    refine ⟨trivial, ?_, trivial⟩
    simp
  have hStfst : ∀ x ∈ St, x.1 ∈ Bx := by
    intro x hx
    rw [hSt] at hx
    exact hx.1
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := Nat.cast_nonneg T
  have hqtime : ∀ q : St, 0 ≤ (ofLp q.1.1).2 ∧ (ofLp q.1.1).2 ≤ (T : ℝ) := by
    intro q
    have h1 := hStfst q.1 q.2
    rw [hBx] at h1
    exact Set.mem_Icc.mp h1.2
  -- Step 5: the terminal time vanishes on the flag.
  obtain ⟨gfl, hgfl⟩ : ∃ g : St → ℝ,
      g = fun q : St => (if q.1.2.1 = true then (1 : ℝ) else 0) * (ofLp q.1.1).2 := ⟨_, rfl⟩
  have hgflc : Continuous gfl := by
    rw [hgfl]
    have h1 : Continuous fun q : St => q.1.2.1 :=
      continuous_fst.comp (continuous_snd.comp continuous_subtype_val)
    have h2 : Continuous fun b : Bool => (if b = true then (1 : ℝ) else 0) :=
      continuous_of_discreteTopology
    have h3 : Continuous fun q : St => (ofLp q.1.1).2 := by
      have hc : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).2 := by fun_prop
      exact hc.comp (continuous_fst.comp continuous_subtype_val)
    exact (h2.comp h1).mul h3
  have hgflnn : ∀ q : St, 0 ≤ gfl q := by
    intro q
    simp only [hgfl]
    refine mul_nonneg ?_ (hqtime q).1
    split <;> norm_num
  have hgflle : ∀ q : St, gfl q ≤ (T : ℝ) := by
    intro q
    simp only [hgfl]
    by_cases hb : q.1.2.1 = true
    · rw [if_pos hb, one_mul]
      exact (hqtime q).2
    · rw [if_neg hb, zero_mul]
      exact hTnn
  have hgflbd : ∀ (k : ℕ) (ω : Ωf k), gfl (Ψ k ω) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k ω
    obtain ⟨hc1, hc2, -⟩ := hΨcoord k ω
    simp only [hgfl]
    by_cases hb : (Ψ k ω).1.2.1 = true
    · rw [if_pos hb, one_mul, hc1, hc2.mp hb]
    · rw [if_neg hb, zero_mul]
      positivity
  have hgfltrans : ∀ k : ℕ,
      ∫ q, gfl q ∂(lam k : Measure St) = ∫ ω, gfl (Ψ k ω) ∂(μf k) := by
    intro k
    rw [hlam k]
    exact integral_map (hΨm k).aemeasurable hgflc.measurable.aestronglyMeasurable
  have hgflint : ∀ k : ℕ, ∫ q, gfl q ∂(lam k : Measure St) ≤ (1 / 2 : ℝ) ^ (k + 1) := by
    intro k
    have := hprob k
    rw [hgfltrans k]
    have hcpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (k + 1) := by positivity
    have hint : Integrable (fun ω => gfl (Ψ k ω)) (μf k) := by
      refine (integrable_const ((1 / 2 : ℝ) ^ (k + 1))).mono
        (hgflc.measurable.comp (hΨm k)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hgflnn (Ψ k ω)),
        abs_of_nonneg hcpos]
      exact hgflbd k ω
    calc ∫ ω, gfl (Ψ k ω) ∂(μf k)
        ≤ ∫ _ω, (1 / 2 : ℝ) ^ (k + 1) ∂(μf k) :=
          integral_mono hint (integrable_const _) (fun ω => hgflbd k ω)
      _ = (1 / 2 : ℝ) ^ (k + 1) := by simp
  have hlimint : ∫ q, gfl q ∂(lmt : Measure St) = 0 := by
    have htend := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hnstend)
      (BoundedContinuousFunction.mkOfCompact ⟨gfl, hgflc⟩)
    simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] at htend
    have hbnd : ∀ h : ℕ, ∫ q, gfl q ∂(lam (ns h) : Measure St) ≤ (1 / 2 : ℝ) ^ (h + 1) := by
      intro h
      refine le_trans (hgflint (ns h)) ?_
      have hh : h ≤ ns h := hnsmono.le_apply
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h0 : Tendsto (fun h : ℕ => (1 / 2 : ℝ) ^ (h + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 2)
        (by norm_num : (1:ℝ) / 2 < 1)).comp (Filter.tendsto_add_atTop_nat 1)
    refine le_antisymm (le_of_tendsto_of_tendsto' htend h0 hbnd) (integral_nonneg hgflnn)
  have hstep5 : ∀ᵐ q ∂(lmt : Measure St), q.1.2.1 = true → (ofLp q.1.1).2 = 0 := by
    have : IsProbabilityMeasure (lmt : Measure St) := lmt.2
    have hint : Integrable gfl (lmt : Measure St) := by
      refine (integrable_const ((T : ℝ) + 1)).mono
        hgflc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall (fun q => ?_))
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hgflnn q),
        abs_of_nonneg (by linarith : (0:ℝ) ≤ (T : ℝ) + 1)]
      linarith [hgflle q]
    have hae := (integral_eq_zero_iff_of_nonneg hgflnn hint).mp hlimint
    filter_upwards [hae] with q hq hflag
    simp only [hgfl, Pi.zero_apply] at hq
    rw [if_pos hflag, one_mul] at hq
    exact hq
  -- Step 6: levels and fits pass to the limit.
  have hvcont : Continuous v := by
    have h := hv.1.1.2.1
    rw [continuousOn_univ] at h
    exact h
  have hqval : Continuous fun q : St => (q : WithLp 2 (F × ℝ) × Bool ×
      (ℕ → WithLp 2 (F × ℝ) × F × ℝ)) := continuous_subtype_val
  have hmkcont : ∀ j : ℕ, Continuous fun q : St => q.1.2.2 j :=
    fun j => (continuous_apply j).comp (continuous_snd.comp (continuous_snd.comp hqval))
  have hmktime : ∀ j : ℕ, Continuous fun q : St => (ofLp (q.1.2.2 j).1).2 := by
    intro j
    have hc : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).2 := by fun_prop
    exact hc.comp (continuous_fst.comp (hmkcont j))
  have hflagcl : IsClosed {q : St | q.1.2.1 = false} := by
    have hc : Continuous fun q : St => q.1.2.1 :=
      continuous_fst.comp (continuous_snd.comp hqval)
    exact (isClosed_discrete {false}).preimage hc
  obtain ⟨Acl, hAcl⟩ : ∃ A : ℕ → Set St, A = fun j =>
      {q : St | (1 / 2 : ℝ) ^ j ≤ (ofLp (q.1.2.2 j).1).2} ∩
      (({q : St | q.1.2.1 = false} ∪
          {q : St | (ofLp (q.1.2.2 j).1).2 = (1 / 2 : ℝ) ^ j}) ∩
        ({q : St | q.1.2.1 = false} ∪
          {q : St | IsFit C₀ v (q.1.2.2 j).1 ((1 / 2 : ℝ) ^ j)
            (q.1.2.2 j).2.1 (q.1.2.2 j).2.2})) := ⟨_, rfl⟩
  have hAclosed : ∀ j : ℕ, IsClosed (Acl j) := by
    intro j
    rw [hAcl]
    refine IsClosed.inter (isClosed_le continuous_const (hmktime j))
      (IsClosed.inter (hflagcl.union ?_) (hflagcl.union ?_))
    · exact isClosed_eq (hmktime j) continuous_const
    · exact (FitSetClosed C₀ v hvcont ((1 / 2 : ℝ) ^ j) (by positivity)).preimage (hmkcont j)
  have hAmem : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 → ∀ ω : Ωf k, Ψ k ω ∈ Acl j := by
    intro k j hj1 hjk ω
    obtain ⟨-, hc2, hc3⟩ := hΨcoord k ω
    obtain ⟨hsmst, hsmle, hsmlt, hsmalt, hpm5, hpm6, hfit7, hfit8⟩ := hmdf k j hj1 hjk
    have hmkval : (Ψ k ω).1.2.2 j
        = (zf k (smarkf k j ω) ω, pjf k j ω, ajf k j ω) := by
      rw [hc3]
      simp only [hwmk]
      rw [if_pos ⟨hj1, hjk⟩]
    have hlv := hlevels k j hj1 hjk
    rw [hAcl]
    refine Set.mem_inter ?_ (Set.mem_inter ?_ ?_)
    · rw [Set.mem_ofPred_eq, hmkval]
      exact hlv.1 ω
    · by_cases hb : (Ψ k ω).1.2.1 = true
      · refine Or.inr ?_
        rw [Set.mem_ofPred_eq, hmkval]
        exact hlv.2 ω (hc2.mp hb)
      · refine Or.inl ?_
        rw [Set.mem_ofPred_eq]
        cases hbv : (Ψ k ω).1.2.1 with
        | false => rfl
        | true => exact absurd hbv hb
    · by_cases hb : (Ψ k ω).1.2.1 = true
      · refine Or.inr ?_
        rw [Set.mem_ofPred_eq, hmkval]
        exact hfit7 ω (hlv.2 ω (hc2.mp hb))
      · refine Or.inl ?_
        rw [Set.mem_ofPred_eq]
        cases hbv : (Ψ k ω).1.2.1 with
        | false => rfl
        | true => exact absurd hbv hb
  have hAlam : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 → (lam k : Measure St) (Acl j) = 1 := by
    intro k j hj1 hjk
    have hu : Ψ k ⁻¹' Acl j = Set.univ := Set.eq_univ_of_forall (hAmem k j hj1 hjk)
    rw [hpush k _ (hAclosed j).measurableSet, hu]
    exact hμ1 k
  have hAlmt : ∀ j : ℕ, 1 ≤ j → (lmt : Measure St) (Acl j) = 1 := by
    intro j hj
    have hpm := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hnstend
      (hAclosed j)
    have hev : ∀ᶠ h in atTop, (lam (ns h) : Measure St) (Acl j) = (1 : ENNReal) := by
      filter_upwards [Filter.eventually_ge_atTop j] with h hh
      have hh2 : h ≤ ns h := hnsmono.le_apply
      exact hAlam (ns h) j hj (by omega)
    have hls : Filter.limsup (fun h => (lam (ns h) : Measure St) (Acl j)) atTop
        = (1 : ENNReal) := (Filter.limsup_congr hev).trans (Filter.limsup_const 1)
    have h1 : (1 : ENNReal) ≤ (lmt : Measure St) (Acl j) := by
      rw [← hls]
      exact hpm
    have : IsProbabilityMeasure (lmt : Measure St) := lmt.2
    exact le_antisymm prob_le_one h1
  have hstep6 : ∀ᵐ q ∂(lmt : Measure St), ∀ j : ℕ, 1 ≤ j → q ∈ Acl j := by
    have : IsProbabilityMeasure (lmt : Measure St) := lmt.2
    rw [MeasureTheory.ae_all_iff]
    intro j
    by_cases hj : 1 ≤ j
    · have hc : (lmt : Measure St) (Acl j)ᶜ = 0 := by
        rw [prob_compl_eq_one_sub (hAclosed j).measurableSet, hAlmt j hj]
        simp
      filter_upwards [MeasureTheory.mem_ae_iff.mpr hc] with q hq _
      exact hq
    · exact Filter.Eventually.of_forall (fun q hjj => absurd hjj hj)
  -- Step 10, first half: the localization events and their limiting mass.
  obtain ⟨Ecl, hEcl⟩ : ∃ E : ℕ → Set St, E = fun j =>
      {q : St | q.1.2.1 = true} ∩
      {q : St | ‖(ofLp q.1.1).1 - (ofLp (q.1.2.2 j).1).1
        - ((ofLp q.1.1).2 - (1 / 2 : ℝ) ^ j) • (q.1.2.2 j).2.1‖
        ≤ Kloc * (1 / 2 : ℝ) ^ j} := ⟨_, rfl⟩
  have hEclosed : ∀ j : ℕ, IsClosed (Ecl j) := by
    intro j
    rw [hEcl]
    refine IsClosed.inter ?_ ?_
    · have hc : Continuous fun q : St => q.1.2.1 :=
        continuous_fst.comp (continuous_snd.comp hqval)
      exact (isClosed_discrete {true}).preimage hc
    · refine isClosed_le ?_ continuous_const
      have h1 : Continuous fun q : St => (ofLp q.1.1).1 := by
        have hc : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).1 := by fun_prop
        exact hc.comp (continuous_fst.comp hqval)
      have h2 : Continuous fun q : St => (ofLp q.1.1).2 := by
        have hc : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).2 := by fun_prop
        exact hc.comp (continuous_fst.comp hqval)
      have h3 : Continuous fun q : St => (ofLp (q.1.2.2 j).1).1 := by
        have hc : Continuous fun z : WithLp 2 (F × ℝ) => (ofLp z).1 := by fun_prop
        exact hc.comp (continuous_fst.comp (hmkcont j))
      have h4 : Continuous fun q : St => (q.1.2.2 j).2.1 :=
        continuous_fst.comp (continuous_snd.comp (hmkcont j))
      exact ((h1.sub h3).sub ((h2.sub continuous_const).smul h4)).norm
  have hEpre : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 →
      Ψ k ⁻¹' Ecl j = {ω : Ωf k | (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1) ∧
        ‖(ofLp (zf k (τf k ω) ω)).1 - (ofLp (zf k (smarkf k j ω) ω)).1
          - ((ofLp (zf k (τf k ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pjf k j ω‖
          ≤ Kloc * (1 / 2 : ℝ) ^ j} := by
    intro k j hj1 hjk
    ext ω
    obtain ⟨hc1, hc2, hc3⟩ := hΨcoord k ω
    have hmkval : (Ψ k ω).1.2.2 j
        = (zf k (smarkf k j ω) ω, pjf k j ω, ajf k j ω) := by
      rw [hc3]
      simp only [hwmk]
      rw [if_pos ⟨hj1, hjk⟩]
    simp only [hEcl, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
      hmkval, hc1]
    exact and_congr_left (fun _ => hc2)
  have hElam : ∀ (k j : ℕ), 1 ≤ j → j ≤ k + 1 →
      ENNReal.ofReal ((1 : ℝ) / 2) ≤ (lam k : Measure St) (Ecl j) := by
    intro k j hj1 hjk
    have hms := (hmark k j hj1 hjk).2.2.1
    have hmes := (hmark k j hj1 hjk).2.2.2
    rw [hpush k _ (hEclosed j).measurableSet, hEpre k j hj1 hjk]
    calc ENNReal.ofReal ((1 : ℝ) / 2)
        ≤ ENNReal.ofReal ((μf k {ω | (ofLp (zf k (τf k ω) ω)).2 = (1 / 2 : ℝ) ^ (k + 1) ∧
            ‖(ofLp (zf k (τf k ω) ω)).1 - (ofLp (zf k (smarkf k j ω) ω)).1
              - ((ofLp (zf k (τf k ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pjf k j ω‖
              ≤ Kloc * (1 / 2 : ℝ) ^ j}).toReal) := ENNReal.ofReal_le_ofReal hmes
      _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hElmt : ∀ j : ℕ, 1 ≤ j →
      ENNReal.ofReal ((1 : ℝ) / 2) ≤ (lmt : Measure St) (Ecl j) := by
    intro j hj
    have hpm := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hnstend
      (hEclosed j)
    refine le_trans ?_ hpm
    refine Filter.le_limsup_of_frequently_le ?_
    refine Filter.Eventually.frequently ?_
    filter_upwards [Filter.eventually_ge_atTop j] with h hh
    have hh2 : h ≤ ns h := hnsmono.le_apply
    exact hElam (ns h) j hj (by omega)
  -- Step 7: the uniform upper bound for `J_ε` on the box, and the averaged
  -- envelope slope that Step 8 passes to the limit.
  obtain ⟨UB, hUB⟩ := JBoxUpperBound C₀ κ hC₀ hκ.le v hv hcent hJ Bx hBxcpt
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc η hη
    obtain ⟨M, hM, hbd⟩ :=
      UniformSubquadratic C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc η hη
    exact ⟨M, hM, fun z hz1 hz2 => hbd v hv hcent z hz1 hz2⟩
  have hvcontI : ContinuousOn v ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hv.1.1.2.1
  obtain ⟨-, -, hcP, hcM, -, -⟩ :=
    QuadEnvAttained (F := F) Set.univ isOpen_univ v hvcontI hvgrow
  obtain ⟨hslmono, hslinf, -, -⟩ :=
    EnvHamiltonianSolution (F := F) Set.univ isOpen_univ v hvcontI hvgrow hv.1
  obtain ⟨Phi, hPhi⟩ : ∃ P : ℝ → WithLp 2 (F × ℝ) → ℝ,
      P = fun l z => (EnvSlopeP v l z + EnvSlopeM v l z) / 2 := ⟨_, rfl⟩
  have hPhicont : ∀ l : ℝ, 0 < l → Continuous (Phi l) := by
    intro l hl
    have hPc : Continuous fun z : WithLp 2 (F × ℝ) => QuadEnvP v l z := by
      rw [continuous_iff_continuousAt]
      intro z₀
      exact (hcP l hl z₀ (Set.mem_univ _) (Set.mem_univ _)).comp
        (by fun_prop : ContinuousAt (fun z : WithLp 2 (F × ℝ) => (l, z)) z₀)
    have hMc : Continuous fun z : WithLp 2 (F × ℝ) => QuadEnvM v l z := by
      rw [continuous_iff_continuousAt]
      intro z₀
      exact (hcM l hl z₀ (Set.mem_univ _) (Set.mem_univ _)).comp
        (by fun_prop : ContinuousAt (fun z : WithLp 2 (F × ℝ) => (l, z)) z₀)
    have hrw : Phi l = fun z => (QuadEnvP v l z - QuadEnvM v l z) / (2 * l) := by
      funext z
      simp only [hPhi, EnvSlopeP, EnvSlopeM]
      field_simp
      ring
    rw [hrw]
    fun_prop
  have hPhimono : ∀ (z : WithLp 2 (F × ℝ)) (l l' : ℝ), 0 < l → l ≤ l' →
      Phi l z ≤ Phi l' z := by
    intro z l l' hl hll
    obtain ⟨h1, h2⟩ := hslmono z l l' hl hll (fun σ _ => Set.mem_univ _)
    simp only [hPhi]
    linarith
  have hSPmono : ∀ (z : WithLp 2 (F × ℝ)) (l l' : ℝ), 0 < l → l ≤ l' →
      EnvSlopeP v l z ≤ EnvSlopeP v l' z :=
    fun z l l' hl hll => (hslmono z l l' hl hll (fun σ _ => Set.mem_univ _)).1
  have hSMmono : ∀ (z : WithLp 2 (F × ℝ)) (l l' : ℝ), 0 < l → l ≤ l' →
      EnvSlopeM v l z ≤ EnvSlopeM v l' z :=
    fun z l l' hl hll => (hslmono z l l' hl hll (fun σ _ => Set.mem_univ _)).2
  have hSPcont : Continuous fun z : WithLp 2 (F × ℝ) => EnvSlopeP v 1 z := by
    have hPc : Continuous fun z : WithLp 2 (F × ℝ) => QuadEnvP v 1 z := by
      rw [continuous_iff_continuousAt]
      intro z₀
      exact (hcP 1 one_pos z₀ (Set.mem_univ _) (Set.mem_univ _)).comp
        (by fun_prop : ContinuousAt (fun z : WithLp 2 (F × ℝ) => ((1 : ℝ), z)) z₀)
    have hrw : (fun z : WithLp 2 (F × ℝ) => EnvSlopeP v 1 z)
        = fun z => QuadEnvP v 1 z - v z := by
      funext z
      simp only [EnvSlopeP, div_one]
    rw [hrw]
    exact hPc.sub hvcont
  obtain ⟨zmx, hzmx, hmaxPhi⟩ := hBxcpt.exists_isMaxOn ⟨_, hzstarB⟩ (hPhicont 1 one_pos).continuousOn
  obtain ⟨zmp, hzmp, hmaxSP⟩ := hBxcpt.exists_isMaxOn ⟨_, hzstarB⟩ hSPcont.continuousOn
  have hUB1 : ∀ z ∈ Bx, Phi 1 z ≤ Phi 1 zmx := fun z hz => hmaxPhi hz
  have hUP1 : ∀ z ∈ Bx, EnvSlopeP v 1 z ≤ EnvSlopeP v 1 zmp := fun z hz => hmaxSP hz
  -- Step 8, first half: the averaged slope of the terminal point has integral at
  -- least `H - 1` against the limiting law, for every length.
  have hzτm : ∀ k : ℕ, @Measurable (Ωf k) (WithLp 2 (F × ℝ)) (m0f k) _
      (fun ω => zf k (τf k ω) ω) := by
    intro k
    exact hdevZ k (τf k) (hlevelset k (τf k) (hτst k)) (fun n => zf k n) (fun n => hzm k n)
  have hεpos : ∀ k : ℕ, 0 < εf k := by
    intro k
    obtain ⟨-, -, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hcwf k
    exact h
  have hεsmall : ∀ k : ℕ, εf k ≤ (1 / 2 : ℝ) ^ (k + 1) / 4 := by
    intro k
    obtain ⟨-, -, -, h, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hcwf k
    exact h
  have hstart : ∀ k : ℕ, H - 1 ≤ JGap v κ (εf k) (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro k
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h⟩ := hcwf k
    exact h
  have htpos : ∀ (k n : ℕ) (ω : Ωf k), 0 < (ofLp (zf k n ω)).2 := by
    intro k n ω
    have h1 := (htr k n ω).1
    have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ (k + 1) := by positivity
    linarith
  have hPhibd : ∀ l : ℝ, 0 < l → ∃ Cl : ℝ, ∀ z ∈ Bx, ‖Phi l z‖ ≤ Cl :=
    fun l hl => hBxcpt.exists_bound_of_continuousOn (hPhicont l hl).continuousOn
  have hPhiint : ∀ (k : ℕ) (l : ℝ), 0 < l →
      Integrable (fun ω => Phi l (zf k (τf k ω) ω)) (μf k) := by
    intro k l hl
    have := hprob k
    obtain ⟨Cl, hCl⟩ := hPhibd l hl
    refine (integrable_const Cl).mono
      (((hPhicont l hl).measurable.comp (hzτm k)).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => ?_))
    refine le_trans (hCl _ (hBxmem k (τf k ω) ω le_rfl)) ?_
    exact le_abs_self Cl
  have hPhiτ : ∀ (k : ℕ) (l : ℝ), 0 < l → εf k ≤ l →
      H - 1 ≤ ∫ ω, Phi l (zf k (τf k ω) ω) ∂(μf k) := by
    intro k l hl hεl
    obtain ⟨hJi, hJb⟩ := hstopf k (τf k) (hτst k) (fun ω => le_rfl)
    refine le_trans (le_trans (hstart k) hJb) ?_
    refine integral_mono hJi (hPhiint k l hl) (fun ω => ?_)
    have h1 := JUpperBound C₀ κ hC₀ hκ.le v hv hcent hJ (εf k) (zf k (τf k ω) ω)
      (hεpos k) (htpos k (τf k ω) ω)
    have h2 := hPhimono (zf k (τf k ω) ω) (εf k) l (hεpos k) hεl
    simp only [hPhi] at h2 ⊢
    linarith
  have hPhilam : ∀ (k : ℕ) (l : ℝ), 0 < l →
      ∫ q, Phi l (q : WithLp 2 (F × ℝ) × Bool ×
        (ℕ → WithLp 2 (F × ℝ) × F × ℝ)).1 ∂(lam k : Measure St)
        = ∫ ω, Phi l (zf k (τf k ω) ω) ∂(μf k) := by
    intro k l hl
    rw [hlam k]
    have hc : Continuous fun q : St => Phi l q.1.1 :=
      (hPhicont l hl).comp (continuous_fst.comp hqval)
    rw [integral_map (hΨm k).aemeasurable hc.measurable.aestronglyMeasurable]
    exact integral_congr_ae
      (Filter.Eventually.of_forall (fun ω => congrArg (Phi l) (hΨcoord k ω).1))
  have hPhilmt : ∀ l : ℝ, 0 < l →
      H - 1 ≤ ∫ q, Phi l (q : WithLp 2 (F × ℝ) × Bool ×
        (ℕ → WithLp 2 (F × ℝ) × F × ℝ)).1 ∂(lmt : Measure St) := by
    intro l hl
    have hc : Continuous fun q : St => Phi l q.1.1 :=
      (hPhicont l hl).comp (continuous_fst.comp hqval)
    have htend := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hnstend)
      (BoundedContinuousFunction.mkOfCompact ⟨fun q : St => Phi l q.1.1, hc⟩)
    simp only [BoundedContinuousFunction.mkOfCompact_apply, ContinuousMap.coe_mk] at htend
    refine ge_of_tendsto htend ?_
    obtain ⟨n0, hn0⟩ := exists_pow_lt_of_lt_one hl (by norm_num : (1 : ℝ) / 2 < 1)
    filter_upwards [Filter.eventually_ge_atTop n0] with h hh
    have hh2 : h ≤ ns h := hnsmono.le_apply
    have hεle : εf (ns h) ≤ l := by
      refine le_trans (hεsmall (ns h)) (le_trans ?_ hn0.le)
      have h3 : (1 / 2 : ℝ) ^ (ns h + 1) ≤ (1 / 2 : ℝ) ^ n0 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h4 : (0 : ℝ) < (1 / 2 : ℝ) ^ (ns h + 1) := by positivity
      linarith
    rw [hPhilam (ns h) l hl]
    exact hPhiτ (ns h) l hl hεle
  -- Step 8, second half: the envelope Hamiltonian is finite at the terminal point.
  have hlpos : ∀ i : ℕ, (0 : ℝ) < (1 / 2 : ℝ) ^ (i + 1) := fun i => by positivity
  have hlle1 : ∀ i : ℕ, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
    intro i
    calc (1 / 2 : ℝ) ^ (i + 1)
        ≤ (1 / 2 : ℝ) ^ 0 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 := by norm_num
  have hPhicoordc : ∀ l : ℝ, 0 < l → Continuous fun q : St => Phi l q.1.1 :=
    fun l hl => (hPhicont l hl).comp (continuous_fst.comp hqval)
  have hPhicoordint : ∀ l : ℝ, 0 < l →
      Integrable (fun q : St => Phi l q.1.1) (lmt : Measure St) := by
    intro l hl
    have := lmt.2
    obtain ⟨Cl, hCl⟩ := hPhibd l hl
    refine (integrable_const Cl).mono
      ((hPhicoordc l hl).measurable.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun q => ?_))
    exact le_trans (hCl _ (hStfst q.1 q.2)) (le_abs_self Cl)
  obtain ⟨gH, hgH⟩ : ∃ g : ℕ → St → ℝ,
      g = fun i q => Phi 1 zmx - Phi ((1 / 2 : ℝ) ^ (i + 1)) q.1.1 := ⟨_, rfl⟩
  have hgHmeas : ∀ i : ℕ, Measurable (gH i) := by
    intro i
    rw [hgH]
    exact measurable_const.sub (hPhicoordc _ (hlpos i)).measurable
  have hgHnn : ∀ (i : ℕ) (q : St), 0 ≤ gH i q := by
    intro i q
    have h1 := hPhimono q.1.1 ((1 / 2 : ℝ) ^ (i + 1)) 1 (hlpos i) (hlle1 i)
    have h2 := hUB1 q.1.1 (hStfst q.1 q.2)
    simp only [hgH]
    linarith
  have hgHmono : ∀ (i : ℕ) (q : St), gH i q ≤ gH (i + 1) q := by
    intro i q
    have h1 : (1 / 2 : ℝ) ^ (i + 1 + 1) ≤ (1 / 2 : ℝ) ^ (i + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 := hPhimono q.1.1 ((1 / 2 : ℝ) ^ (i + 1 + 1)) ((1 / 2 : ℝ) ^ (i + 1))
      (hlpos (i + 1)) h1
    simp only [hgH]
    linarith
  have hgHint : ∀ i : ℕ, Integrable (gH i) (lmt : Measure St) := by
    intro i
    rw [hgH]
    exact (integrable_const (Phi 1 zmx)).sub (hPhicoordint _ (hlpos i))
  have hgHbd : ∀ i : ℕ, ∫ q, gH i q ∂(lmt : Measure St) ≤ Phi 1 zmx - (H - 1) := by
    intro i
    have := lmt.2
    have hrw : ∫ q, gH i q ∂(lmt : Measure St)
        = Phi 1 zmx - ∫ q, Phi ((1 / 2 : ℝ) ^ (i + 1)) q.1.1 ∂(lmt : Measure St) := by
      rw [hgH]
      rw [integral_sub (integrable_const (Phi 1 zmx)) (hPhicoordint _ (hlpos i))]
      simp
    rw [hrw]
    have := hPhilmt ((1 / 2 : ℝ) ^ (i + 1)) (hlpos i)
    linarith
  have hbddH := MonotoneLimitFiniteAE (lmt : Measure St) gH (Phi 1 zmx - (H - 1))
    hgHmeas hgHnn hgHmono hgHint hgHbd
  have hstep8 : ∀ᵐ q ∂(lmt : Measure St), (⊥ : EReal) < EnvHamiltonian v q.1.1 := by
    filter_upwards [hbddH] with q hq
    obtain ⟨Cq, hCq⟩ := hq
    have hPhilow : ∀ l : ℝ, 0 < l → Phi 1 zmx - Cq ≤ Phi l q.1.1 := by
      intro l hl
      obtain ⟨i, hi⟩ := exists_pow_lt_of_lt_one hl (by norm_num : (1 : ℝ) / 2 < 1)
      have h1 : (1 / 2 : ℝ) ^ (i + 1) ≤ l := by
        refine le_trans ?_ hi.le
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h2 : gH i q ≤ Cq := hCq ⟨i, rfl⟩
      have h3 := hPhimono q.1.1 ((1 / 2 : ℝ) ^ (i + 1)) l (hlpos i) h1
      simp only [hgH] at h2
      linarith
    have hSMlow1 : ∀ l : ℝ, 0 < l → l ≤ 1 →
        2 * (Phi 1 zmx - Cq) - EnvSlopeP v 1 zmp ≤ EnvSlopeM v l q.1.1 := by
      intro l hl hl1
      have h1 := hPhilow l hl
      have h2 : EnvSlopeP v l q.1.1 ≤ EnvSlopeP v 1 zmp :=
        le_trans (hSPmono q.1.1 l 1 hl hl1) (hUP1 q.1.1 (hStfst q.1 q.2))
      simp only [hPhi] at h1 ⊢
      linarith
    have hSMlow : ∀ l : ℝ, 0 < l →
        2 * (Phi 1 zmx - Cq) - EnvSlopeP v 1 zmp ≤ EnvSlopeM v l q.1.1 := by
      intro l hl
      rcases le_total l 1 with hl1 | hl1
      · exact hSMlow1 l hl hl1
      · exact le_trans (hSMlow1 1 one_pos le_rfl) (hSMmono q.1.1 1 l one_pos hl1)
    rw [← hslinf q.1.1 (fun σ => Set.mem_univ _)]
    refine lt_of_lt_of_le
      (EReal.bot_lt_coe (2 * (Phi 1 zmx - Cq) - EnvSlopeP v 1 zmp)) ?_
    refine le_iInf₂ (fun l hl => ?_)
    exact_mod_cast hSMlow l hl
  -- Step 9: contact at every limiting mark.
  -- the whole argument is `ContactAtLimitingMarks`: it sees the state space only as a
  -- topological measurable space with a continuous mark map, and the walk family only
  -- through the pushforward, the box bound `hUB` and the averaged gap bound along the
  -- marks, so none of Step 3's construction travels with it.
  obtain ⟨-, hgap2⟩ := ContactGapLimit C₀ κ hC₀ hκ.le v hv hcent hJ
  have hstep9 : ∀ᵐ q ∂(lmt : Measure St), ∀ j : ℕ, 1 ≤ j →
      ContactEnv v κ (q.1.2.2 j).1 = v (q.1.2.2 j).1 := by
    refine ContactAtLimitingMarks (St := St) (Ωf := Ωf) (m0f := m0f) v κ H UB hvcont hWcont
      (fun z hz => (hsand z hz).2) hgap2 Bx hBxcpt hUB
      (fun q j => (q.1.2.2 j).1) (fun j => continuous_fst.comp (hmkcont j))
      lmt lam ns (fun h => hnsmono.le_apply) hnstend Acl hAclosed hAlmt
      (fun j q hq => by rw [hAcl] at hq; exact hq.1)
      μf hprob Ψ hΨm hpush zf smarkf εf hεpos hεsmall htpos ?_ ?_ ?_
    · intro k j ω hj1 hjk
      have h1 : (Ψ k ω).1.2.2 j
          = (zf k (smarkf k j ω) ω, pjf k j ω, ajf k j ω) := by
        rw [(hΨcoord k ω).2.2]
        simp only [hwmk]
        rw [if_pos ⟨hj1, hjk⟩]
      rw [h1]
    · intro k j hj1 hjk ω
      obtain ⟨-, hmsmle, -, -, -, -, -, -⟩ := hmdf k j hj1 hjk
      exact hBxmem k (smarkf k j ω) ω (hmsmle ω)
    · intro k j hj1 hjk
      obtain ⟨hmsmst, hmsmle, -, -, -, -, -, -⟩ := hmdf k j hj1 hjk
      obtain ⟨hfi, hfb⟩ := hstopf k (smarkf k j) hmsmst hmsmle
      exact ⟨hfi, le_trans (hstart k) hfb⟩
  -- Step 10, second half: the selection and the conclusion.
  have hlmtprob : IsProbabilityMeasure (lmt : Measure St) := lmt.2
  obtain ⟨Gs, hGs⟩ : ∃ G : Set St, G = {q : St |
      (q.1.2.1 = true → (ofLp q.1.1).2 = 0) ∧
      (∀ j : ℕ, 1 ≤ j → q ∈ Acl j) ∧
      ((⊥ : EReal) < EnvHamiltonian v q.1.1) ∧
      (∀ j : ℕ, 1 ≤ j → ContactEnv v κ (q.1.2.2 j).1 = v (q.1.2.2 j).1)} := ⟨_, rfl⟩
  have hGnull : (lmt : Measure St) Gsᶜ = 0 := by
    have hcomb : ∀ᵐ q ∂(lmt : Measure St), q ∈ Gs := by
      filter_upwards [hstep5, hstep6, hstep8, hstep9] with q h5 h6 h8 h9
      rw [hGs]
      exact ⟨h5, h6, h8, h9⟩
    rw [← MeasureTheory.mem_ae_iff]
    exact hcomb
  obtain ⟨qs, hqsG, hqsinf⟩ := TailEventSelection (lmt : Measure St)
    (ENNReal.ofReal ((1 : ℝ) / 2)) (by simp) Ecl
    (fun j => (hEclosed j).measurableSet) hElmt Gs hGnull
  rw [hGs] at hqsG
  obtain ⟨hG5, hG6, hG8, hG9⟩ := hqsG
  -- the flag is `true` at the selected point, because the index set is nonempty
  obtain ⟨j0, hj0⟩ := hqsinf.nonempty
  have hflagtrue : qs.1.2.1 = true := by
    have h1 := hj0.2
    rw [hEcl] at h1
    exact h1.1
  have htend0 : (ofLp qs.1.1).2 = 0 := hG5 hflagtrue
  obtain ⟨xend, hxend⟩ : ∃ x : F, x = (ofLp qs.1.1).1 := ⟨_, rfl⟩
  have hzend : toLp 2 (xend, (0 : ℝ)) = qs.1.1 := by
    rw [hxend, ← htend0]
  refine ⟨Kloc, xend, {j : ℕ | 1 ≤ j ∧ qs ∈ Ecl j}, by linarith, hqsinf,
    fun j hj => hj.1, ?_, ?_⟩
  · rw [hzend]
    exact hG8
  · intro j hj
    obtain ⟨hj1, hjE⟩ := hj
    have hAj := hG6 j hj1
    rw [hAcl] at hAj
    have htj : (ofLp (qs.1.2.2 j).1).2 = (1 / 2 : ℝ) ^ j := by
      rcases hAj.2.1 with h | h
      · rw [Set.mem_ofPred_eq] at h
        rw [hflagtrue] at h
        exact absurd h (by simp)
      · rw [Set.mem_ofPred_eq] at h
        exact h
    have hfitj : IsFit C₀ v (qs.1.2.2 j).1 ((1 / 2 : ℝ) ^ j)
        (qs.1.2.2 j).2.1 (qs.1.2.2 j).2.2 := by
      rcases hAj.2.2 with h | h
      · rw [Set.mem_ofPred_eq] at h
        rw [hflagtrue] at h
        exact absurd h (by simp)
      · rw [Set.mem_ofPred_eq] at h
        exact h
    obtain ⟨xj, hxj⟩ : ∃ x : F, x = (ofLp (qs.1.2.2 j).1).1 := ⟨_, rfl⟩
    have hzj : toLp 2 (xj, (1 / 2 : ℝ) ^ j) = (qs.1.2.2 j).1 := by
      rw [hxj, ← htj]
    refine ⟨xj, (qs.1.2.2 j).2.1, (qs.1.2.2 j).2.2, ?_, ?_, ?_⟩
    · rw [hzj]
      exact hfitj
    · rw [hzj]
      exact hG9 j hj1
    · have hE := hjE
      rw [hEcl] at hE
      have hbd := hE.2
      rw [Set.mem_ofPred_eq, htend0] at hbd
      have hrw : (ofLp qs.1.1).1 - (ofLp (qs.1.2.2 j).1).1
          - ((0 : ℝ) - (1 / 2 : ℝ) ^ j) • (qs.1.2.2 j).2.1
          = xend - xj + ((1 / 2 : ℝ) ^ j) • (qs.1.2.2 j).2.1 := by
        rw [hxend, hxj, zero_sub, neg_smul, sub_neg_eq_add]
      rw [hrw] at hbd
      exact hbd
