module

public import InfHarmonic.IsContactWalk
public import InfHarmonic.DPLogVelocity
public import InfHarmonic.WalkPathwiseBounds
public import InfHarmonic.DoobL2Maximal
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.EnvHamiltonian
public import InfHarmonic.EnvelopeCompetitorBounds
public import InfHarmonic.LatticeLogGreenFunction
public import InfHarmonic.IntegralSqrtProductCauchySchwarz
public import InfHarmonic.StoppedPortionTravelBound
public import InfHarmonic.StoppedLatticeSupersolutionBound
public import InfHarmonic.StoppedWalkLowerExitProbability

@[expose] public section
set_option maxHeartbeats 600000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.7, part 2: for the pair supplied by the extremal envelope
contact and the error constant `C_*` of the budget, there are an integer
`T ≥ 8` and a radius `R` for which every stopped contact walk obeys the travel
inequality (6.22) --- in the generality of the displacement from the start of a
stopped portion, measured in a sheared frame of slope `p` and scale `r` --- and
reaches the lower time level with probability at least `3/4`. -/
theorem StoppedWalkTravel (C₀ κ H : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ)
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
      (𝓝[>] (0 : ℝ)) (𝓝 H))
    (Cstar : ℝ) (hCstar : 0 < Cstar) :
    ∃ (T : ℕ) (R : ℝ), 8 ≤ T ∧ 2 ≤ R ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω)
        (μ : Measure Ω) (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
        (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ),
        IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ →
        ∫ ω, (∑ n ∈ Finset.range (τ ω),
          (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
            + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ
          ≤ Cstar * (1 + Real.log (R + (T : ℝ) + 2)) ^ 4 →
        (∀ (ρ σ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ρ ω : ℕ∞)) →
            IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) →
            ∀ hρσ : (∀ ω, ρ ω ≤ σ ω), (∀ ω, σ ω ≤ τ ω) →
            ∀ (p : Ω → F) (Cp r : ℝ), 0 < r → (∀ ω, ‖p ω‖ ≤ Cp) →
            (∀ n, StronglyMeasurable[𝒢 n] (fun ω => if ρ ω ≤ n then p ω else 0)) →
            Integrable (fun ω => (Finset.Icc (ρ ω) (σ ω)).sup'
                (Finset.nonempty_Icc.mpr (hρσ ω))
                (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
                  - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖)) μ ∧
            Integrable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) μ ∧
            Integrable (fun ω => (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ))) μ ∧
            Integrable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
                  + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) μ ∧
            ∫ ω, (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
                (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
                  - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖) ∂μ
              ≤ 2 * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                    (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ)
                + Real.sqrt (∫ ω, (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)) ∂μ)
                  * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                      (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
                        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1)
                            - Q₀ n ω‖ ^ 2)) ∂μ)) ∧
        (MeasurableSet {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N} ∧
          (3 : ℝ) / 4 ≤ (μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}).toReal) := by
  classical
  -- the six standing properties of the extremal contact pair enter through the
  -- nodes cited below; those not consumed directly are recorded here.
  have _unused_hWsub : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2}
      (ContactEnv v κ) := hWsub
  have _unused_hW0 : ContactEnv v κ (toLp 2 ((0 : F), (1 : ℝ))) = 0 := hW0
  have _unused_hv0 : v (toLp 2 ((0 : F), (1 : ℝ))) = 0 := hv0
  have _unused_hconc : ∀ t : ℝ, 0 < t → ConcaveOn ℝ (Set.univ : Set F)
      (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t)) := hconc
  have _unused_hgap : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z = v z →
      (BaryEnv v (ofLp z).2 z - v z) / (ofLp z).2 = κ ^ 2 / 2 := hgap
  have _unused_hham : EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal) := hham
  have _unused_hslope : Tendsto
      (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 H) := hslope
  -- ===== Step 0: the constants, and the choice of `T = 8` and `R`. =====
  obtain ⟨C₂, hC₂0, hC₂b⟩ := DPLogVelocity (F := F) C₀ hC₀ κ hκ.le
  obtain ⟨Λ₀, hΛ₀d⟩ : ∃ r : ℝ, r = 32 * Real.sqrt 8 + 8 * Real.log 8 ^ 2 := ⟨_, rfl⟩
  have hΛ₀0 : (0:ℝ) ≤ Λ₀ := by rw [hΛ₀d]; positivity
  obtain ⟨CV, hCVd⟩ : ∃ r : ℝ, r = 16 * C₂ ^ 2 + 4 * C₂ ^ 2 * Λ₀ := ⟨_, rfl⟩
  have hCV0 : (0:ℝ) ≤ CV := by rw [hCVd]; positivity
  obtain ⟨C', hC'd⟩ : ∃ r : ℝ, r = 2 * Real.sqrt CV + Real.sqrt (8 * Cstar) := ⟨_, rfl⟩
  have hC'0 : (0:ℝ) ≤ C' := by rw [hC'd]; positivity
  obtain ⟨R, hRd⟩ : ∃ r : ℝ, r = max 10 (2500 * (8 * C') ^ 2) := ⟨_, rfl⟩
  have hR10 : (10:ℝ) ≤ R := by rw [hRd]; exact le_max_left _ _
  have hRc : 2500 * (8 * C') ^ 2 ≤ R := by rw [hRd]; exact le_max_right _ _
  -- the fourth-root bound on the log square
  have hlogsq : ∀ K : ℝ, 1 ≤ K → (1 + Real.log K) ^ 2 ≤ 16 * Real.sqrt K := by
    intro K hK
    have hK0 : (0:ℝ) < K := by linarith only [hK]
    have hs1 : (1:ℝ) ≤ Real.sqrt K := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hK
    obtain ⟨Sr, hSrd⟩ : ∃ r : ℝ, r = Real.sqrt (Real.sqrt K) := ⟨_, rfl⟩
    have hS1 : (1:ℝ) ≤ Sr := by
      rw [hSrd, show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hs1
    have hS2 : Sr ^ 2 = Real.sqrt K := by
      rw [hSrd]; exact Real.sq_sqrt (Real.sqrt_nonneg K)
    have hlogS : Real.log Sr = Real.log K / 4 := by
      rw [hSrd, Real.log_sqrt (Real.sqrt_nonneg K), Real.log_sqrt hK0.le]; ring
    have hle : Real.log Sr ≤ Sr - 1 :=
      Real.log_le_sub_one_of_pos (by linarith only [hS1])
    have hlogK : Real.log K ≤ 4 * (Sr - 1) := by
      rw [hlogS] at hle; linarith only [hle]
    have hlog0 : (0:ℝ) ≤ Real.log K := Real.log_nonneg hK
    have h1 : 1 + Real.log K ≤ 4 * Sr - 3 := by linarith only [hlogK]
    have h2 : (0:ℝ) ≤ 1 + Real.log K := by linarith only [hlog0]
    have h3 := mul_self_le_mul_self h2 h1
    rw [← hS2]
    nlinarith only [h3, hS1]
  have hRkey : 8 * C' * (1 + Real.log (R + 10)) ^ 2 ≤ R := by
    have hR1 : (1:ℝ) ≤ R + 10 := by linarith only [hR10]
    have h1 := hlogsq (R + 10) hR1
    have hsq : Real.sqrt (R + 10) ≤ 2 * Real.sqrt R := by
      have h2 : R + 10 ≤ 2 ^ 2 * R := by linarith only [hR10]
      calc Real.sqrt (R + 10) ≤ Real.sqrt (2 ^ 2 * R) := Real.sqrt_le_sqrt h2
        _ = 2 * Real.sqrt R := by
            rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    have hsR : 32 * (8 * C') ≤ Real.sqrt R := by
      have h3 : (32 * (8 * C')) ^ 2 ≤ R := by nlinarith only [hRc, hC'0]
      have h4 := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq (by positivity)] at h4
    calc 8 * C' * (1 + Real.log (R + 10)) ^ 2
        ≤ 8 * C' * (16 * Real.sqrt (R + 10)) := by nlinarith only [h1, hC'0]
      _ ≤ 8 * C' * (16 * (2 * Real.sqrt R)) := by nlinarith only [hsq, hC'0]
      _ = 32 * (8 * C') * Real.sqrt R := by ring
      _ ≤ Real.sqrt R * Real.sqrt R := by
          nlinarith only [hsR, Real.sqrt_nonneg R]
      _ = R := Real.mul_self_sqrt (by linarith only [hR10])
  refine ⟨8, R, le_rfl, by linarith only [hR10], ?_⟩
  intro N hN ε Ω m0 μ 𝒢 ξ z zp zm Q₀ τ hw hbudget
  obtain ⟨hprob, ⟨k₀, hεdef⟩, hε0, hεN, hξpm, hξmeas, hξcond, hzmeas, hzpmeas, hzmmeas,
    hQmeas, hz0, hpair, hrec, hgrad, hτst, hτint, hlive, hexit, hxbnd, hJgap⟩ := hw
  have : IsProbabilityMeasure μ := ⟨hprob⟩
  -- ===== Step 1: the time walk on the lattice `εℤ`. =====
  have hδ0 : (0:ℝ) < (1/2:ℝ) ^ N := by positivity
  have hεle : ε ≤ 1 / 8 := by
    have h1 : ((1:ℝ)/2) ^ N ≤ ((1:ℝ)/2) ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
    rw [pow_one] at h1
    linarith only [hεN, h1]
  obtain ⟨j₀, hj₀d⟩ : ∃ m : ℕ, m = 2 ^ k₀ := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ m : ℕ, m = 8 * 2 ^ k₀ := ⟨_, rfl⟩
  have h2k : ((2:ℝ) ^ k₀) ≠ 0 := by positivity
  have hεj : ε * (j₀ : ℝ) = 1 := by
    rw [hεdef, hj₀d]; push_cast
    rw [one_div, inv_pow, inv_mul_cancel₀ h2k]
  have hεq : ε * (q : ℝ) = 8 := by
    rw [hqd]; push_cast
    rw [hj₀d] at hεj; push_cast at hεj
    linarith only [hεj]
  have hj₀8 : (8:ℝ) ≤ (j₀ : ℝ) := by
    have h1 : ε * (j₀:ℝ) = 1 := hεj
    nlinarith only [h1, hεle, hε0, Nat.cast_nonneg (α := ℝ) j₀]
  have hqj : (q : ℝ) = 8 * (j₀ : ℝ) := by rw [hqd, hj₀d]; push_cast; ring
  -- the sign process as an integer
  obtain ⟨Ξ, hΞd⟩ : ∃ f : ℕ → Ω → ℤ, f = fun n ω => if ξ n ω = 1 then 1 else -1 := ⟨_, rfl⟩
  have hΞreal : ∀ n ω, ((Ξ n ω : ℤ) : ℝ) = ξ n ω := by
    intro n ω
    rw [hΞd]
    by_cases h : ξ n ω = 1
    · simp only [h]; norm_num
    · rcases hξpm n ω with h1 | h1
      · exact absurd h1 h
      · simp only [h1]; norm_num
  obtain ⟨S, hSd⟩ : ∃ f : ℕ → Ω → ℤ, f = fun n ω =>
      (j₀ : ℤ) + ∑ m ∈ Finset.range n, (if m < τ ω then Ξ m ω else 0) := ⟨_, rfl⟩
  have hS0 : ∀ ω, S 0 ω = (j₀ : ℤ) := by intro ω; rw [hSd]; simp
  have hSstep : ∀ n ω, S (n + 1) ω = S n ω + (if n < τ ω then Ξ n ω else 0) := by
    intro n ω; rw [hSd]; simp [Finset.sum_range_succ]; ring
  -- the time coordinate moves by `± ε` while the walk is live
  have htstep : ∀ n ω, (ofLp (z (n + 1) ω)).2
      = (ofLp (z n ω)).2 + (if n < τ ω then ε * ξ n ω else 0) := by
    intro n ω
    by_cases hn : n < τ ω
    · obtain ⟨Yp, Ym, -, -, hzp, hzm⟩ := hpair n ω hn
      rw [hrec n ω, if_pos hn, if_pos hn]
      rcases hξpm n ω with h1 | h1
      · rw [if_pos h1, hzp, h1]; simp
      · rw [if_neg (by rw [h1]; norm_num), hzm, h1]; simp; ring
    · rw [hrec n ω, if_neg hn, if_neg hn, add_zero]
  have hlat : ∀ n ω, (ofLp (z n ω)).2 = ε * (S n ω : ℝ) := by
    intro n ω
    induction n with
    | zero => rw [hz0 ω, hS0 ω]; simp [hεj]
    | succ n ih =>
        rw [htstep n ω, ih, hSstep n ω]
        by_cases hn : n < τ ω
        · rw [if_pos hn, if_pos hn]; push_cast; rw [hΞreal n ω]; ring
        · rw [if_neg hn, if_neg hn]; simp
  -- the live range of the lattice coordinate
  have hSlive : ∀ n ω, n < τ ω → 5 ≤ S n ω ∧ S n ω ≤ (q : ℤ) - 1 := by
    intro n ω hn
    obtain ⟨h1, h2, -⟩ := hlive n ω hn
    rw [hlat n ω] at h1 h2
    have h4 : 4 * ε < ε * (S n ω : ℝ) := by linarith only [h1, hεN]
    have h5 : (4:ℝ) < (S n ω : ℝ) := by
      nlinarith only [h4, hε0]
    have h6 : ε * (S n ω : ℝ) < ε * (q : ℝ) := by
      rw [hεq]; push_cast at h2; linarith only [h2]
    have h7 : (S n ω : ℝ) < (q : ℝ) := by
      exact lt_of_mul_lt_mul_left (by linarith only [h6]) hε0.le
    constructor
    · have : (4:ℤ) < S n ω := by exact_mod_cast h5
      omega
    · have : S n ω < (q : ℤ) := by exact_mod_cast h7
      omega
  have hSrange : ∀ n ω, 4 ≤ S n ω ∧ S n ω ≤ (q : ℤ) := by
    intro n ω
    induction n with
    | zero =>
        rw [hS0 ω]
        constructor
        · have : (4:ℝ) ≤ (j₀:ℝ) := by linarith only [hj₀8]
          exact_mod_cast this
        · have : (j₀:ℝ) ≤ (q:ℝ) := by rw [hqj]; linarith only [hj₀8]
          exact_mod_cast this
    | succ n ih =>
        rw [hSstep n ω]
        by_cases hn : n < τ ω
        · obtain ⟨h1, h2⟩ := hSlive n ω hn
          rw [if_pos hn, hΞd]
          by_cases h : ξ n ω = 1 <;> simp [h] <;> omega
        · rw [if_neg hn, add_zero]; exact ih
  -- ===== measurability infrastructure for the lattice walk =====
  have hq1 : (1:ℤ) ≤ (q:ℤ) := by
    have h1 : (8:ℝ) ≤ (q:ℝ) := by rw [hqj]; linarith only [hj₀8]
    have h2 : (8:ℤ) ≤ (q:ℤ) := by exact_mod_cast h1
    omega
  have hbddg : ∀ g : ℤ → ℝ, ∃ C : ℝ, ∀ j : ℤ, 0 < j → j ≤ (q:ℤ) → |g j| ≤ C := by
    intro g
    have hne : (Finset.Icc (1:ℤ) (q:ℤ)).Nonempty := ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hq1⟩⟩
    refine ⟨(Finset.Icc (1:ℤ) (q:ℤ)).sup' hne (fun j => |g j|), fun j h1 h2 => ?_⟩
    exact Finset.le_sup' (fun j => |g j|) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hliveG : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | n < τ ω} := by
    intro n
    have h0 := hτst n
    have he : {ω | n < τ ω} = {ω | ((fun ω => (τ ω : ℕ∞)) ω) ≤ (n : ℕ∞)}ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Nat.cast_lt]
    rw [he]
    exact MeasurableSet.compl h0
  have hliveG' : ∀ m n : ℕ, m ≤ n → MeasurableSet[𝒢 n] {ω | m < τ ω} :=
    fun m n h => (𝒢.mono h) _ (hliveG m)
  have hξmeasG : ∀ m n : ℕ, m < n → Measurable[𝒢 n] (ξ m) := fun m n hmn =>
    ((hξmeas m).mono (𝒢.mono (by omega))).measurable
  have hSmeasG : ∀ n : ℕ, Measurable[𝒢 n] (S n) := by
    intro n
    rw [hSd]
    refine Measurable.add measurable_const (Finset.measurable_sum _ (fun m hm => ?_))
    have hmn : m < n := Finset.mem_range.mp hm
    refine Measurable.ite (hliveG' m n (le_of_lt hmn)) ?_ measurable_const
    rw [hΞd]
    exact Measurable.ite ((hξmeasG m n hmn) (measurableSet_singleton 1))
      measurable_const measurable_const
  have hgSmeasG : ∀ (g : ℤ → ℝ) (k n : ℕ), k ≤ n → Measurable[𝒢 n] (fun ω => g (S k ω)) :=
    fun g k n h => measurable_from_top.comp ((hSmeasG k).mono (𝒢.mono h) le_rfl)
  have hgSmeas : ∀ (g : ℤ → ℝ) (k : ℕ), Measurable (fun ω => g (S k ω)) :=
    fun g k => (hgSmeasG g k k le_rfl).mono (𝒢.le k) le_rfl
  have hgSint : ∀ (g : ℤ → ℝ) (C : ℝ), (∀ j : ℤ, 0 < j → j ≤ (q:ℤ) → |g j| ≤ C) →
      ∀ k : ℕ, Integrable (fun ω => g (S k ω)) μ := by
    intro g C hC k
    refine Integrable.mono' (integrable_const C) (hgSmeas g k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    obtain ⟨h1, h2⟩ := hSrange k ω
    rw [Real.norm_eq_abs]
    exact hC _ (by omega) h2
  -- ===== stopping-time and lattice-window data for Claim T. =====
  have hstG : ∀ (ζ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) →
      ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | ζ ω ≤ n} := by
    intro ζ hζ n
    have he : {ω | ζ ω ≤ n} = {ω | ((fun ω => (ζ ω : ℕ∞)) ω) ≤ (n : ℕ∞)} := by
      ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
    rw [he]; exact hζ n
  have hstmeas : ∀ ζ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) → Measurable ζ := by
    intro ζ hζ
    have hle : ∀ n : ℕ, MeasurableSet {ω | ζ ω ≤ n} := fun n => (𝒢.le n) _ (hstG ζ hζ n)
    refine measurable_to_countable' (fun n => ?_)
    rcases n with _ | k
    · have he : (ζ ⁻¹' {0}) = {ω | ζ ω ≤ 0} := by
        ext ω; simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, Nat.le_zero]
      rw [he]; exact hle 0
    · have he : (ζ ⁻¹' {k + 1}) = {ω | ζ ω ≤ k + 1} \ {ω | ζ ω ≤ k} := by
        ext ω
        simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
        omega
      rw [he]; exact (hle (k + 1)).diff (hle k)
  have hτmeas : Measurable τ := hstmeas τ hτst
  have hrandidx2 : ∀ (ζ η : Ω → ℕ), Measurable ζ → Measurable η →
      ∀ G : ℕ → ℕ → Ω → ℝ, (∀ n m, Measurable (G n m)) →
      Measurable (fun ω => G (ζ ω) (η ω) ω) := by
    intro ζ η hζ hη G hG s hs
    have he : (fun ω => G (ζ ω) (η ω) ω) ⁻¹' s
        = ⋃ n : ℕ, ⋃ m : ℕ, (({ω | ζ ω = n} ∩ {ω | η ω = m}) ∩ (G n m ⁻¹' s)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      refine ⟨fun h => ⟨ζ ω, η ω, ⟨rfl, rfl⟩, h⟩, ?_⟩
      rintro ⟨n, m, ⟨h1, h2⟩, h3⟩
      rw [h1, h2]; exact h3
    rw [he]
    exact MeasurableSet.iUnion (fun n => MeasurableSet.iUnion (fun m =>
      ((hζ (measurableSet_singleton n)).inter (hη (measurableSet_singleton m))).inter (hG n m hs)))
  have h0st : IsStoppingTime 𝒢 (fun ω => (((fun _ => (0:ℕ)) ω : ℕ) : ℕ∞)) := by
    intro n
    have h1 : MeasurableSet[𝒢 n] (Set.univ : Set Ω) := MeasurableSet.univ
    simp
  -- the walk is frozen after `τ`
  have hSfroz : ∀ (n : ℕ) (ω : Ω), τ ω ≤ n → S n ω = S (τ ω) ω := by
    intro n ω hn
    induction n with
    | zero => rw [Nat.le_zero.mp hn]
    | succ n ih =>
        rcases Nat.lt_or_ge (τ ω) (n + 1) with h | h
        · have h2 : τ ω ≤ n := by omega
          rw [hSstep n ω, if_neg (by omega), add_zero]
          exact ih h2
        · rw [show τ ω = n + 1 by omega]
  -- the lattice window data in the shape the cited node asks for
  have hSrange' : ∀ n ω, ((4:ℕ):ℤ) ≤ S n ω ∧ S n ω ≤ ((q:ℕ):ℤ) := by
    intro n ω
    obtain ⟨h1, h2⟩ := hSrange n ω
    exact ⟨by omega, h2⟩
  have hbddg' : ∀ g : ℤ → ℝ, ∃ C : ℝ,
      ∀ i : ℤ, ((4:ℕ):ℤ) ≤ i → i ≤ ((q:ℕ):ℤ) → |g i| ≤ C := by
    intro g
    obtain ⟨C, hC⟩ := hbddg g
    exact ⟨C, fun i h1 h2 => hC i (by omega) h2⟩
  have hSwin : ∀ (n : ℕ) (ω : Ω), (0:ℕ) ≤ n → n < τ ω →
      ((4:ℕ):ℤ) < S n ω ∧ S n ω < ((q:ℕ):ℤ) := by
    intro n ω _ hn
    obtain ⟨h1, h2⟩ := hSlive n ω hn
    exact ⟨by omega, by omega⟩
  -- ===== Claim T: the supersolution bound along the stopped walk. =====
  -- the stopped-portion supersolution bound of `StoppedLatticeSupersolutionBound`,
  -- specialized to the whole walk: mark time `0`, portion stopping time `τ`,
  -- event `Ω`, window `(4, q)`.
  have claimTgen := StoppedLatticeSupersolutionBound μ 𝒢 ξ Ξ S τ (fun _ => (0:ℕ)) τ 4 q q
    hξpm hξmeas hξcond hΞd hSstep hSrange' h0st measurable_const hτst hτmeas
    (fun ω => Nat.zero_le _) (fun _ => le_rfl) hstG hrandidx2 hbddg' hgSmeasG hgSmeas hSwin
  have claimT : ∀ hf uf : ℤ → ℝ, (∀ j : ℤ, 0 ≤ uf j) →
      (∀ j : ℤ, 0 < j → j ≤ (q:ℤ) → 0 ≤ hf j) →
      (∀ j : ℤ, 0 < j → j < (q:ℤ) → (hf (j + 1) + hf (j - 1)) / 2 - hf j ≤ - uf j) →
      ∀ n : ℕ, ∫ ω, (hf (S n ω) + ∑ m ∈ Finset.range n,
          (if m < τ ω then uf (S m ω) else 0)) ∂μ ≤ hf (j₀ : ℤ) := by
    intro hf uf hu0 _hh0 hpoi n
    have hAG : ∀ k : ℕ, MeasurableSet[𝒢 k] ((Set.univ : Set Ω) ∩ {_ω | (0:ℕ) ≤ k}) := by
      intro k
      have he : (Set.univ : Set Ω) ∩ {_ω | (0:ℕ) ≤ k} = Set.univ := by ext ω; simp
      rw [he]; exact MeasurableSet.univ
    have hgen := claimTgen hf uf Set.univ hu0
      (fun i h1 h2 => hpoi i (by omega) h2) MeasurableSet.univ hAG n
    have hind : ∀ ω : Ω, Set.indicator (Set.univ : Set Ω) (fun _ => (1:ℝ)) ω = 1 :=
      fun ω => Set.indicator_of_mem (Set.mem_univ ω) _
    have hLeq : ∀ ω : Ω, Set.indicator (Set.univ : Set Ω) (fun _ => (1:ℝ)) ω *
        (hf (S (min (max 0 n) (τ ω)) ω) + ∑ m ∈ Finset.Ico 0 (min n (τ ω)), uf (S m ω))
        = hf (S n ω) + ∑ m ∈ Finset.range n, (if m < τ ω then uf (S m ω) else 0) := by
      intro ω
      rw [hind ω, one_mul, max_eq_right (Nat.zero_le n)]
      have hidx : S (min n (τ ω)) ω = S n ω := by
        rcases Nat.le_total n (τ ω) with h | h
        · rw [Nat.min_eq_left h]
        · rw [Nat.min_eq_right h, hSfroz n ω h]
      have hsum : ∑ m ∈ Finset.Ico 0 (min n (τ ω)), uf (S m ω)
          = ∑ m ∈ Finset.range n, (if m < τ ω then uf (S m ω) else 0) := by
        rw [← Finset.sum_filter]
        refine Finset.sum_congr ?_ (fun m _ => rfl)
        ext m
        simp
      rw [hidx, hsum]
    have hReq : ∀ ω : Ω,
        Set.indicator (Set.univ : Set Ω) (fun _ => (1:ℝ)) ω * hf (S 0 ω) = hf (j₀ : ℤ) := by
      intro ω; rw [hind ω, one_mul, hS0 ω]
    refine le_trans (le_of_eq (integral_congr_ae
      (Filter.Eventually.of_forall (fun ω => (hLeq ω).symm)))) (le_trans hgen (le_of_eq ?_))
    calc ∫ ω, Set.indicator (Set.univ : Set Ω) (fun _ => (1:ℝ)) ω * hf (S 0 ω) ∂μ
        = ∫ _ω : Ω, hf (j₀ : ℤ) ∂μ :=
          integral_congr_ae (Filter.Eventually.of_forall hReq)
      _ = hf (j₀ : ℤ) := by rw [integral_const]; simp
  -- ===== Step 2: three consequences of Claim T. =====
  have hsumtail : ∀ (w : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω), τ ω ≤ n →
      ∑ m ∈ Finset.range n, (if m < τ ω then w m ω else 0)
        = ∑ m ∈ Finset.range (τ ω), w m ω := by
    intro w n ω hn
    have h1 : ∑ m ∈ Finset.range (τ ω), (if m < τ ω then w m ω else 0)
        = ∑ m ∈ Finset.range n, (if m < τ ω then w m ω else 0) :=
      Finset.sum_subset (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hn)) (fun m _ hm' => by
        rw [if_neg (fun hc => hm' (Finset.mem_range.mpr hc))])
    rw [← h1]
    exact Finset.sum_congr rfl (fun m hm => if_pos (Finset.mem_range.mp hm))
  -- (a) the time budget
  have htime : ∫ ω, ((τ ω : ℕ) : ℝ) ∂μ ≤ (j₀ : ℝ) * ((q:ℝ) - (j₀:ℝ)) := by
    have hcl := claimT (fun j => (j:ℝ) * ((q:ℝ) - (j:ℝ))) (fun _ => 1)
      (fun j => zero_le_one) ?_ ?_
    · -- pass to the limit in `n`
      have hA : ∀ n : ℕ, ∫ ω, (∑ m ∈ Finset.range n, (if m < τ ω then (1:ℝ) else 0)) ∂μ
          ≤ (j₀ : ℝ) * ((q:ℝ) - (j₀:ℝ)) := by
        intro n
        have h1 := hcl n
        have hnn : (0:ℝ) ≤ ∫ ω, ((S n ω : ℝ) * ((q:ℝ) - (S n ω : ℝ))) ∂μ := by
          refine integral_nonneg (fun ω => ?_)
          obtain ⟨e1, e2⟩ := hSrange n ω
          have e3 : (0:ℝ) ≤ (S n ω : ℝ) := by
            have : (0:ℤ) ≤ S n ω := by omega
            exact_mod_cast this
          have e4 : (S n ω : ℝ) ≤ (q:ℝ) := by exact_mod_cast e2
          exact mul_nonneg e3 (by linarith only [e4])
        have hint1 : Integrable (fun ω => (S n ω : ℝ) * ((q:ℝ) - (S n ω : ℝ))) μ := by
          obtain ⟨C, hC⟩ := hbddg (fun j => (j:ℝ) * ((q:ℝ) - (j:ℝ)))
          exact hgSint (fun j => (j:ℝ) * ((q:ℝ) - (j:ℝ))) C hC n
        have hint2 : Integrable (fun ω => ∑ m ∈ Finset.range n,
            (if m < τ ω then (1:ℝ) else 0)) μ := by
          refine integrable_finsetSum _ (fun m _ => ?_)
          refine Integrable.mono' (integrable_const (1:ℝ))
            (((measurable_const (a := (1:ℝ))).ite ((𝒢.le m) _ (hliveG m))
              measurable_const)).aestronglyMeasurable
            (Filter.Eventually.of_forall (fun ω => ?_))
          by_cases hm : m < τ ω
          · rw [if_pos hm]; simp
          · rw [if_neg hm]; simp
        rw [integral_add hint1 hint2] at h1
        push_cast at h1
        linarith only [h1, hnn]
      refine le_of_tendsto (MeasureTheory.integral_tendsto_of_tendsto_of_monotone
        (fun n => ?_) hτint ?_ ?_) (Filter.Eventually.of_forall hA)
      · refine integrable_finsetSum _ (fun m _ => ?_)
        refine Integrable.mono' (integrable_const (1:ℝ))
          (((measurable_const (a := (1:ℝ))).ite ((𝒢.le m) _ (hliveG m))
            measurable_const)).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        by_cases hm : m < τ ω
        · rw [if_pos hm]; simp
        · rw [if_neg hm]; simp
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        intro a b hab
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_range.mpr
          (lt_of_lt_of_le (Finset.mem_range.mp hx) hab)) (fun m _ _ => ?_)
        by_cases hm : m < τ ω
        · rw [if_pos hm]; norm_num
        · rw [if_neg hm]
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        refine tendsto_atTop_of_eventually_const (i₀ := τ ω) (fun n hn => ?_)
        rw [hsumtail (fun _ _ => (1:ℝ)) n ω hn, Finset.sum_const, Finset.card_range]
        simp
    · intro j h1 h2
      have e1 : (0:ℝ) ≤ (j:ℝ) := by
        have : (0:ℤ) ≤ j := by omega
        exact_mod_cast this
      have e2 : (j:ℝ) ≤ (q:ℝ) := by exact_mod_cast h2
      exact mul_nonneg e1 (by linarith only [e2])
    · intro j h1 h2
      have e : (((j+1 : ℤ)):ℝ) * ((q:ℝ) - ((j+1 : ℤ):ℝ))
          + (((j-1 : ℤ)):ℝ) * ((q:ℝ) - ((j-1 : ℤ):ℝ))
          = 2 * ((j:ℝ) * ((q:ℝ) - (j:ℝ))) - 2 := by push_cast; ring
      rw [e]
      ring_nf
      norm_num
  have htb : ∫ ω, ε ^ 2 * ((τ ω : ℕ) : ℝ) ∂μ ≤ 8 := by
    rw [integral_const_mul]
    have h1 : ε ^ 2 * ((j₀ : ℝ) * ((q:ℝ) - (j₀:ℝ))) ≤ 8 := by
      have e1 : ε * (j₀:ℝ) = 1 := hεj
      have e2 : ε * (q:ℝ) = 8 := hεq
      have e3 : (0:ℝ) ≤ (j₀:ℝ) := Nat.cast_nonneg j₀
      nlinarith only [e1, e2, e3, hε0]
    have h2 := htime
    nlinarith only [h1, h2, hε0, sq_nonneg ε]
  -- (c) the upper time level
  have hupper : ∀ n : ℕ, ∫ ω, ((S n ω : ℝ) / (q:ℝ)) ∂μ ≤ 1 / 8 := by
    have hq0 : (0:ℝ) < (q:ℝ) := by
      have : (8:ℝ) ≤ (q:ℝ) := by rw [hqj]; linarith only [hj₀8]
      linarith only [this]
    intro n
    have hcl := claimT (fun j => (j:ℝ) / (q:ℝ)) (fun _ => 0) (fun j => le_rfl) ?_ ?_ n
    · have he : ∀ ω, ((S n ω : ℝ) / (q:ℝ) + ∑ m ∈ Finset.range n,
          (if m < τ ω then (0:ℝ) else 0)) = (S n ω : ℝ) / (q:ℝ) := by
        intro ω; simp
      rw [integral_congr_ae (Filter.Eventually.of_forall he)] at hcl
      have hj : (((j₀:ℤ)):ℝ) / (q:ℝ) = 1 / 8 := by
        push_cast
        rw [hqj]
        have h5 : (0:ℝ) < (j₀:ℝ) := by linarith only [hj₀8]
        field_simp
      rw [hj] at hcl
      exact hcl
    · intro j h1 h2
      have e1 : (0:ℝ) ≤ (j:ℝ) := by
        have : (0:ℤ) ≤ j := by omega
        exact_mod_cast this
      positivity
    · intro j h1 h2
      have hqne : (q:ℝ) ≠ 0 := ne_of_gt hq0
      have e : ((((j+1 : ℤ)):ℝ) / (q:ℝ) + (((j-1 : ℤ)):ℝ) / (q:ℝ)) / 2 - (j:ℝ) / (q:ℝ) = 0 := by
        push_cast
        field_simp
        ring
      rw [e]
      norm_num
  -- ===== Step 3a: pathwise bounds along the walk. =====
  obtain ⟨ΛQ, ΛE, hΛE0, hxall, htall, hlogt, hQbd, hEbd⟩ :=
    WalkPathwiseBounds C₀ κ hC₀ v hv hcent hJ hWcont hWgrow hsand C₂ hC₂0 hC₂b R hR10
      ε hε0 hεle q hεq ξ z zp zm Q₀ τ S hrec hpair hgrad hxbnd hlat hSrange
  have hG : 4 * ε * (1 / (32 * ε)) = 1 / 8 := by
    field_simp
    ring
  -- ===== general measure-theoretic tools used by Step 4. =====
  have hlimmeas : ∀ (G : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ h, Measurable (G h)) →
      (∀ ω, ∃ H : ℕ, ∀ h, H ≤ h → G h ω = g ω) → Measurable g := by
    intro G g hG hconv
    refine measurable_of_tendsto_metrizable hG (tendsto_pi_nhds.mpr (fun ω => ?_))
    obtain ⟨H, hH⟩ := hconv ω
    exact tendsto_atTop_of_eventually_const (i₀ := H) (fun n hn => hH n hn)
  have hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ, (∀ m, Measurable (G m)) →
      Measurable (fun ω => G (ζ ω) ω) := by
    intro ζ hζ G hG s hs
    have he : (fun ω => G (ζ ω) ω) ⁻¹' s = ⋃ m : ℕ, ({ω | ζ ω = m} ∩ (G m ⁻¹' s)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨ζ ω, rfl, h⟩, fun ⟨m, hm, h⟩ => by rw [hm]; exact h⟩
    rw [he]
    exact MeasurableSet.iUnion (fun m => (hζ (measurableSet_singleton m)).inter (hG m hs))
  have hΩ : Nonempty Ω := by
    by_contra hc
    rw [not_nonempty_iff] at hc
    have he : (Set.univ : Set Ω) = ∅ := Set.univ_eq_empty_iff.mpr hc
    rw [he, measure_empty] at hprob
    exact absurd hprob (by norm_num)
  -- ===== Step 4: the travel inequality, i.e. (i). =====
  have hcore := StoppedPortionTravelBound μ 𝒢 hΩ ε hε0 ξ z zp zm Q₀ τ hξpm hξmeas
    hξcond hzmeas hzpmeas hzmmeas hQmeas hrec hτint htstep ΛQ ΛE hΛE0 hQbd hEbd
    hstmeas hlimmeas hrandidx
  -- ===== Step 3b: the logarithmic time-average bound. =====
  -- the logarithmic weight `u(j) = ε² |log (ε j)|²`, which Step 4 reads directly
  obtain ⟨uf, hufd⟩ : ∃ f : ℤ → ℝ,
      f = fun j : ℤ => ε ^ 2 * |Real.log (ε * (j : ℝ))| ^ 2 := ⟨_, rfl⟩
  have huf0 : ∀ j : ℤ, 0 ≤ uf j := by intro j; rw [hufd]; positivity
  -- the Green function of the stopped time walk against that weight
  obtain ⟨hGf, hGfnn, hGfpoi₀, hGfj⟩ :=
    LatticeLogGreenFunction ε q j₀ Λ₀ hε0 hεj hεq hΛ₀d
  have hGfpoi : ∀ j : ℤ, 0 < j → j < (q:ℤ) →
      (hGf (j + 1) + hGf (j - 1)) / 2 - hGf j ≤ -(uf j) := by
    intro j h1 h2
    have h3 : uf j = ε ^ 2 * |Real.log (ε * (j : ℝ))| ^ 2 := by rw [hufd]
    rw [h3]
    exact hGfpoi₀ j h1 h2
  -- ===== Step 3c: the velocity budget. =====
  have htsum : ∀ (c : ℕ → Ω → ℝ) (Λc : ℝ), (∀ n, Measurable (c n)) → (∀ n ω, 0 ≤ c n ω) →
      0 ≤ Λc → (∀ n ω, n < τ ω → c n ω ≤ Λc) →
      Measurable (fun ω => ∑ n ∈ Finset.range (τ ω), c n ω) ∧
      Integrable (fun ω => ∑ n ∈ Finset.range (τ ω), c n ω) μ ∧
      (∀ ω, ∑ n ∈ Finset.range (τ ω), c n ω ≤ Λc * (τ ω : ℝ)) := by
    intro c Λc hcm hc0 hΛc hcb
    have hpt : ∀ ω, ∑ n ∈ Finset.range (τ ω), c n ω ≤ Λc * (τ ω : ℝ) := by
      intro ω
      have h1 : ∑ n ∈ Finset.range (τ ω), c n ω ≤ ∑ _n ∈ Finset.range (τ ω), Λc :=
        Finset.sum_le_sum (fun n hn => hcb n ω (Finset.mem_range.mp hn))
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
      linarith only [h1]
    have hmeas : Measurable (fun ω => ∑ n ∈ Finset.range (τ ω), c n ω) := by
      refine hlimmeas (fun h ω => ∑ n ∈ Finset.range h, (if n < τ ω then c n ω else 0)) _
        (fun h => ?_) (fun ω => ⟨τ ω, fun h hh => hsumtail c h ω hh⟩)
      exact Finset.measurable_sum _ (fun n _ =>
        (hcm n).ite ((𝒢.le n) _ (hliveG n)) measurable_const)
    refine ⟨hmeas, ?_, hpt⟩
    refine Integrable.mono' (hτint.const_mul Λc) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun n _ => hc0 n ω))]
    exact hpt ω
  have hufS : ∀ (m : ℕ) (ω : Ω),
      uf (S m ω) = ε ^ 2 * |Real.log ((ofLp (z m ω)).2)| ^ 2 := by
    intro m ω
    simp only [hufd]
    rw [← hlat m ω]
  have hufmeas : ∀ m, Measurable (fun ω => uf (S m ω)) := fun m => hgSmeas uf m
  have hufbnd : ∀ (m : ℕ) (ω : Ω),
      uf (S m ω) ≤ ε ^ 2 * (|Real.log (4 * ε)| + Real.log 8) ^ 2 := by
    intro m ω
    rw [hufS m ω]
    have h1 := hlogt m ω
    have h2 : (0:ℝ) ≤ |Real.log ((ofLp (z m ω)).2)| := abs_nonneg _
    have h3 : (0:ℝ) ≤ ε ^ 2 := sq_nonneg ε
    have h4 := mul_self_le_mul_self h2 h1
    nlinarith only [h3, h4]
  obtain ⟨hLm, hLi, hLb⟩ := htsum (fun m ω => uf (S m ω))
    (ε ^ 2 * (|Real.log (4 * ε)| + Real.log 8) ^ 2) hufmeas (fun m ω => huf0 _)
    (by positivity) (fun m ω _ => hufbnd m ω)
  have hlogtime : ∫ ω, (∑ m ∈ Finset.range (τ ω), uf (S m ω)) ∂μ ≤ 2 * Λ₀ := by
    have hpartint : ∀ n : ℕ, Integrable (fun ω => ∑ m ∈ Finset.range n,
        (if m < τ ω then uf (S m ω) else 0)) μ := by
      intro n
      refine integrable_finsetSum _ (fun m _ => ?_)
      refine Integrable.mono' (integrable_const (ε ^ 2 * (|Real.log (4 * ε)| + Real.log 8) ^ 2))
        (((hufmeas m).ite ((𝒢.le m) _ (hliveG m)) measurable_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs]
      by_cases hc : m < τ ω
      · rw [if_pos hc, abs_of_nonneg (huf0 _)]
        exact hufbnd m ω
      · rw [if_neg hc, abs_zero]
        have := hufbnd m ω
        have h5 := huf0 (S m ω)
        linarith only [this, h5]
    have hA : ∀ n : ℕ, ∫ ω, (∑ m ∈ Finset.range n,
        (if m < τ ω then uf (S m ω) else 0)) ∂μ ≤ 2 * Λ₀ := by
      intro n
      have h1 := claimT hGf uf huf0 hGfnn hGfpoi n
      obtain ⟨Cg', hCg'⟩ := hbddg hGf
      have hint1 : Integrable (fun ω => hGf (S n ω)) μ := hgSint hGf Cg' hCg' n
      have hnn : (0:ℝ) ≤ ∫ ω, hGf (S n ω) ∂μ := by
        refine integral_nonneg (fun ω => ?_)
        obtain ⟨e1, e2⟩ := hSrange n ω
        exact hGfnn (S n ω) (by omega) e2
      rw [integral_add hint1 (hpartint n)] at h1
      linarith only [h1, hnn, hGfj]
    refine le_of_tendsto (MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      hpartint hLi ?_ ?_) (Filter.Eventually.of_forall hA)
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      intro a b hab
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hx) hab)) (fun m _ _ => ?_)
      by_cases hc : m < τ ω
      · rw [if_pos hc]; exact huf0 _
      · rw [if_neg hc]
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      refine tendsto_atTop_of_eventually_const (i₀ := τ ω) (fun n hn => ?_)
      exact hsumtail (fun m ω => uf (S m ω)) n ω hn
  -- the velocity budget
  obtain ⟨LB, hLBd⟩ : ∃ t : ℝ, t = 1 + Real.log (R + 10) := ⟨_, rfl⟩
  have hLB1 : (1:ℝ) ≤ LB := by
    rw [hLBd]
    have h1 : (0:ℝ) ≤ Real.log (R + 10) := Real.log_nonneg (by linarith only [hR10])
    linarith only [h1]
  have hQmeasR : ∀ n, Measurable (fun ω => ε ^ 2 * ‖Q₀ n ω‖ ^ 2) := by
    intro n
    exact ((((hQmeas n).mono (𝒢.le n)).norm.measurable).pow_const 2).const_mul _
  have hQsq : ∀ (n : ℕ) (ω : Ω), ε ^ 2 * ‖Q₀ n ω‖ ^ 2
      ≤ 2 * C₂ ^ 2 * (ε ^ 2 * LB ^ 2) + 2 * C₂ ^ 2 * uf (S n ω) := by
    intro n ω
    obtain ⟨h1, h2⟩ := htall n ω
    have hR2 : (2:ℝ) ≤ R + 10 := by linarith only [hR10]
    have hxK : ‖(ofLp (z n ω)).1‖ ≤ R + 10 := by
      have := hxall n ω; linarith only [this, hR10]
    have htK : |(ofLp (z n ω)).2| ≤ R + 10 := by
      rw [abs_of_nonneg (by linarith only [h1, hε0])]
      linarith only [h2, hR10]
    have hεt : ε < (ofLp (z n ω)).2 := by linarith only [h1, hε0]
    have h3 := hC₂b v hv hcent hJ (R + 10) hR2 (ofLp (z n ω)).1 (ofLp (z n ω)).2 ε
      hxK htK hε0 (by linarith only [hεle]) hεt (Q₀ n ω) (hgrad n ω)
    rw [← hLBd] at h3
    have h4 : (0:ℝ) ≤ ‖Q₀ n ω‖ := norm_nonneg _
    have h5 : (0:ℝ) ≤ |Real.log ((ofLp (z n ω)).2)| := abs_nonneg _
    have h6 := mul_self_le_mul_self h4 h3
    have h7 : (0:ℝ) ≤ ε ^ 2 := sq_nonneg ε
    have h9 : (0:ℝ) ≤ C₂ ^ 2 := sq_nonneg C₂
    have hsq1 : ‖Q₀ n ω‖ ^ 2 ≤ C₂ ^ 2 * (LB + |Real.log ((ofLp (z n ω)).2)|) ^ 2 := by
      nlinarith only [h6]
    have hsq2 : (LB + |Real.log ((ofLp (z n ω)).2)|) ^ 2
        ≤ 2 * LB ^ 2 + 2 * |Real.log ((ofLp (z n ω)).2)| ^ 2 := by
      nlinarith only [sq_nonneg (LB - |Real.log ((ofLp (z n ω)).2)|)]
    have hsq3 : ‖Q₀ n ω‖ ^ 2
        ≤ C₂ ^ 2 * (2 * LB ^ 2 + 2 * |Real.log ((ofLp (z n ω)).2)| ^ 2) := by
      nlinarith only [hsq1, hsq2, h9]
    rw [hufS n ω]
    have h10 := mul_le_mul_of_nonneg_left hsq3 h7
    nlinarith only [h10]
  obtain ⟨hVm, hVi, hVb⟩ := htsum (fun n ω => ε ^ 2 * ‖Q₀ n ω‖ ^ 2) (ε ^ 2 * ΛQ ^ 2)
    hQmeasR (fun n ω => by positivity) (by positivity) (fun n ω _ => by
      have h1 := hQbd n ω
      have h2 := mul_self_le_mul_self (norm_nonneg (Q₀ n ω)) h1
      have h3 : (0:ℝ) ≤ ε ^ 2 := sq_nonneg ε
      nlinarith only [h2, h3])
  have hVbd : ∫ ω, (∑ n ∈ Finset.range (τ ω), ε ^ 2 * ‖Q₀ n ω‖ ^ 2) ∂μ ≤ CV * LB ^ 2 := by
    have hrhsint : Integrable (fun ω => 2 * C₂ ^ 2 * LB ^ 2 * (ε ^ 2 * (τ ω : ℝ))
        + 2 * C₂ ^ 2 * (∑ m ∈ Finset.range (τ ω), uf (S m ω))) μ :=
      ((hτint.const_mul (ε ^ 2)).const_mul (2 * C₂ ^ 2 * LB ^ 2)).add
        (hLi.const_mul (2 * C₂ ^ 2))
    have hptle : ∀ ω, ∑ n ∈ Finset.range (τ ω), ε ^ 2 * ‖Q₀ n ω‖ ^ 2
        ≤ 2 * C₂ ^ 2 * LB ^ 2 * (ε ^ 2 * (τ ω : ℝ))
          + 2 * C₂ ^ 2 * (∑ m ∈ Finset.range (τ ω), uf (S m ω)) := by
      intro ω
      have h1 : ∑ n ∈ Finset.range (τ ω), ε ^ 2 * ‖Q₀ n ω‖ ^ 2
          ≤ ∑ n ∈ Finset.range (τ ω),
            (2 * C₂ ^ 2 * (ε ^ 2 * LB ^ 2) + 2 * C₂ ^ 2 * uf (S n ω)) :=
        Finset.sum_le_sum (fun n _ => hQsq n ω)
      have h2 : ∑ n ∈ Finset.range (τ ω),
          (2 * C₂ ^ 2 * (ε ^ 2 * LB ^ 2) + 2 * C₂ ^ 2 * uf (S n ω))
          = 2 * C₂ ^ 2 * LB ^ 2 * (ε ^ 2 * (τ ω : ℝ))
            + 2 * C₂ ^ 2 * (∑ m ∈ Finset.range (τ ω), uf (S m ω)) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ← Finset.mul_sum]
        ring
      rw [h2] at h1
      exact h1
    have h2 := integral_mono hVi hrhsint hptle
    rw [integral_add ((hτint.const_mul (ε ^ 2)).const_mul (2 * C₂ ^ 2 * LB ^ 2))
      (hLi.const_mul (2 * C₂ ^ 2)), integral_const_mul, integral_const_mul,
      integral_const_mul] at h2
    have h3 : (0:ℝ) ≤ 2 * C₂ ^ 2 * LB ^ 2 := by positivity
    have h4 : 2 * C₂ ^ 2 * LB ^ 2 * ((∫ ω, (τ ω : ℝ) ∂μ) * ε ^ 2)
        ≤ 2 * C₂ ^ 2 * LB ^ 2 * 8 := by
      have h5 : (∫ ω, (τ ω : ℝ) ∂μ) * ε ^ 2 ≤ 8 := by
        have h6 := htb
        rw [integral_const_mul] at h6
        linarith only [h6]
      exact mul_le_mul_of_nonneg_left h5 h3
    have h7 : (0:ℝ) ≤ 2 * C₂ ^ 2 := by positivity
    have h8 : 2 * C₂ ^ 2 * (∫ ω, (∑ m ∈ Finset.range (τ ω), uf (S m ω)) ∂μ)
        ≤ 2 * C₂ ^ 2 * (2 * Λ₀) := mul_le_mul_of_nonneg_left hlogtime h7
    have h11 : (0:ℝ) ≤ 4 * C₂ ^ 2 * Λ₀ * (LB ^ 2 - 1) := by
      have h12 : (1:ℝ) ≤ LB ^ 2 := by nlinarith only [hLB1]
      have h13 : (0:ℝ) ≤ 4 * C₂ ^ 2 * Λ₀ := by positivity
      nlinarith only [h12, h13]
    rw [hCVd]
    nlinarith only [h2, h4, h8, h11]
  -- ===== Step 5: the lower hitting probability, i.e. (ii). =====
  -- the travel inequality at the full stopped portion
  have hpmeas0 : ∀ n, StronglyMeasurable[𝒢 n]
      (fun ω => if (fun _ => (0:ℕ)) ω ≤ n then (fun _ => (0:F)) ω else 0) := by
    intro n
    simp only
    exact stronglyMeasurable_const
  obtain ⟨hsupint, -, -, -, hsupbd⟩ := hcore (fun _ => (0:ℕ)) τ h0st hτst
    (fun ω => Nat.zero_le _) (fun ω => le_rfl) (fun _ => (0:F)) 0 1 one_pos
    (fun ω => by show ‖(0:F)‖ ≤ 0; simp) hpmeas0
  have hfeq : ∀ (ω : Ω) (n : ℕ), (1:ℝ)⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z 0 ω)).1
      - ((ofLp (z n ω)).2 - (ofLp (z 0 ω)).2) • (0:F)‖ = ‖(ofLp (z n ω)).1‖ := by
    intro ω n
    rw [hz0 ω]
    simp
  simp only [div_one, sub_zero, Nat.cast_zero, inv_one, one_mul, smul_zero,
    ← Finset.range_eq_Ico] at hsupbd hsupint
  have hb3 : ∫ ω, (∑ x ∈ Finset.range (τ ω),
      (‖ε⁻¹ • ((ofLp (zp x ω)).1 - (ofLp (z x ω)).1) - Q₀ x ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z x ω)).1 - (ofLp (zm x ω)).1) - Q₀ x ω‖ ^ 2)) ∂μ
      ≤ Cstar * LB ^ 4 := by
    have h1 := hbudget
    rw [show R + ((8:ℕ) : ℝ) + 2 = R + 10 by push_cast; ring, ← hLBd] at h1
    exact h1
  have hC'bd : ∫ ω, (Finset.Icc 0 (τ ω)).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le (τ ω)))
      (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖) ∂μ ≤ C' * LB ^ 2 := by
    refine le_trans hsupbd ?_
    have e1 := Real.sqrt_le_sqrt hVbd
    have e2 := Real.sqrt_le_sqrt htb
    have e3 := Real.sqrt_le_sqrt hb3
    have e4 : Real.sqrt (CV * LB ^ 2) = Real.sqrt CV * LB := by
      rw [Real.sqrt_mul hCV0, Real.sqrt_sq (by linarith only [hLB1])]
    have e5 : Real.sqrt (Cstar * LB ^ 4) = Real.sqrt Cstar * LB ^ 2 := by
      rw [Real.sqrt_mul hCstar.le, show LB ^ 4 = (LB ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    rw [e4] at e1
    rw [e5] at e3
    have e6 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
    have e7 : (0:ℝ) ≤ Real.sqrt CV := Real.sqrt_nonneg CV
    have e8 : (0:ℝ) ≤ Real.sqrt Cstar := Real.sqrt_nonneg Cstar
    have e9 : (0:ℝ) ≤ Real.sqrt (∫ ω, (∑ x ∈ Finset.range (τ ω),
        (‖ε⁻¹ • ((ofLp (zp x ω)).1 - (ofLp (z x ω)).1) - Q₀ x ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z x ω)).1 - (ofLp (zm x ω)).1) - Q₀ x ω‖ ^ 2)) ∂μ) :=
      Real.sqrt_nonneg _
    have e10 : Real.sqrt (∫ ω, ε ^ 2 * ((τ ω : ℕ) : ℝ) ∂μ)
        * Real.sqrt (∫ ω, (∑ x ∈ Finset.range (τ ω),
            (‖ε⁻¹ • ((ofLp (zp x ω)).1 - (ofLp (z x ω)).1) - Q₀ x ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z x ω)).1 - (ofLp (zm x ω)).1) - Q₀ x ω‖ ^ 2)) ∂μ)
        ≤ Real.sqrt 8 * (Real.sqrt Cstar * LB ^ 2) := by
      refine mul_le_mul e2 e3 e9 e6
    have e11 : Real.sqrt 8 * (Real.sqrt Cstar * LB ^ 2)
        = Real.sqrt (8 * Cstar) * LB ^ 2 := by
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 8)]
      ring
    rw [e11] at e10
    rw [hC'd]
    have e13 : (0:ℝ) ≤ Real.sqrt CV * (LB ^ 2 - LB) := by
      have e14 : LB ≤ LB ^ 2 := by nlinarith only [hLB1]
      exact mul_nonneg e7 (by linarith only [e14])
    linarith only [e1, e10, e13]
  -- the horizontal displacement enters `StoppedWalkLowerExitProbability`
  -- through its norm only
  have hxnmeas : ∀ n : ℕ, Measurable (fun ω => ‖(ofLp (z n ω)).1‖) := by
    have hcx : Continuous fun u : WithLp 2 (F × ℝ) => (ofLp u).1 :=
      continuous_fst.comp (WithLp.prod_continuous_ofLp 2 F ℝ)
    exact fun n => (((hcx.comp_stronglyMeasurable ((hzmeas n).mono (𝒢.le n)))).norm).measurable
  exact ⟨hcore, StoppedWalkLowerExitProbability μ z S τ ε (C' * LB ^ 2) R q N
    hε0 hεq (by linarith only [hR10]) hlat (fun ω => by rw [hz0 ω])
    (fun n ω => ⟨by have h := (hSrange n ω).1; omega, (hSrange n ω).2⟩) hSfroz
    (fun n => hgSmeas (fun j => (j : ℝ)) n) hxnmeas hτmeas hrandidx hupper
    (fun ω => by
      rcases hexit ω with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by rw [h]; norm_num))
      · exact Or.inr (Or.inr h))
    hsupint hC'bd (by rw [← hLBd] at hRkey; linarith only [hRkey])⟩
