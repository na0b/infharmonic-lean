module

public import InfHarmonic.IsMarkData
public import InfHarmonic.StoppedWalkTravel
public import InfHarmonic.FrameEnvelopeCovariance
public import InfHarmonic.FrameVelocityCovariance
public import InfHarmonic.FitParamBound
public import InfHarmonic.DPLogVelocity
public import InfHarmonic.SqrtSumLogSquareBounds
public import InfHarmonic.StoppedLatticeSupersolutionBound
public import InfHarmonic.ExpectedPortionLengthBound
public import InfHarmonic.MarkCutoffProbabilities
public import InfHarmonic.LogGridSumBound
public import InfHarmonic.MarkFrameTravelBound

@[expose] public section
set_option maxHeartbeats 400000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.7, part 3: for the pair supplied by the extremal envelope
contact there are a box `(T, R)`, a radius `K ≥ 2` and a constant `C_Γ > 0`, all
independent of `N` and of the level `j`, such that every stopped contact walk
with marks and fits obeys the fit-parameter bound `Γ_j = C_Γ (L(B) + j)` and the
localization (6.30): the localization event is measurable and has probability at
least `1/2`, i.e. with probability at least `1/2` the walk reaches the lower time
level and its terminal point lies within `K δ_j` of the `j`-th mark in that
mark's fitted frame. -/
theorem MarkLocalization (C₀ κ H : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ)
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
    ∃ (T : ℕ) (R K CΓ : ℝ), 8 ≤ T ∧ 2 ≤ R ∧ 2 ≤ K ∧ 0 < CΓ ∧
      ∀ (N : ℕ), 1 ≤ N → ∀ (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω)
        (μ : Measure Ω) (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
        (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ),
        IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ →
        ∫ ω, (∑ n ∈ Finset.range (τ ω),
          (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
            + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ
          ≤ Cstar * (1 + Real.log (R + (T : ℝ) + 2)) ^ 4 →
        ∀ (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (aj : ℕ → Ω → ℝ),
          IsMarkData C₀ v N 𝒢 z τ smark pj aj →
          ∀ j : ℕ, 1 ≤ j → j ≤ N →
            (∀ ω, ‖pj j ω‖ + |aj j ω|
              ≤ CΓ * ((1 + Real.log (R + (T : ℝ) + 2)) + (j : ℝ))) ∧
            (1 : ℝ) ≤ CΓ * ((1 + Real.log (R + (T : ℝ) + 2)) + (j : ℝ)) ∧
            MeasurableSet {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
              ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
                - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖
                ≤ K * (1 / 2 : ℝ) ^ j} ∧
            (1 : ℝ) / 2 ≤ (μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
              ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
                - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖
                ≤ K * (1 / 2 : ℝ) ^ j}).toReal := by
  classical
  -- ===== Step 0: the constants, and the choice of `T`, `R`, `K` and `C_Γ`. =====
  obtain ⟨Cf, hCf0, hCfb⟩ := FitParamBound (F := F) C₀ hC₀
  obtain ⟨C₂, hC₂0, hC₂b⟩ := DPLogVelocity (F := F) C₀ hC₀ κ hκ.le
  obtain ⟨T, R, hT8, hR2, hswt⟩ := StoppedWalkTravel C₀ κ H hC₀ hκ v hv hcent hJ hWcont
    hWgrow hWsub hsand hW0 hv0 hconc hgap hham hslope Cstar hCstar
  obtain ⟨CΓ, hCΓd⟩ : ∃ t : ℝ, t = max Cf 1 := ⟨_, rfl⟩
  have hCΓ1 : (1:ℝ) ≤ CΓ := by rw [hCΓd]; exact le_max_right _ _
  have hCΓf : Cf ≤ CΓ := by rw [hCΓd]; exact le_max_left _ _
  have hCΓ0 : (0:ℝ) < CΓ := by linarith only [hCΓ1]
  have hT8R : (8:ℝ) ≤ (T:ℝ) := by exact_mod_cast hT8
  have hB12 : (12:ℝ) ≤ R + (T:ℝ) + 2 := by linarith only [hR2, hT8R]
  obtain ⟨LB, hLBd⟩ : ∃ t : ℝ, t = 1 + Real.log (R + (T:ℝ) + 2) := ⟨_, rfl⟩
  have hLB1 : (1:ℝ) < LB := by
    rw [hLBd]
    have h1 : (0:ℝ) < Real.log (R + (T:ℝ) + 2) := Real.log_pos (by linarith only [hB12])
    linarith only [h1]
  obtain ⟨B₀, hB₀d⟩ : ∃ t : ℝ, t = Cstar * LB ^ 4 := ⟨_, rfl⟩
  have hB₀0 : (0:ℝ) ≤ B₀ := by
    rw [hB₀d]
    have h1 : (0:ℝ) < LB := by linarith only [hLB1]
    positivity
  obtain ⟨Λ, hΛd⟩ : ∃ t : ℝ, t = 32 * Real.sqrt 8 + 8 * Real.log 8 ^ 2 := ⟨_, rfl⟩
  have hΛ0 : (0:ℝ) ≤ Λ := by rw [hΛd]; positivity
  obtain ⟨CM, hCMd⟩ : ∃ t : ℝ, t = 2 * C₂ ^ 2 * (16 + 4 * Λ) := ⟨_, rfl⟩
  have hCM0 : (0:ℝ) ≤ CM := by rw [hCMd]; positivity
  obtain ⟨C', hC'd⟩ : ∃ t : ℝ, t = max (2 * Real.sqrt CM) 4 := ⟨_, rfl⟩
  have hC'4 : (4:ℝ) ≤ C' := by rw [hC'd]; exact le_max_right _ _
  have hC'CM : 2 * Real.sqrt CM ≤ C' := by rw [hC'd]; exact le_max_left _ _
  have hC'0 : (0:ℝ) ≤ C' := by linarith only [hC'4]
  obtain ⟨K, hKd⟩ : ∃ t : ℝ,
      t = max 2 (max (6400 * C' ^ 2) (16 * C' * Real.sqrt B₀)) := ⟨_, rfl⟩
  have hK2 : (2:ℝ) ≤ K := by rw [hKd]; exact le_max_left _ _
  have hlogsq : ∀ x : ℝ, 2 ≤ x → 1 + Real.log (x + 10) ≤ 5 * Real.sqrt x := by
    intro x hx
    have hx0 : (0:ℝ) < x := by linarith only [hx]
    have hs1 : (1:ℝ) ≤ Real.sqrt (x + 10) := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith only [hx0])
    have hlog : Real.log (x + 10) = 2 * Real.log (Real.sqrt (x + 10)) := by
      rw [Real.log_sqrt (by linarith only [hx0])]; ring
    have hle : Real.log (Real.sqrt (x + 10)) ≤ Real.sqrt (x + 10) - 1 :=
      Real.log_le_sub_one_of_pos (by linarith only [hs1])
    have h6 : Real.sqrt (x + 10) ≤ Real.sqrt 6 * Real.sqrt x := by
      rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 6)]
      exact Real.sqrt_le_sqrt (by linarith only [hx])
    have h6v : Real.sqrt 6 ≤ 5 / 2 := by
      rw [show (5:ℝ)/2 = Real.sqrt ((5/2)^2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hsx : (0:ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
    rw [hlog]
    nlinarith only [hle, h6, h6v, hsx]
  have hKkey : 8 * C' * ((1 + Real.log (K + 10)) + Real.sqrt B₀) ≤ K := by
    have h1 := hlogsq K hK2
    have h2 : 6400 * C' ^ 2 ≤ K := by
      rw [hKd]; exact le_trans (le_max_left _ _) (le_max_right _ _)
    have h3 : 16 * C' * Real.sqrt B₀ ≤ K := by
      rw [hKd]; exact le_trans (le_max_right _ _) (le_max_right _ _)
    have hsK0 : (0:ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    have hKK : Real.sqrt K * Real.sqrt K = K := Real.mul_self_sqrt (by linarith only [hK2])
    have hsK : 80 * C' ≤ Real.sqrt K := by
      have h4 : (80 * C') ^ 2 ≤ K := by nlinarith only [h2]
      have h5 := Real.sqrt_le_sqrt h4
      rwa [Real.sqrt_sq (by positivity)] at h5
    have e1 : 8 * C' * (1 + Real.log (K + 10)) ≤ 8 * C' * (5 * Real.sqrt K) :=
      mul_le_mul_of_nonneg_left h1 (by linarith only [hC'0])
    have e2 : 40 * C' * Real.sqrt K ≤ (Real.sqrt K / 2) * Real.sqrt K :=
      mul_le_mul_of_nonneg_right (by linarith only [hsK]) hsK0
    nlinarith only [e1, e2, hKK, h3]
  refine ⟨T, R, K, CΓ, hT8, hR2, hK2, hCΓ0, ?_⟩
  intro N hN ε Ω m0 μ 𝒢 ξ z zp zm Q₀ τ hw hbudget smark pj aj hmark j hj1 hjN
  rw [← hLBd]
  have hwc := hw
  obtain ⟨hprob, ⟨kk, hεdef⟩, hε0, hεN, hξpm, hξmeas, hξcond, hzmeas, hzpmeas, hzmmeas,
    hQmeas, hz0, hpair, hrec, hgrad, hτst, hτint, hlive, hexit, hxbnd, hJgap⟩ := hw
  have hprobμ : IsProbabilityMeasure μ := ⟨hprob⟩
  obtain ⟨hσst, hστ, hσlt, hσalt, hpmeasG, hameasG, hfitσ, hzeroσ⟩ := hmark j hj1 hjN
  obtain ⟨r, hrd⟩ : ∃ t : ℝ, t = (1 / 2 : ℝ) ^ j := ⟨_, rfl⟩
  have hr0 : (0:ℝ) < r := by rw [hrd]; positivity
  have hrhalf : r ≤ 1 / 2 := by
    rw [hrd]
    calc ((1:ℝ)/2) ^ j ≤ ((1:ℝ)/2) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hj1
      _ = 1 / 2 := pow_one _
  have hjR : (1:ℝ) ≤ (j:ℝ) := by exact_mod_cast hj1
  -- ===== Step 2: the fit-parameter bound, i.e. the first two conjuncts. =====
  have hlogr : |Real.log r| = (j:ℝ) * Real.log 2 := by
    have h1 : Real.log r = -((j:ℝ) * Real.log 2) := by
      rw [hrd, Real.log_pow, one_div, Real.log_inv]
      ring
    rw [h1, abs_neg, abs_of_nonneg (by positivity)]
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith only [this]
  have hc2 : (1:ℝ) ≤ CΓ * (LB + (j:ℝ)) := by
    have h1 : (2:ℝ) ≤ LB + (j:ℝ) := by linarith only [hLB1, hjR]
    nlinarith only [h1, hCΓ1]
  have hc1 : ∀ ω, ‖pj j ω‖ + |aj j ω| ≤ CΓ * (LB + (j:ℝ)) := by
    intro ω
    by_cases hc : (ofLp (z (smark j ω) ω)).2 = (1 / 2 : ℝ) ^ j
    · have hfitω := hfitσ ω hc
      have h2B : (2:ℝ) ≤ R + (T:ℝ) + 2 := by linarith only [hB12]
      have hxb : ‖(ofLp (z (smark j ω) ω)).1‖ ≤ R + (T:ℝ) + 2 := by
        have h3 := hxbnd (smark j ω) ω (hστ ω)
        linarith only [h3, hT8R]
      have htb : |(ofLp (z (smark j ω) ω)).2| ≤ R + (T:ℝ) + 2 := by
        rw [hc, abs_of_nonneg (by positivity)]
        have h4 : ((1:ℝ)/2) ^ j ≤ 1 := by
          rw [← hrd]; linarith only [hrhalf]
        linarith only [h4, hB12]
      have h5 := hCfb v hv (Or.inr hcent) (R + (T:ℝ) + 2) h2B (z (smark j ω) ω) hxb htb
        ((1 / 2 : ℝ) ^ j) (by positivity) (pj j ω) (aj j ω) hfitω
      rw [← hrd, hlogr, ← hLBd] at h5
      have h6 : Cf * (LB + (j:ℝ) * Real.log 2) ≤ CΓ * (LB + (j:ℝ)) := by
        have h7 : (j:ℝ) * Real.log 2 ≤ (j:ℝ) := by
          nlinarith only [hlog2, hjR]
        have h8 : (0:ℝ) ≤ LB + (j:ℝ) * Real.log 2 := by
          have h9 : (0:ℝ) ≤ (j:ℝ) * Real.log 2 := by positivity
          linarith only [h9, hLB1]
        nlinarith only [h7, h8, hCΓf, hCf0]
      linarith only [h5, h6]
    · obtain ⟨hp0, ha0⟩ := hzeroσ ω hc
      rw [hp0, ha0]
      have h1 : (0:ℝ) ≤ CΓ * (LB + (j:ℝ)) := by linarith only [hc2]
      simp only [norm_zero, abs_zero, add_zero]
      linarith only [h1]
  refine ⟨hc1, hc2, ?_⟩
  -- ===== Step 1: the time walk on the lattice `εℤ`. =====
  have hεle : ε ≤ (1 / 2 : ℝ) ^ N / 4 := hεN
  have hkkN : N + 2 ≤ kk := by
    by_contra hcon
    have h1 : kk ≤ N + 1 := by omega
    have h2 : ((1:ℝ)/2) ^ (N + 1) ≤ ((1:ℝ)/2) ^ kk :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) h1
    rw [← hεdef] at h2
    have h3 : ((1:ℝ)/2) ^ (N + 1) = ((1:ℝ)/2) ^ N / 2 := by
      rw [pow_succ]; ring
    rw [h3] at h2
    have h4 : (0:ℝ) < ((1:ℝ)/2) ^ N := by positivity
    linarith only [h2, hεle, h4]
  have hpow2 : ∀ i : ℕ, i ≤ kk → ((2:ℝ)) ^ (kk - i) * (2:ℝ) ^ i = (2:ℝ) ^ kk := by
    intro i hi
    rw [← pow_add, Nat.sub_add_cancel hi]
  obtain ⟨aa, haad⟩ : ∃ m : ℕ, m = 2 ^ (kk - N) := ⟨_, rfl⟩
  obtain ⟨cc, hccd⟩ : ∃ m : ℕ, m = 2 ^ (kk - j) := ⟨_, rfl⟩
  obtain ⟨j₀, hj₀d⟩ : ∃ m : ℕ, m = 2 ^ kk := ⟨_, rfl⟩
  obtain ⟨qq, hqqd⟩ : ∃ m : ℕ, m = T * 2 ^ kk := ⟨_, rfl⟩
  obtain ⟨bb, hbbd⟩ : ∃ m : ℕ, m = 8 * 2 ^ (kk - j) := ⟨_, rfl⟩
  have hεj₀ : ε * (j₀ : ℝ) = 1 := by
    rw [hj₀d, hεdef]
    push_cast
    rw [div_pow, one_pow, div_mul_cancel₀ _ (by positivity : ((2:ℝ) ^ kk) ≠ 0)]
  have hε2kk : ε * (2:ℝ) ^ kk = 1 := by
    have h3 := hεj₀
    rw [hj₀d] at h3
    push_cast at h3
    exact h3
  have hεpow : ∀ i : ℕ, i ≤ kk → ε * ((2 ^ (kk - i) : ℕ) : ℝ) = (1 / 2 : ℝ) ^ i := by
    intro i hi
    have h1 : (((2 ^ (kk - i) : ℕ)) : ℝ) * (2:ℝ) ^ i = (2:ℝ) ^ kk := by
      push_cast
      exact hpow2 i hi
    have h2 : (0:ℝ) < (2:ℝ) ^ i := by positivity
    have h3 : ε * ((2 ^ (kk - i) : ℕ) : ℝ) * (2:ℝ) ^ i = 1 := by
      rw [mul_assoc, h1, hε2kk]
    rw [div_pow, one_pow, eq_div_iff (ne_of_gt h2)]
    exact h3
  have hεaa : ε * (aa : ℝ) = (1 / 2 : ℝ) ^ N := by rw [haad]; exact hεpow N (by omega)
  have hεcc : ε * (cc : ℝ) = r := by rw [hccd, hrd]; exact hεpow j (by omega)
  have hεqq : ε * (qq : ℝ) = (T : ℝ) := by
    rw [hqqd]
    push_cast
    have h1 : ε * ((T:ℝ) * (2:ℝ) ^ kk) = (T:ℝ) * (ε * (2:ℝ) ^ kk) := by ring
    rw [h1, hε2kk, mul_one]
  have hεbb : ε * (bb : ℝ) = 8 * r := by
    rw [hbbd]
    push_cast
    have h1 : ε * (8 * (2:ℝ) ^ (kk - j)) = 8 * (ε * ((2 ^ (kk - j) : ℕ) : ℝ)) := by
      push_cast; ring
    rw [h1, hεpow j (by omega), ← hrd]
  have haa4 : 4 ≤ aa := by
    rw [haad]
    have h1 : 2 ^ 2 ≤ 2 ^ (kk - N) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have haacc : aa ≤ cc := by
    rw [haad, hccd]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hccbb : cc < bb := by rw [hbbd, ← hccd]; omega
  have hccpos : 0 < cc := by rw [hccd]; positivity
  -- the sign process and the lattice coordinate
  obtain ⟨Ξ, hΞd⟩ : ∃ f : ℕ → Ω → ℤ, f = fun n ω => if ξ n ω = 1 then 1 else -1 := ⟨_, rfl⟩
  have hΞreal : ∀ n ω, ((Ξ n ω : ℤ) : ℝ) = ξ n ω := by
    intro n ω
    simp only [hΞd]
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
    | zero => rw [hz0 ω, hS0 ω]; simp [hεj₀]
    | succ n ih =>
        rw [htstep n ω, ih, hSstep n ω]
        by_cases hn : n < τ ω
        · rw [if_pos hn, if_pos hn]; push_cast; rw [hΞreal n ω]; ring
        · rw [if_neg hn, if_neg hn]; simp
  have hSlive : ∀ n ω, n < τ ω → (aa : ℤ) < S n ω ∧ S n ω < (qq : ℤ) := by
    intro n ω hn
    obtain ⟨h1, h2, -⟩ := hlive n ω hn
    rw [hlat n ω] at h1 h2
    constructor
    · have h3 : ε * (aa : ℝ) < ε * (S n ω : ℝ) := by rw [hεaa]; exact h1
      have h4 : (aa : ℝ) < (S n ω : ℝ) := lt_of_mul_lt_mul_left h3 hε0.le
      exact_mod_cast h4
    · have h3 : ε * (S n ω : ℝ) < ε * (qq : ℝ) := by rw [hεqq]; exact h2
      have h4 : (S n ω : ℝ) < (qq : ℝ) := lt_of_mul_lt_mul_left h3 hε0.le
      exact_mod_cast h4
  have hSrange : ∀ n ω, (aa : ℤ) ≤ S n ω ∧ S n ω ≤ (qq : ℤ) := by
    intro n ω
    induction n with
    | zero =>
        rw [hS0 ω]
        have h1 : aa ≤ j₀ := by
          rw [haad, hj₀d]
          exact Nat.pow_le_pow_right (by norm_num) (by omega)
        have h2 : j₀ ≤ qq := by
          rw [hqqd, hj₀d]
          have : 1 * 2 ^ kk ≤ T * 2 ^ kk := Nat.mul_le_mul_right _ (by omega)
          omega
        constructor
        · exact_mod_cast h1
        · exact_mod_cast h2
    | succ n ih =>
        rw [hSstep n ω]
        by_cases hn : n < τ ω
        · obtain ⟨h1, h2⟩ := hSlive n ω hn
          rw [if_pos hn, hΞd]
          by_cases h : ξ n ω = 1 <;> simp [h] <;> omega
        · rw [if_neg hn, add_zero]; exact ih
  -- ===== measurability infrastructure =====
  have hstmeas : ∀ ζ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) → Measurable ζ := by
    intro ζ hζ
    have hle : ∀ n : ℕ, MeasurableSet {ω | ζ ω ≤ n} := by
      intro n
      have h0 := hζ n
      have he : {ω | ζ ω ≤ n} = {ω | ((fun ω => (ζ ω : ℕ∞)) ω) ≤ (n : ℕ∞)} := by
        ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
      rw [he]
      exact (𝒢.le n) _ h0
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
  have hσmeas : Measurable (smark j) := hstmeas (smark j) hσst
  have hstG : ∀ (ζ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) →
      ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | ζ ω ≤ n} := by
    intro ζ hζ n
    have h0 := hζ n
    have he : {ω | ζ ω ≤ n} = {ω | ((fun ω => (ζ ω : ℕ∞)) ω) ≤ (n : ℕ∞)} := by
      ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
    rw [he]; exact h0
  have hliveG : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | n < τ ω} := by
    intro n
    have he : {ω | n < τ ω} = {ω | τ ω ≤ n}ᶜ := by
      ext ω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
    rw [he]
    exact MeasurableSet.compl (hstG τ hτst n)
  have hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ, (∀ m, Measurable (G m)) →
      Measurable (fun ω => G (ζ ω) ω) := by
    intro ζ hζ G hG s hs
    have he : (fun ω => G (ζ ω) ω) ⁻¹' s = ⋃ m : ℕ, ({ω | ζ ω = m} ∩ (G m ⁻¹' s)) := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨ζ ω, rfl, h⟩, fun ⟨m, hm, h⟩ => by rw [hm]; exact h⟩
    rw [he]
    exact MeasurableSet.iUnion (fun m => (hζ (measurableSet_singleton m)).inter (hG m hs))
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
  have hc1' : Continuous fun u : WithLp 2 (F × ℝ) => (ofLp u).1 :=
    continuous_fst.comp (WithLp.prod_continuous_ofLp 2 F ℝ)
  have hc2' : Continuous fun u : WithLp 2 (F × ℝ) => (ofLp u).2 :=
    continuous_snd.comp (WithLp.prod_continuous_ofLp 2 F ℝ)
  have hzx : ∀ n, StronglyMeasurable (fun ω => (ofLp (z n ω)).1) := fun n =>
    hc1'.comp_stronglyMeasurable ((hzmeas n).mono (𝒢.le n))
  have hzt : ∀ n, StronglyMeasurable (fun ω => (ofLp (z n ω)).2) := fun n =>
    hc2'.comp_stronglyMeasurable ((hzmeas n).mono (𝒢.le n))
  have hpjm : ∀ n, StronglyMeasurable (fun ω => if smark j ω ≤ n then pj j ω else 0) :=
    fun n => (hpmeasG n).mono (𝒢.le n)
  -- ===== the localization event is measurable: the third conjunct. =====
  have hGmeas : ∀ n m : ℕ, Measurable (fun ω => ‖(ofLp (z n ω)).1 - (ofLp (z m ω)).1
      - ((ofLp (z n ω)).2 - r) • (if smark j ω ≤ m then pj j ω else 0)‖) := by
    intro n m
    exact (((hzx n).sub (hzx m)).sub (((hzt n).sub stronglyMeasurable_const).smul
      (hpjm m))).norm.measurable
  have hGval : ∀ ω, ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
      - ((ofLp (z (τ ω) ω)).2 - r) • (if smark j ω ≤ smark j ω then pj j ω else 0)‖
      = ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖ := by
    intro ω
    rw [if_pos (le_refl (smark j ω)), hrd]
  have hXτmeas : Measurable (fun ω => (ofLp (z (τ ω) ω)).2) :=
    hrandidx τ hτmeas (fun n ω => (ofLp (z n ω)).2) (fun n => (hzt n).measurable)
  have hNmeas : Measurable (fun ω => ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
      - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖) := by
    have he : (fun ω => ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖)
        = fun ω => (fun n m ω => ‖(ofLp (z n ω)).1 - (ofLp (z m ω)).1
          - ((ofLp (z n ω)).2 - r) • (if smark j ω ≤ m then pj j ω else 0)‖)
            (τ ω) (smark j ω) ω := by
      funext ω
      exact (hGval ω).symm
    rw [he]
    exact hrandidx2 τ (smark j) hτmeas hσmeas _ hGmeas
  have hLmeas : MeasurableSet {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
      ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖ ≤ K * (1 / 2 : ℝ) ^ j} := by
    have he : {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
        ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
          - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖ ≤ K * (1 / 2 : ℝ) ^ j}
        = ((fun ω => (ofLp (z (τ ω) ω)).2) ⁻¹' {(1 / 2 : ℝ) ^ N})
          ∩ ((fun ω => ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
            - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖)
              ⁻¹' (Set.Iic (K * (1 / 2 : ℝ) ^ j))) := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_Iic]
    rw [he]
    exact (hXτmeas (measurableSet_singleton _)).inter (hNmeas measurableSet_Iic)
  refine ⟨hLmeas, ?_⟩
  -- ===== Step 4: the portion and its stopping index. =====
  have heqG : ∀ (ζ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) →
      ∀ i : ℕ, MeasurableSet[𝒢 i] {ω | ζ ω = i} := by
    intro ζ hζ i
    rcases i with _ | k
    · have he : {ω | ζ ω = 0} = {ω | ζ ω ≤ 0} := by
        ext ω; simp only [Set.mem_ofPred_eq, Nat.le_zero]
      rw [he]; exact hstG ζ hζ 0
    · have he : {ω | ζ ω = k + 1} = {ω | ζ ω ≤ k + 1} \ {ω | ζ ω ≤ k} := by
        ext ω; simp only [Set.mem_ofPred_eq, Set.mem_sdiff]; omega
      rw [he]
      exact (hstG ζ hζ (k + 1)).diff
        ((𝒢.mono (by omega : k ≤ k + 1)) _ (hstG ζ hζ k))
  have hσeqG : ∀ i : ℕ, MeasurableSet[𝒢 i] {ω | smark j ω = i} := heqG (smark j) hσst
  obtain ⟨Xst, hXstd⟩ : ∃ f : ℕ → Ω → F, f = fun m ω =>
      ∑ i ∈ Finset.range (m + 1), (if smark j ω = i then (ofLp (z i ω)).1 else 0) := ⟨_, rfl⟩
  obtain ⟨Tst, hTstd⟩ : ∃ f : ℕ → Ω → ℝ, f = fun m ω =>
      ∑ i ∈ Finset.range (m + 1), (if smark j ω = i then (ofLp (z i ω)).2 else 0) := ⟨_, rfl⟩
  have hXstG : ∀ m, StronglyMeasurable[𝒢 m] (Xst m) := by
    intro m
    simp only [hXstd]
    refine Finset.stronglyMeasurable_fun_sum _ (fun i hi => ?_)
    have him : i ≤ m := by have h := Finset.mem_range.mp hi; omega
    exact StronglyMeasurable.ite ((𝒢.mono him) _ (hσeqG i))
      (hc1'.comp_stronglyMeasurable ((hzmeas i).mono (𝒢.mono him))) stronglyMeasurable_const
  have hTstG : ∀ m, StronglyMeasurable[𝒢 m] (Tst m) := by
    intro m
    simp only [hTstd]
    refine Finset.stronglyMeasurable_fun_sum _ (fun i hi => ?_)
    have him : i ≤ m := by have h := Finset.mem_range.mp hi; omega
    exact StronglyMeasurable.ite ((𝒢.mono him) _ (hσeqG i))
      (hc2'.comp_stronglyMeasurable ((hzmeas i).mono (𝒢.mono him))) stronglyMeasurable_const
  have hXstval : ∀ (m : ℕ) (ω : Ω), smark j ω ≤ m → Xst m ω = (ofLp (z (smark j ω) ω)).1 := by
    intro m ω hm
    simp only [hXstd]
    rw [Finset.sum_eq_single (smark j ω) (fun i _ hine => if_neg (by omega))
      (fun hnot => absurd (Finset.mem_range.mpr (by omega)) hnot), if_pos rfl]
  have hTstval : ∀ (m : ℕ) (ω : Ω), smark j ω ≤ m → Tst m ω = (ofLp (z (smark j ω) ω)).2 := by
    intro m ω hm
    simp only [hTstd]
    rw [Finset.sum_eq_single (smark j ω) (fun i _ hine => if_neg (by omega))
      (fun hnot => absurd (Finset.mem_range.mpr (by omega)) hnot), if_pos rfl]
  obtain ⟨Yst, hYstd⟩ : ∃ f : ℕ → Ω → ℝ, f = fun m ω =>
      r⁻¹ * ‖(ofLp (z m ω)).1 - Xst m ω
        - ((ofLp (z m ω)).2 - r) • (if smark j ω ≤ m then pj j ω else 0)‖ := ⟨_, rfl⟩
  have hYstG : ∀ m, Measurable[𝒢 m] (Yst m) := by
    intro m
    simp only [hYstd]
    refine Measurable.const_mul ?_ _
    refine StronglyMeasurable.measurable ?_
    exact ((((hzmeas m).mono (le_refl (𝒢 m))) |> fun h =>
      hc1'.comp_stronglyMeasurable h).sub (hXstG m)).sub
        (((hc2'.comp_stronglyMeasurable ((hzmeas m).mono (le_refl (𝒢 m)))).sub
          stronglyMeasurable_const).smul (hpmeasG m)) |>.norm
  have hYstval : ∀ (m : ℕ) (ω : Ω), smark j ω ≤ m →
      Yst m ω = r⁻¹ * ‖(ofLp (z m ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z m ω)).2 - r) • pj j ω‖ := by
    intro m ω hm
    simp only [hYstd, hXstval m ω hm, if_pos hm]
  -- the portion's stopping rule
  obtain ⟨Qp, hQpd⟩ : ∃ f : ℕ → Ω → Prop, f = fun m ω =>
      (m = τ ω ∨ 8 * r ≤ (ofLp (z m ω)).2 ∨ K ≤ Yst m ω) := ⟨_, rfl⟩
  have hQpG : ∀ m : ℕ, MeasurableSet[𝒢 m] {ω | Qp m ω} := by
    intro m
    have hmeas : MeasurableSet[𝒢 m] ({ω | τ ω = m}
        ∪ (((fun ω => (ofLp (z m ω)).2) ⁻¹' (Set.Ici (8 * r)))
          ∪ ((Yst m) ⁻¹' (Set.Ici K)))) := by
      refine (heqG τ hτst m).union (MeasurableSet.union ?_ ?_)
      · exact (hc2'.comp_stronglyMeasurable ((hzmeas m).mono (le_refl (𝒢 m)))).measurable
          measurableSet_Ici
      · exact (hYstG m) measurableSet_Ici
    refine MeasurableSet.congr hmeas ?_
    ext ω
    simp only [hQpd, Set.mem_ofPred_eq, Set.mem_union, Set.mem_preimage, Set.mem_Ici]
    constructor
    · rintro (h | h | h)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
  have hex : ∀ ω, ∃ n, smark j ω ≤ n ∧ Qp n ω := by
    intro ω
    exact ⟨τ ω, hστ ω, by rw [hQpd]; exact Or.inl rfl⟩
  obtain ⟨tau', htau'd⟩ : ∃ f : Ω → ℕ, f = fun ω =>
      if (ofLp (z (smark j ω) ω)).2 = r then Nat.find (hex ω) else smark j ω := ⟨_, rfl⟩
  have hσtau' : ∀ ω, smark j ω ≤ tau' ω := by
    intro ω
    simp only [htau'd]
    by_cases hc : (ofLp (z (smark j ω) ω)).2 = r
    · rw [if_pos hc]; exact (Nat.find_spec (hex ω)).1
    · rw [if_neg hc]
  have htau'τ : ∀ ω, tau' ω ≤ τ ω := by
    intro ω
    simp only [htau'd]
    by_cases hc : (ofLp (z (smark j ω) ω)).2 = r
    · rw [if_pos hc]
      exact Nat.find_le ⟨hστ ω, by rw [hQpd]; exact Or.inl rfl⟩
    · rw [if_neg hc]; exact hστ ω
  have htau'spec : ∀ ω, (ofLp (z (smark j ω) ω)).2 = r → Qp (tau' ω) ω := by
    intro ω hc
    simp only [htau'd, if_pos hc]
    exact (Nat.find_spec (hex ω)).2
  have htau'min : ∀ (ω : Ω) (n : ℕ), smark j ω ≤ n → n < tau' ω → ¬ Qp n ω := by
    intro ω n hn1 hn2
    by_cases hc : (ofLp (z (smark j ω) ω)).2 = r
    · simp only [htau'd, if_pos hc] at hn2
      have h := Nat.find_min (hex ω) hn2
      tauto
    · simp only [htau'd, if_neg hc] at hn2
      omega
  have htau'off : ∀ ω, ¬ ((ofLp (z (smark j ω) ω)).2 = r) → tau' ω = smark j ω := by
    intro ω hc
    simp only [htau'd, if_neg hc]
  have htau'st : IsStoppingTime 𝒢 (fun ω => (tau' ω : ℕ∞)) := by
    intro n
    have hmeas : MeasurableSet[𝒢 n] ({ω | smark j ω ≤ n} ∩ ((((Tst n) ⁻¹' {r}) ∩
        (⋃ m ∈ Finset.range (n + 1), ({ω | smark j ω ≤ m} ∩ {ω | Qp m ω})))
          ∪ (((Tst n) ⁻¹' {r})ᶜ))) := by
      refine MeasurableSet.inter (hstG (smark j) hσst n) (MeasurableSet.union ?_ ?_)
      · refine MeasurableSet.inter ((hTstG n).measurable (measurableSet_singleton r)) ?_
        refine MeasurableSet.biUnion (Set.to_countable _) (fun m hm => ?_)
        have hmn : m ≤ n := by have h := Finset.mem_range.mp hm; omega
        exact ((𝒢.mono hmn) _ (hstG (smark j) hσst m)).inter ((𝒢.mono hmn) _ (hQpG m))
      · exact ((hTstG n).measurable (measurableSet_singleton r)).compl
    refine MeasurableSet.congr hmeas ?_
    ext ω
    show (_ ∈ _) ↔ ((tau' ω : ℕ∞) ≤ (n : ℕ∞))
    rw [Nat.cast_le]
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_union,
      Set.mem_preimage, Set.mem_singleton_iff, Set.mem_compl_iff, Set.mem_iUnion,
      Finset.mem_range, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hTstval n ω h1] at h2
      rcases h2 with ⟨hc, m, hm1, hm2⟩ | hc
      · simp only [htau'd, if_pos hc]
        exact (Nat.find_le_iff (hex ω) n).mpr ⟨m, by omega, hm2⟩
      · rw [htau'off ω hc]; exact h1
    · intro h
      have h1 : smark j ω ≤ n := le_trans (hσtau' ω) h
      refine ⟨h1, ?_⟩
      rw [hTstval n ω h1]
      by_cases hc : (ofLp (z (smark j ω) ω)).2 = r
      · refine Or.inl ⟨hc, ?_⟩
        simp only [htau'd, if_pos hc] at h
        obtain ⟨m, hm1, hm2⟩ := (Nat.find_le_iff (hex ω) n).mp h
        exact ⟨m, by omega, hm2⟩
      · exact Or.inr hc
  -- ===== lattice-function helpers =====
  have htau'meas : Measurable tau' := hstmeas tau' htau'st
  have haaqq : (aa : ℤ) ≤ (qq : ℤ) := by
    have h1 : aa ≤ qq := by
      rw [haad, hqqd]
      calc 2 ^ (kk - N) ≤ 2 ^ kk := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 1 * 2 ^ kk := by ring
        _ ≤ T * 2 ^ kk := Nat.mul_le_mul_right _ (by omega)
    exact_mod_cast h1
  have hbddg : ∀ g : ℤ → ℝ, ∃ C : ℝ, ∀ i : ℤ, (aa:ℤ) ≤ i → i ≤ (qq:ℤ) → |g i| ≤ C := by
    intro g
    have hne : (Finset.Icc (aa:ℤ) (qq:ℤ)).Nonempty := ⟨(aa:ℤ), Finset.mem_Icc.mpr ⟨le_rfl, haaqq⟩⟩
    refine ⟨(Finset.Icc (aa:ℤ) (qq:ℤ)).sup' hne (fun i => |g i|), fun i h1 h2 => ?_⟩
    exact Finset.le_sup' (fun i => |g i|) (Finset.mem_Icc.mpr ⟨h1, h2⟩)
  have hξmeasG : ∀ m n : ℕ, m < n → Measurable[𝒢 n] (ξ m) := fun m n hmn =>
    ((hξmeas m).mono (𝒢.mono (by omega))).measurable
  have hSmeasG : ∀ n : ℕ, Measurable[𝒢 n] (S n) := by
    intro n
    rw [hSd]
    refine Measurable.add measurable_const (Finset.measurable_sum _ (fun m hm => ?_))
    have hmn : m < n := Finset.mem_range.mp hm
    refine Measurable.ite ((𝒢.mono (le_of_lt hmn)) _ (hliveG m)) ?_ measurable_const
    rw [hΞd]
    exact Measurable.ite ((hξmeasG m n hmn) (measurableSet_singleton 1))
      measurable_const measurable_const
  have hgSmeasG : ∀ (g : ℤ → ℝ) (k n : ℕ), k ≤ n → Measurable[𝒢 n] (fun ω => g (S k ω)) :=
    fun g k n h => measurable_from_top.comp ((hSmeasG k).mono (𝒢.mono h) le_rfl)
  have hgSmeas : ∀ (g : ℤ → ℝ) (k : ℕ), Measurable (fun ω => g (S k ω)) :=
    fun g k => (hgSmeasG g k k le_rfl).mono (𝒢.le k) le_rfl
  have hgSint : ∀ (g : ℤ → ℝ) (C : ℝ),
      (∀ i : ℤ, (aa:ℤ) ≤ i → i ≤ (qq:ℤ) → |g i| ≤ C) →
      ∀ k : ℕ, Integrable (fun ω => g (S k ω)) μ := by
    intro g C hC k
    refine Integrable.mono' (integrable_const C) (hgSmeas g k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    obtain ⟨h1, h2⟩ := hSrange k ω
    rw [Real.norm_eq_abs]
    exact hC _ h1 h2
  have hSwin : ∀ (n : ℕ) (ω : Ω), smark j ω ≤ n → n < tau' ω →
      (aa:ℤ) < S n ω ∧ S n ω < (bb:ℤ) := by
    intro n ω h1 h2
    have hnτ : n < τ ω := lt_of_lt_of_le h2 (htau'τ ω)
    obtain ⟨e1, -⟩ := hSlive n ω hnτ
    refine ⟨e1, ?_⟩
    have h3 := htau'min ω n h1 h2
    rw [hQpd] at h3
    have h4 : (ofLp (z n ω)).2 < 8 * r := by
      by_contra hcon
      exact h3 (Or.inr (Or.inl (by linarith only [hcon])))
    rw [hlat n ω, ← hεbb] at h4
    have h5 : (S n ω : ℝ) < (bb:ℝ) := lt_of_mul_lt_mul_left (by linarith only [h4]) hε0.le
    exact_mod_cast h5
  -- ===== Claim T': the conditional supersolution bound along the portion. =====
  have claimT := StoppedLatticeSupersolutionBound μ 𝒢 ξ Ξ S τ (smark j) tau' aa bb qq
    hξpm hξmeas hξcond hΞd hSstep hSrange hσst hσmeas htau'st htau'meas hσtau' htau'τ
    hstG hrandidx2 hbddg hgSmeasG hgSmeas hSwin
  -- ===== Step 1(b): the mark is at or above its level, and `{t_τ = δ_N} ⊆ R_j`. =====
  have hccj₀ : (cc:ℤ) ≤ (j₀:ℤ) := by
    have h1 : cc ≤ j₀ := by
      rw [hccd, hj₀d]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    exact_mod_cast h1
  have hSmark : ∀ (n : ℕ) (ω : Ω), n ≤ smark j ω → (cc:ℤ) ≤ S n ω := by
    intro n ω
    induction n with
    | zero => intro _; rw [hS0 ω]; exact hccj₀
    | succ n ih =>
        intro hn
        have hn1 : n < smark j ω := by omega
        have hih := ih (by omega)
        obtain ⟨hnτ, hne⟩ := hσlt ω n hn1
        have hSne : S n ω ≠ (cc:ℤ) := by
          intro hcon
          apply hne
          rw [hlat n ω, hcon, ← hrd]
          exact hεcc
        have hgt : (cc:ℤ) < S n ω := by omega
        rw [hSstep n ω, if_pos hnτ, hΞd]
        by_cases h : ξ n ω = 1 <;> simp [h] <;> omega
  have hRjsub : ∀ ω, (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N →
      (ofLp (z (smark j ω) ω)).2 = r := by
    intro ω hτN
    have h1 : (cc:ℤ) ≤ S (smark j ω) ω := hSmark (smark j ω) ω le_rfl
    have h2 : r ≤ (ofLp (z (smark j ω) ω)).2 := by
      rw [hlat (smark j ω) ω, ← hεcc]
      have h3 : (cc:ℝ) ≤ (S (smark j ω) ω : ℝ) := by exact_mod_cast h1
      exact mul_le_mul_of_nonneg_left h3 hε0.le
    rcases hσalt ω with h4 | h4
    · -- σ = τ
      have h5 : (ofLp (z (smark j ω) ω)).2 = (1 / 2 : ℝ) ^ N := by rw [h4]; exact hτN
      have h6 : (1 / 2 : ℝ) ^ N ≤ r := by
        rw [← hεaa, ← hεcc]
        have h7 : (aa:ℝ) ≤ (cc:ℝ) := by exact_mod_cast haacc
        exact mul_le_mul_of_nonneg_left h7 hε0.le
      rw [h5]
      linarith only [h2, h5, h6]
    · rw [← hrd] at h4; exact h4
  -- ===== Step 6(a): the number of portion steps. =====
  -- the bound is `ExpectedPortionLengthBound`, which sees only the lattice data; Claim T'
  -- at `A = Set.univ`, with its indicator cleared, is its supersolution hypothesis.
  have haaR : (0:ℝ) ≤ (aa:ℝ) := Nat.cast_nonneg aa
  have hbb0 : 0 < bb := by rw [hbbd]; positivity
  obtain ⟨hnstint, htimebudget⟩ :=
    ExpectedPortionLengthBound μ S τ (smark j) tau' aa bb hσmeas htau'meas htau'τ
      hτint hrandidx hrandidx2 hgSmeas hSwin (fun hf uf hu0 hpoi n => by
        have h1 := claimT hf uf Set.univ hu0 hpoi MeasurableSet.univ
          (fun n => by
            have he : (Set.univ : Set Ω) ∩ {ω | smark j ω ≤ n} = {ω | smark j ω ≤ n} := by
              rw [Set.univ_inter]
            rw [he]
            exact hstG (smark j) hσst n) n
        have hind1 : ∀ ω : Ω, Set.indicator (Set.univ : Set Ω) (fun _ => (1:ℝ)) ω = 1 := by
          intro ω
          rw [Set.indicator_of_mem (Set.mem_univ ω)]
        simpa only [hind1, one_mul] using h1)
  -- ===== Steps 3 and 6(c): the fitted frame and the velocity bound. =====
  obtain ⟨LK, hLKd⟩ : ∃ t : ℝ, t = 1 + Real.log (K + 10) := ⟨_, rfl⟩
  have hLK1 : (1:ℝ) ≤ LK := by
    rw [hLKd]
    have h1 : (0:ℝ) ≤ Real.log (K + 10) := Real.log_nonneg (by linarith only [hK2])
    linarith only [h1]
  have hεr1 : ε / r ≤ 1 := by
    rw [div_le_one hr0]
    have h1 : (1/2:ℝ) ^ N ≤ r := by
      rw [← hεaa, ← hεcc]
      have h2 : (aa:ℝ) ≤ (cc:ℝ) := by exact_mod_cast haacc
      exact mul_le_mul_of_nonneg_left h2 hε0.le
    have h3 : (0:ℝ) < (1/2:ℝ) ^ N := by positivity
    linarith only [hεN, h1, h3]
  have hεr0 : (0:ℝ) < ε / r := by positivity
  have hQ'bd : ∀ (n : ℕ) (ω : Ω), (ofLp (z (smark j ω) ω)).2 = r → smark j ω ≤ n →
      n < tau' ω → ‖Q₀ n ω - pj j ω‖ ≤ C₂ * (LK + |Real.log ((ε / r) * (S n ω : ℝ))|) := by
    intro n ω hR hn1 hn2
    have hnτ : n < τ ω := lt_of_lt_of_le hn2 (htau'τ ω)
    have hfitω : IsFit C₀ v (z (smark j ω) ω) r (pj j ω) (aj j ω) := by
      have hR' : (ofLp (z (smark j ω) ω)).2 = (1 / 2 : ℝ) ^ j := by rw [hR, hrd]
      have h1 := hfitσ ω hR'
      rw [← hrd] at h1
      exact h1
    have hzeq : (toLp 2 ((ofLp (z (smark j ω) ω)).1, r) : WithLp 2 (F × ℝ))
        = z (smark j ω) ω := by
      rw [← hR]
    have hfit2 : IsFit C₀ v (toLp 2 ((ofLp (z (smark j ω) ω)).1, r)) r (pj j ω) (aj j ω) := by
      rw [hzeq]; exact hfitω
    obtain ⟨hvbarclass, hvbarcent, hvbarJ, -⟩ := FrameEnvelopeCovariance C₀ κ hC₀ hκ.le v hv hJ
      r hr0 (ofLp (z (smark j ω) ω)).1 (pj j ω) (aj j ω) hfit2
    obtain ⟨vbar, hvbard⟩ : ∃ f : WithLp 2 (F × ℝ) → ℝ, f = fun ζ =>
        FrameChange v (toLp 2 ((ofLp (z (smark j ω) ω)).1, r)) r (pj j ω) (aj j ω)
          (ζ - toLp 2 ((0 : F), (1 : ℝ))) := ⟨_, rfl⟩
    rw [← hvbard] at hvbarclass hvbarcent hvbarJ
    have hεtn : ε < (ofLp (z n ω)).2 := by
      obtain ⟨e1, -⟩ := hSlive n ω hnτ
      have e2 : (aa:ℤ) + 1 ≤ S n ω := by omega
      have e3 : (1:ℝ) < (S n ω : ℝ) := by
        have e4 : (1:ℤ) < S n ω := by
          have e5 : (4:ℤ) ≤ (aa:ℤ) := by exact_mod_cast haa4
          omega
        exact_mod_cast e4
      rw [hlat n ω]
      nlinarith only [e3, hε0]
    obtain ⟨-, -, -, hgradbar, -, -⟩ := FrameVelocityCovariance C₀ κ hC₀ hκ.le v hv hcent hJ
      r hr0 (ofLp (z (smark j ω) ω)).1 (pj j ω) (aj j ω) hfit2 vbar hvbard ε hε0
      (z n ω) (zp n ω) (zm n ω) hεtn (hpair n ω hnτ) (Q₀ n ω) (hgrad n ω)
      (toLp 2 (r⁻¹ • ((ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - r) • pj j ω), (ofLp (z n ω)).2 / r))
      (toLp 2 (r⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (zp n ω)).2 - r) • pj j ω), (ofLp (zp n ω)).2 / r))
      (toLp 2 (r⁻¹ • ((ofLp (zm n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (zm n ω)).2 - r) • pj j ω), (ofLp (zm n ω)).2 / r))
      rfl rfl rfl
    -- the primed state is inside the box
    have hynorm : ‖r⁻¹ • ((ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - r) • pj j ω)‖ ≤ K + 10 := by
      have h1 := htau'min ω n hn1 hn2
      rw [hQpd] at h1
      have h2 : Yst n ω < K := by
        by_contra hcon
        exact h1 (Or.inr (Or.inr (by linarith only [hcon])))
      rw [hYstval n ω hn1] at h2
      have h3 : ‖r⁻¹ • ((ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
          - ((ofLp (z n ω)).2 - r) • pj j ω)‖
          = r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
            - ((ofLp (z n ω)).2 - r) • pj j ω‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r⁻¹)]
      rw [h3]
      linarith only [h2]
    have htnbd : (ofLp (z n ω)).2 < 8 * r := by
      have h1 := htau'min ω n hn1 hn2
      rw [hQpd] at h1
      by_contra hcon
      exact h1 (Or.inr (Or.inl (by linarith only [hcon])))
    have hsnbd : |(ofLp (z n ω)).2 / r| ≤ K + 10 := by
      have h1 : (0:ℝ) < (ofLp (z n ω)).2 := by linarith only [hεtn, hε0]
      rw [abs_of_nonneg (by positivity)]
      rw [div_le_iff₀ hr0]
      nlinarith only [htnbd, hK2, hr0]
    have hεrs : ε / r < (ofLp (z n ω)).2 / r := by
      rw [div_lt_div_iff_of_pos_right hr0]
      exact hεtn
    have h5 := hC₂b vbar hvbarclass hvbarcent hvbarJ (K + 10) (by linarith only [hK2])
      (r⁻¹ • ((ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - r) • pj j ω)) ((ofLp (z n ω)).2 / r) (ε / r)
      hynorm hsnbd hεr0 hεr1 hεrs (Q₀ n ω - pj j ω) hgradbar
    rw [← hLKd] at h5
    have hsneq : (ofLp (z n ω)).2 / r = (ε / r) * (S n ω : ℝ) := by
      rw [hlat n ω]
      ring
    rw [hsneq] at h5
    exact h5
  -- ===== Step 6(b,c): the logarithmic grid sum. =====
  obtain ⟨uw, huwd⟩ : ∃ f : ℤ → ℝ, f = fun i =>
      if (aa:ℤ) < i ∧ i < (bb:ℤ) then (ε / r) ^ 2 * |Real.log ((ε / r) * (i:ℝ))| ^ 2
      else 0 := ⟨_, rfl⟩
  have hεrbb : (ε / r) * (bb:ℝ) = 8 := by
    rw [div_mul_eq_mul_div, hεbb]
    field_simp
  have haabbZ : (aa:ℤ) < (bb:ℤ) := by
    have h1 : aa < bb := by
      have h2 : cc < bb := hccbb
      omega
    exact_mod_cast h1
  have haabbR : (0:ℝ) < (bb:ℝ) - (aa:ℝ) := by
    have h1 : (aa:ℝ) < (bb:ℝ) := by
      have h2 : (aa:ℤ) < (bb:ℤ) := haabbZ
      exact_mod_cast h2
    linarith only [h1]
  obtain ⟨huwsumint', hlogsum⟩ :=
    LogGridSumBound μ 𝒢 S (smark j) tau' τ aa bb qq ε r Λ uw hεr0 hbb0 haa4 haaR
      haabbR hεrbb hΛd hΛ0 huwd hσst hσmeas htau'meas htau'τ hτint hSrange hstG
      hrandidx hrandidx2 hbddg hgSmeas claimT
  -- ===== Step 7: the frame travel bound. =====
  obtain ⟨hwtravel, hwmeasN, hwhit⟩ := hswt N hN ε Ω m0 μ 𝒢 ξ z zp zm Q₀ τ hwc hbudget
  -- the three inputs `MarkFrameTravelBound` takes in narrowed form
  have hpbd : ∀ ω, ‖pj j ω‖ ≤ CΓ * (LB + (j:ℝ)) := by
    intro ω
    have h1 := hc1 ω
    have h2 : (0:ℝ) ≤ |aj j ω| := abs_nonneg _
    linarith only [h1, h2]
  have huwvalh : ∀ (n : ℕ) (ω : Ω), smark j ω ≤ n → n < tau' ω →
      uw (S n ω) = (ε / r) ^ 2 * |Real.log ((ε / r) * (S n ω : ℝ))| ^ 2 := by
    intro n ω hn1 hn2
    obtain ⟨e1, e2⟩ := hSwin n ω hn1 hn2
    simp only [huwd]
    rw [if_pos ⟨e1, e2⟩]
  have hbudgetB : ∫ ω, (∑ n ∈ Finset.range (τ ω),
      (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ ≤ B₀ := by
    rw [hB₀d, hLBd]
    exact hbudget
  -- the travel bound
  rw [← hLKd] at hKkey
  obtain ⟨hI1, htravbd⟩ :=
    MarkFrameTravelBound μ 𝒢 z zp zm Q₀ S smark pj tau' τ j bb ε r
      (CΓ * (LB + (j:ℝ))) B₀ C' CM C₂ LK Λ uw hwtravel hpbd hσst htau'st hτst
      hσtau' htau'τ hpmeasG hnstint huwsumint' hlogsum huwvalh hQ'bd htau'off
      htimebudget hbudgetB hr0 hεrbb hCMd hCM0 hC₂0 hΛ0 hC'CM hC'4 hLK1
  -- Markov's inequality
  have hmarkov : ∀ (A : Set Ω) (f : Ω → ℝ) (c : ℝ), MeasurableSet A → 0 < c →
      Integrable f μ → (∀ ω, 0 ≤ f ω) → (∀ ω ∈ A, c ≤ f ω) →
      (μ A).toReal * c ≤ ∫ ω, f ω ∂μ := by
    intro A f c hA hc hfi hf0 hAf
    have hind : Integrable (A.indicator (fun _ => c)) μ := (integrable_const c).indicator hA
    have hle : ∀ ω, A.indicator (fun _ => c) ω ≤ f ω := by
      intro ω
      by_cases hc' : ω ∈ A
      · rw [Set.indicator_of_mem hc']
        exact hAf ω hc'
      · rw [Set.indicator_of_notMem hc']
        exact hf0 ω
    have h1 := integral_mono hind hfi hle
    rw [integral_indicator hA, setIntegral_const, smul_eq_mul] at h1
    exact h1
  -- ===== Step 8: the two cutoff probabilities. =====
  obtain ⟨hB1, hB2⟩ :=
    MarkCutoffProbabilities μ 𝒢 z S smark pj j tau' Tst Yst aa bb cc kk ε r K C' B₀ LK
      hε0 hr0 hccd hbbd hεcc hεbb haacc haaR haabbR hK2 hKkey hlat hzt hσst hσmeas htau'meas
      hσtau' hstG hrandidx hrandidx2 hgSmeas hTstG hTstval hYstG hYstval hmarkov hI1
      htravbd claimT
  -- ===== Step 9: the combination. =====
  have hcover : {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N} ⊆
      {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
        ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
          - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖ ≤ K * (1 / 2 : ℝ) ^ j}
      ∪ (({ω | (ofLp (z (smark j ω) ω)).2 = r} ∩ {ω | K ≤ Yst (tau' ω) ω})
        ∪ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
          ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2})) := by
    intro ω hω
    have hτN : (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N := hω
    have hR : (ofLp (z (smark j ω) ω)).2 = r := hRjsub ω hτN
    by_cases hb1 : K ≤ Yst (tau' ω) ω
    · exact Or.inr (Or.inl ⟨hR, hb1⟩)
    · by_cases hb2 : 8 * r ≤ (ofLp (z (tau' ω) ω)).2
      · exact Or.inr (Or.inr ⟨hR, hb2⟩)
      · have hspec := htau'spec ω hR
        rw [hQpd] at hspec
        have hττ' : tau' ω = τ ω := by
          rcases hspec with h | h | h
          · exact h
          · exact absurd h hb2
          · exact absurd h hb1
        refine Or.inl ⟨hτN, ?_⟩
        have h1 : Yst (τ ω) ω < K := by
          rw [← hττ']
          exact lt_of_not_ge hb1
        rw [hYstval (τ ω) ω (hστ ω)] at h1
        rw [← hrd]
        have h3 : r * (r⁻¹ * ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
            - ((ofLp (z (τ ω) ω)).2 - r) • pj j ω‖) < r * K :=
          mul_lt_mul_of_pos_left h1 hr0
        rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hr0), one_mul] at h3
        linarith only [h3]
  have hfin : (1:ℝ) / 2 ≤ (μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
      ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖
        ≤ K * (1 / 2 : ℝ) ^ j}).toReal := by
    have hle : μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}
        ≤ μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∧
            ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
              - ((ofLp (z (τ ω) ω)).2 - (1 / 2 : ℝ) ^ j) • pj j ω‖ ≤ K * (1 / 2 : ℝ) ^ j}
          + (μ ({ω | (ofLp (z (smark j ω) ω)).2 = r} ∩ {ω | K ≤ Yst (tau' ω) ω})
            + μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
              ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2})) := by
      refine le_trans (measure_mono hcover) (le_trans (measure_union_le _ _) ?_)
      exact add_le_add le_rfl (measure_union_le _ _)
    have hne2 : μ ({ω | (ofLp (z (smark j ω) ω)).2 = r} ∩ {ω | K ≤ Yst (tau' ω) ω})
        + μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
          ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2}) ≠ ⊤ :=
      ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, hne2⟩) hle
    rw [ENNReal.toReal_add (measure_ne_top _ _) hne2,
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
    linarith only [h2, hwhit, hB1, hB2]
  exact hfin
