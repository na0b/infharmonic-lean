import InfHarmonic.Preamble
set_option maxHeartbeats 400000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 5 of Proposition 6.7: the stopped contact walk reaches the lower time
level with probability at least `3/4`. The walk's time coordinate is carried by
the lattice height `S` with spacing `ε`, so the upper time level `8` is the top
lattice site `q`; the hypothesis that `∫ S_n / q ≤ 1/8` at every fixed time `n`
is the optional-stopping bound for the symmetric walk started at the level
`1 = ε j₀` of a time interval of length `8 = ε q`, and bounds the probability of
an upper time stop by `1/8`. The hypothesis that the expected maximal horizontal
displacement is at most `M` with `8 M ≤ R` bounds the probability of a
horizontal stop by `1/8` through Markov's inequality. Since the terminal point
always satisfies one of the three stopping alternatives, the two bounds leave
probability at least `3/4` for the lower time level. The ambient space is an
arbitrary finite-dimensional real inner-product space `F`. -/
theorem StoppedWalkLowerExitProbability {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (z : ℕ → Ω → WithLp 2 (F × ℝ)) (S : ℕ → Ω → ℤ) (τ : Ω → ℕ)
    (ε M R : ℝ) (q N : ℕ)
    (hε0 : 0 < ε) (hεq : ε * (q : ℝ) = 8) (hR0 : 0 < R)
    (hlat : ∀ n ω, (ofLp (z n ω)).2 = ε * ((S n ω : ℤ) : ℝ))
    (hz0 : ∀ ω, (ofLp (z 0 ω)).1 = (0 : F))
    (hS0q : ∀ n ω, (0 : ℤ) ≤ S n ω ∧ S n ω ≤ (q : ℤ))
    (hSfroz : ∀ (n : ℕ) (ω : Ω), τ ω ≤ n → S n ω = S (τ ω) ω)
    (hSmeas : ∀ n : ℕ, Measurable (fun ω => ((S n ω : ℤ) : ℝ)))
    (hxnmeas : ∀ n : ℕ, Measurable (fun ω => ‖(ofLp (z n ω)).1‖))
    (hτmeas : Measurable τ)
    (hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ, (∀ m, Measurable (G m)) →
      Measurable (fun ω => G (ζ ω) ω))
    (hupper : ∀ n : ℕ, ∫ ω, (((S n ω : ℤ) : ℝ) / (q : ℝ)) ∂μ ≤ 1 / 8)
    (hexit : ∀ ω, (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∨
      (ofLp (z (τ ω) ω)).2 = 8 ∨ R ≤ ‖(ofLp (z (τ ω) ω)).1‖)
    (hsupint : Integrable (fun ω => (Finset.Icc 0 (τ ω)).sup'
      (Finset.nonempty_Icc.mpr (Nat.zero_le (τ ω)))
      (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖)) μ)
    (hsupbd : ∫ ω, (Finset.Icc 0 (τ ω)).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le (τ ω)))
      (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖) ∂μ ≤ M)
    (hMR : 8 * M ≤ R) :
    MeasurableSet {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N} ∧
      (3 : ℝ) / 4 ≤ (μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}).toReal := by
  classical
  have hqR0 : (0:ℝ) < (q:ℝ) := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hεq; norm_num at hεq
    · exact_mod_cast h
  -- measurability of the terminal lattice height, time level and displacement
  have hSτmeas : Measurable (fun ω => ((S (τ ω) ω : ℤ) : ℝ)) :=
    hrandidx τ hτmeas (fun n ω => ((S n ω : ℤ) : ℝ)) hSmeas
  have htτ : ∀ ω, (ofLp (z (τ ω) ω)).2 = ε * ((S (τ ω) ω : ℤ) : ℝ) := fun ω => hlat (τ ω) ω
  have hXτmeas : Measurable (fun ω => (ofLp (z (τ ω) ω)).2) := by
    have he : (fun ω => (ofLp (z (τ ω) ω)).2) = fun ω => ε * ((S (τ ω) ω : ℤ) : ℝ) :=
      funext htτ
    rw [he]
    exact hSτmeas.const_mul ε
  have hBmeas : MeasurableSet {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N} :=
    hXτmeas (measurableSet_singleton _)
  have hB8meas : MeasurableSet {ω | (ofLp (z (τ ω) ω)).2 = 8} :=
    hXτmeas (measurableSet_singleton _)
  have hARmeas : MeasurableSet {ω | R ≤ ‖(ofLp (z (τ ω) ω)).1‖} :=
    (hrandidx τ hτmeas (fun n ω => ‖(ofLp (z n ω)).1‖) hxnmeas) measurableSet_Ici
  -- the mean terminal lattice height, from the uniform bound at every fixed time
  have hupperlim : ∫ ω, (((S (τ ω) ω : ℤ) : ℝ) / (q : ℝ)) ∂μ ≤ 1 / 8 := by
    refine le_of_tendsto (MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ => (1:ℝ)) (fun n => ?_) (integrable_const 1) (fun n => ?_) ?_)
      (Filter.Eventually.of_forall hupper)
    · exact ((hSmeas n).div_const (q:ℝ)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      obtain ⟨e1, e2⟩ := hS0q n ω
      have e3 : (0:ℝ) ≤ ((S n ω : ℤ) : ℝ) := by exact_mod_cast e1
      have e4 : ((S n ω : ℤ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast e2
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_one hqR0]
      exact e4
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      refine tendsto_atTop_of_eventually_const (i₀ := τ ω) (fun n hn => ?_)
      rw [hSfroz n ω hn]
  have hmarkov : ∀ (A : Set Ω) (f : Ω → ℝ) (c : ℝ), MeasurableSet A → 0 < c →
      Integrable f μ → (∀ ω, 0 ≤ f ω) → (∀ ω ∈ A, c ≤ f ω) →
      (μ A).toReal * c ≤ ∫ ω, f ω ∂μ := by
    intro A f c hA hc hfi hf0 hAf
    have hind : Integrable (A.indicator (fun _ => c)) μ :=
      (integrable_const c).indicator hA
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
  -- the upper time level is reached with probability at most 1/8
  have hnn : ∀ ω, (0:ℝ) ≤ ((S (τ ω) ω : ℤ) : ℝ) / (q:ℝ) := by
    intro ω
    have e3 : (0:ℝ) ≤ ((S (τ ω) ω : ℤ) : ℝ) := by exact_mod_cast (hS0q (τ ω) ω).1
    positivity
  have hP8 : (μ {ω | (ofLp (z (τ ω) ω)).2 = 8}).toReal ≤ 1 / 8 := by
    have h1 := hmarkov {ω | (ofLp (z (τ ω) ω)).2 = 8}
      (fun ω => ((S (τ ω) ω : ℤ) : ℝ) / (q : ℝ)) 1 hB8meas one_pos
      (by
        refine Integrable.mono' (integrable_const (1:ℝ))
          (hSτmeas.div_const (q:ℝ)).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        have e4 : ((S (τ ω) ω : ℤ) : ℝ) ≤ (q:ℝ) := by exact_mod_cast (hS0q (τ ω) ω).2
        rw [Real.norm_eq_abs, abs_of_nonneg (hnn ω), div_le_one hqR0]
        exact e4)
      hnn
      (fun ω hω => by
        have hval : (ofLp (z (τ ω) ω)).2 = 8 := hω
        rw [htτ ω] at hval
        have e5 : ((S (τ ω) ω : ℤ) : ℝ) = (q:ℝ) := by
          have h6 : ε * ((S (τ ω) ω : ℤ) : ℝ) = ε * (q:ℝ) := by rw [hval, hεq]
          exact mul_left_cancel₀ (ne_of_gt hε0) h6
        rw [e5, div_self (ne_of_gt hqR0)])
    rw [mul_one] at h1
    linarith only [h1, hupperlim]
  -- the horizontal cutoff is reached with probability at most 1/8
  have hxτle : ∀ ω, ‖(ofLp (z (τ ω) ω)).1‖
      ≤ (Finset.Icc 0 (τ ω)).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le (τ ω)))
        (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖) := by
    intro ω
    have h1 := Finset.le_sup' (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖)
      (Finset.mem_Icc.mpr ⟨Nat.zero_le (τ ω), le_rfl⟩)
    calc ‖(ofLp (z (τ ω) ω)).1‖ = ‖(ofLp (z (τ ω) ω)).1 - (ofLp (z 0 ω)).1‖ := by
          rw [hz0 ω, sub_zero]
      _ ≤ _ := h1
  have hsupnn : ∀ ω, (0:ℝ) ≤ (Finset.Icc 0 (τ ω)).sup'
      (Finset.nonempty_Icc.mpr (Nat.zero_le (τ ω)))
      (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖) :=
    fun ω => le_trans (norm_nonneg _) (hxτle ω)
  have hPR : (μ {ω | R ≤ ‖(ofLp (z (τ ω) ω)).1‖}).toReal ≤ 1 / 8 := by
    have h1 := hmarkov {ω | R ≤ ‖(ofLp (z (τ ω) ω)).1‖}
      (fun ω => (Finset.Icc 0 (τ ω)).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le (τ ω)))
        (fun x => ‖(ofLp (z x ω)).1 - (ofLp (z 0 ω)).1‖)) R hARmeas hR0 hsupint hsupnn
      (fun ω hω => le_trans hω (hxτle ω))
    have h2 := le_trans h1 hsupbd
    have h5 : (μ {ω | R ≤ ‖(ofLp (z (τ ω) ω)).1‖}).toReal * R ≤ (1 / 8 : ℝ) * R := by
      linarith only [h2, hMR]
    exact le_of_mul_le_mul_right h5 hR0
  -- the union bound over the two bad alternatives
  have hcover : {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}ᶜ
      ⊆ {ω | (ofLp (z (τ ω) ω)).2 = 8} ∪ {ω | R ≤ ‖(ofLp (z (τ ω) ω)).1‖} := by
    intro ω hω
    rcases hexit ω with h | h | h
    · exact absurd h hω
    · exact Or.inl h
    · exact Or.inr h
  have hsum1 : (μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}).toReal
      + (μ ({ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}ᶜ)).toReal = 1 := by
    have h1 := measure_add_measure_compl (μ := μ) hBmeas
    rw [measure_univ] at h1
    have h2 : (μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}).toReal
        + (μ ({ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}ᶜ)).toReal
        = ((μ {ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N})
            + (μ ({ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}ᶜ))).toReal :=
      (ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)).symm
    rw [h2, h1]
    simp
  have hcompl : (μ ({ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}ᶜ)).toReal ≤ 1 / 4 := by
    have h1 : μ ({ω | (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N}ᶜ)
        ≤ μ {ω | (ofLp (z (τ ω) ω)).2 = 8} + μ {ω | R ≤ ‖(ofLp (z (τ ω) ω)).1‖} :=
      le_trans (measure_mono hcover) (measure_union_le _ _)
    have h2 := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
    rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
    linarith only [h2, hP8, hPR]
  refine ⟨hBmeas, ?_⟩
  linarith only [hsum1, hcompl]
