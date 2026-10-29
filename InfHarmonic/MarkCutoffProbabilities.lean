module

public import InfHarmonic.IsMarkData
public import InfHarmonic.StoppedWalkTravel
public import InfHarmonic.StoppedLatticeSupersolutionBound

@[expose] public section
set_option maxHeartbeats 400000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 8 of Proposition 6.7: the two cutoff probabilities.  On the event that
the `j`-th mark sits at its own level `r`, the probability that the fitted
displacement ever reaches `K` is at most `1/8` by the travel bound and Markov's
inequality, and the probability that the portion stopping time lands at the
upper time level `8 r` is at most `1/8` by the Green-function estimate of
Claim T'.  Both bounds are uniform in `j` and `N`. -/
theorem MarkCutoffProbabilities {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (z : ℕ → Ω → WithLp 2 (F × ℝ)) (S : ℕ → Ω → ℤ)
    (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (j : ℕ)
    (tau' : Ω → ℕ) (Tst Yst : ℕ → Ω → ℝ)
    (aa bb cc kk : ℕ) (ε r K C' B₀ LK : ℝ)
    (hε0 : 0 < ε) (hr0 : (0:ℝ) < r)
    (hccd : cc = 2 ^ (kk - j)) (hbbd : bb = 8 * 2 ^ (kk - j))
    (hεcc : ε * (cc : ℝ) = r) (hεbb : ε * (bb : ℝ) = 8 * r)
    (haacc : aa ≤ cc) (haaR : (0:ℝ) ≤ (aa:ℝ))
    (haabbR : (0:ℝ) < (bb:ℝ) - (aa:ℝ))
    (hK2 : (2:ℝ) ≤ K)
    (hKkey : 8 * C' * (LK + Real.sqrt B₀) ≤ K)
    (hlat : ∀ n ω, (ofLp (z n ω)).2 = ε * (S n ω : ℝ))
    (hzt : ∀ n, StronglyMeasurable (fun ω => (ofLp (z n ω)).2))
    (hσst : IsStoppingTime 𝒢 (fun ω => (smark j ω : ℕ∞)))
    (hσmeas : Measurable (smark j)) (htau'meas : Measurable tau')
    (hσtau' : ∀ ω, smark j ω ≤ tau' ω)
    (hstG : ∀ (ζ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) →
      ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | ζ ω ≤ n})
    (hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ,
      (∀ m, Measurable (G m)) → Measurable (fun ω => G (ζ ω) ω))
    (hrandidx2 : ∀ (ζ η : Ω → ℕ), Measurable ζ → Measurable η →
      ∀ G : ℕ → ℕ → Ω → ℝ, (∀ n m, Measurable (G n m)) →
      Measurable (fun ω => G (ζ ω) (η ω) ω))
    (hgSmeas : ∀ (g : ℤ → ℝ) (k : ℕ), Measurable (fun ω => g (S k ω)))
    (hTstG : ∀ m, StronglyMeasurable[𝒢 m] (Tst m))
    (hTstval : ∀ (m : ℕ) (ω : Ω), smark j ω ≤ m → Tst m ω = (ofLp (z (smark j ω) ω)).2)
    (hYstG : ∀ m, Measurable[𝒢 m] (Yst m))
    (hYstval : ∀ (m : ℕ) (ω : Ω), smark j ω ≤ m →
      Yst m ω = r⁻¹ * ‖(ofLp (z m ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z m ω)).2 - r) • pj j ω‖)
    (hmarkov : ∀ (A : Set Ω) (f : Ω → ℝ) (c : ℝ), MeasurableSet A → 0 < c →
      Integrable f μ → (∀ ω, 0 ≤ f ω) → (∀ ω ∈ A, c ≤ f ω) →
      (μ A).toReal * c ≤ ∫ ω, f ω ∂μ)
    (hI1 : Integrable (fun ω => (Finset.Icc (smark j ω) (tau' ω)).sup'
      (Finset.nonempty_Icc.mpr (hσtau' ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖)) μ)
    (htravbd : ∫ ω, (Finset.Icc (smark j ω) (tau' ω)).sup'
      (Finset.nonempty_Icc.mpr (hσtau' ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖) ∂μ
      ≤ C' * (LK + Real.sqrt B₀))
    (claimT : ∀ (hf uf : ℤ → ℝ) (A : Set Ω), (∀ i : ℤ, 0 ≤ uf i) →
      (∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) →
        (hf (i + 1) + hf (i - 1)) / 2 - hf i ≤ -(uf i)) →
      MeasurableSet A → (∀ n : ℕ, MeasurableSet[𝒢 n] (A ∩ {ω | smark j ω ≤ n})) →
      ∀ n : ℕ,
        ∫ ω, Set.indicator A (fun _ => (1:ℝ)) ω *
            (hf (S (min (max (smark j ω) n) (tau' ω)) ω)
              + ∑ m ∈ Finset.Ico (smark j ω) (min n (tau' ω)), uf (S m ω)) ∂μ
          ≤ ∫ ω, Set.indicator A (fun _ => (1:ℝ)) ω * hf (S (smark j ω) ω) ∂μ) :
    (μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
        ∩ {ω | K ≤ Yst (tau' ω) ω})).toReal ≤ 1 / 8 ∧
      (μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
        ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2})).toReal ≤ 1 / 8 := by
  have hRjmeas : MeasurableSet {ω | (ofLp (z (smark j ω) ω)).2 = r} := by
    have h1 : Measurable (fun ω => (ofLp (z (smark j ω) ω)).2) :=
      hrandidx (smark j) hσmeas (fun n ω => (ofLp (z n ω)).2) (fun n => (hzt n).measurable)
    exact h1 (measurableSet_singleton r)
  have hRjG : ∀ n : ℕ, MeasurableSet[𝒢 n]
      ({ω | (ofLp (z (smark j ω) ω)).2 = r} ∩ {ω | smark j ω ≤ n}) := by
    intro n
    have hmeas : MeasurableSet[𝒢 n] (((Tst n) ⁻¹' {r}) ∩ {ω | smark j ω ≤ n}) :=
      ((hTstG n).measurable (measurableSet_singleton r)).inter (hstG (smark j) hσst n)
    refine MeasurableSet.congr hmeas ?_
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      rw [hTstval n ω h2] at h1
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      rw [hTstval n ω h2]
      exact ⟨h1, h2⟩
  have hYstτ'meas : Measurable (fun ω => Yst (tau' ω) ω) :=
    hrandidx tau' htau'meas (fun m ω => Yst m ω) (fun m => (hYstG m).mono (𝒢.le m) le_rfl)
  have hB1meas : MeasurableSet ({ω | (ofLp (z (smark j ω) ω)).2 = r}
      ∩ {ω | K ≤ Yst (tau' ω) ω}) :=
    hRjmeas.inter (hYstτ'meas measurableSet_Ici)
  have hsupnn : ∀ ω, (0:ℝ) ≤ (Finset.Icc (smark j ω) (tau' ω)).sup'
      (Finset.nonempty_Icc.mpr (hσtau' ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖) := by
    intro ω
    have h1 := Finset.le_sup' (f := fun n => r⁻¹ * ‖(ofLp (z n ω)).1
      - (ofLp (z (smark j ω) ω)).1
      - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖)
      (Finset.mem_Icc.mpr ⟨le_rfl, hσtau' ω⟩)
    refine le_trans ?_ h1
    positivity
  have hB1 : (μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
      ∩ {ω | K ≤ Yst (tau' ω) ω})).toReal ≤ 1 / 8 := by
    have hKpos : (0:ℝ) < K := by linarith only [hK2]
    have hAf : ∀ ω ∈ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
        ∩ {ω | K ≤ Yst (tau' ω) ω}), K ≤ (Finset.Icc (smark j ω) (tau' ω)).sup'
        (Finset.nonempty_Icc.mpr (hσtau' ω))
        (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (smark j ω) ω)).1
          - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖) := by
      intro ω hω
      obtain ⟨hR, hY⟩ := hω
      have hR' : (ofLp (z (smark j ω) ω)).2 = r := hR
      have hY' : K ≤ Yst (tau' ω) ω := hY
      rw [hYstval (tau' ω) ω (hσtau' ω)] at hY'
      have h1 := Finset.le_sup' (f := fun n => r⁻¹ * ‖(ofLp (z n ω)).1
        - (ofLp (z (smark j ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖)
        (Finset.mem_Icc.mpr ⟨hσtau' ω, le_rfl⟩)
      have heq : r⁻¹ * ‖(ofLp (z (tau' ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
          - ((ofLp (z (tau' ω) ω)).2 - r) • pj j ω‖
          = r⁻¹ * ‖(ofLp (z (tau' ω) ω)).1 - (ofLp (z (smark j ω) ω)).1
            - ((ofLp (z (tau' ω) ω)).2 - (ofLp (z (smark j ω) ω)).2) • pj j ω‖ := by
        rw [hR']
      rw [heq] at hY'
      exact le_trans hY' h1
    have h2 := hmarkov _ _ K hB1meas hKpos hI1 hsupnn hAf
    have h3 := le_trans h2 htravbd
    have h4 : (0:ℝ) ≤ (μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
        ∩ {ω | K ≤ Yst (tau' ω) ω})).toReal := ENNReal.toReal_nonneg
    nlinarith only [h3, hKkey, h4, hKpos]
  -- the clamped affine function for the second cutoff
  obtain ⟨lf, hlfd⟩ : ∃ f : ℤ → ℝ, f = fun i : ℤ =>
      max 0 (min 1 (((i:ℝ) - (aa:ℝ)) / ((bb:ℝ) - (aa:ℝ)))) := ⟨_, rfl⟩
  have hlf0 : ∀ i : ℤ, 0 ≤ lf i := by
    intro i; simp only [hlfd]; exact le_max_left _ _
  have hlf1 : ∀ i : ℤ, lf i ≤ 1 := by
    intro i; simp only [hlfd]
    exact max_le (by norm_num) (min_le_left _ _)
  have hlfaff : ∀ i : ℤ, (aa:ℤ) ≤ i → i ≤ (bb:ℤ) →
      lf i = ((i:ℝ) - (aa:ℝ)) / ((bb:ℝ) - (aa:ℝ)) := by
    intro i h1 h2
    simp only [hlfd]
    have e1 : (aa:ℝ) ≤ (i:ℝ) := by exact_mod_cast h1
    have e2 : (i:ℝ) ≤ (bb:ℝ) := by exact_mod_cast h2
    have e3 : (0:ℝ) ≤ ((i:ℝ) - (aa:ℝ)) / ((bb:ℝ) - (aa:ℝ)) :=
      div_nonneg (by linarith only [e1]) haabbR.le
    have e4 : ((i:ℝ) - (aa:ℝ)) / ((bb:ℝ) - (aa:ℝ)) ≤ 1 := by
      rw [div_le_one haabbR]; linarith only [e2]
    rw [min_eq_right e4, max_eq_right e3]
  have hlfbb : ∀ i : ℤ, (bb:ℤ) ≤ i → lf i = 1 := by
    intro i h1
    simp only [hlfd]
    have e1 : (bb:ℝ) ≤ (i:ℝ) := by exact_mod_cast h1
    have e2 : (1:ℝ) ≤ ((i:ℝ) - (aa:ℝ)) / ((bb:ℝ) - (aa:ℝ)) := by
      rw [le_div_iff₀ haabbR]; linarith only [e1]
    rw [min_eq_left e2]
    norm_num
  have hlfpoi : ∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) →
      (lf (i + 1) + lf (i - 1)) / 2 - lf i ≤ -((fun _ : ℤ => (0:ℝ)) i) := by
    intro i h1 h2
    have hqne : ((bb:ℝ) - (aa:ℝ)) ≠ 0 := ne_of_gt haabbR
    have heq : (lf (i + 1) + lf (i - 1)) / 2 - lf i = 0 := by
      rw [hlfaff (i + 1) (by omega) (by omega), hlfaff (i - 1) (by omega) (by omega),
        hlfaff i (by omega) (by omega)]
      push_cast
      field_simp
      ring
    rw [heq]
    norm_num
  have hbb8cc : (bb:ℝ) = 8 * (cc:ℝ) := by
    rw [hbbd, hccd]; push_cast; ring
  have hSσcc : ∀ ω, (ofLp (z (smark j ω) ω)).2 = r → S (smark j ω) ω = (cc:ℤ) := by
    intro ω hR
    have h1 : ε * (S (smark j ω) ω : ℝ) = ε * (cc:ℝ) := by
      rw [← hlat (smark j ω) ω, hR, hεcc]
    have h2 : (S (smark j ω) ω : ℝ) = (cc:ℝ) := mul_left_cancel₀ (ne_of_gt hε0) h1
    exact_mod_cast h2
  have hB2 : (μ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
      ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2})).toReal ≤ 1 / 8 := by
    have hXτ'meas : Measurable (fun ω => (ofLp (z (tau' ω) ω)).2) :=
      hrandidx tau' htau'meas (fun n ω => (ofLp (z n ω)).2) (fun n => (hzt n).measurable)
    have hB2meas : MeasurableSet ({ω | (ofLp (z (smark j ω) ω)).2 = r}
        ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2}) :=
      hRjmeas.inter (hXτ'meas measurableSet_Ici)
    obtain ⟨indR, hindRd⟩ : ∃ f : Ω → ℝ,
        f = Set.indicator {ω | (ofLp (z (smark j ω) ω)).2 = r} (fun _ => (1:ℝ)) := ⟨_, rfl⟩
    have hindRmeas : Measurable indR := by
      rw [hindRd]; exact measurable_const.indicator hRjmeas
    have hindR01 : ∀ ω, 0 ≤ indR ω ∧ indR ω ≤ 1 := by
      intro ω
      rw [hindRd]
      by_cases hc : ω ∈ {ω | (ofLp (z (smark j ω) ω)).2 = r}
      · rw [Set.indicator_of_mem hc]; norm_num
      · rw [Set.indicator_of_notMem hc]; norm_num
    have hSτ'meas : Measurable (fun ω => lf (S (tau' ω) ω)) :=
      hrandidx tau' htau'meas (fun m ω => lf (S m ω)) (fun m => hgSmeas lf m)
    have hprodint : Integrable (fun ω => indR ω * lf (S (tau' ω) ω)) μ := by
      refine Integrable.mono' (integrable_const (1:ℝ))
        (hindRmeas.mul hSτ'meas).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      obtain ⟨e1, e2⟩ := hindR01 ω
      have e3 := hlf0 (S (tau' ω) ω)
      have e4 := hlf1 (S (tau' ω) ω)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith only [e1, e2, e3, e4]
    -- the conditional hitting bound
    have hcl := claimT lf (fun _ => 0) {ω | (ofLp (z (smark j ω) ω)).2 = r}
      (fun i => le_rfl) hlfpoi hRjmeas hRjG
    have hclean : ∀ (n : ℕ) (ω : Ω),
        Set.indicator {ω | (ofLp (z (smark j ω) ω)).2 = r} (fun _ => (1:ℝ)) ω
          * (lf (S (min (max (smark j ω) n) (tau' ω)) ω)
            + ∑ _m ∈ Finset.Ico (smark j ω) (min n (tau' ω)), (0:ℝ))
        = indR ω * lf (S (min (max (smark j ω) n) (tau' ω)) ω) := by
      intro n ω
      rw [hindRd, Finset.sum_const_zero, add_zero]
    have hRbd : ∫ ω, Set.indicator {ω | (ofLp (z (smark j ω) ω)).2 = r} (fun _ => (1:ℝ)) ω
        * lf (S (smark j ω) ω) ∂μ ≤ 1 / 8 := by
      have hptR : ∀ ω, Set.indicator {ω | (ofLp (z (smark j ω) ω)).2 = r} (fun _ => (1:ℝ)) ω
          * lf (S (smark j ω) ω) ≤ 1 / 8 := by
        intro ω
        by_cases hc : (ofLp (z (smark j ω) ω)).2 = r
        · have hmem : ω ∈ {ω | (ofLp (z (smark j ω) ω)).2 = r} := hc
          rw [Set.indicator_of_mem hmem, one_mul, hSσcc ω hc,
            hlfaff (cc:ℤ) (by exact_mod_cast haacc) (by
              have h1 : cc ≤ bb := by omega
              exact_mod_cast h1)]
          have h2 : (0:ℝ) ≤ (aa:ℝ) := haaR
          rw [div_le_div_iff₀ haabbR (by norm_num : (0:ℝ) < 8), hbb8cc]
          push_cast
          linarith only [h2]
        · have hnm : ω ∉ {ω | (ofLp (z (smark j ω) ω)).2 = r} := hc
          rw [Set.indicator_of_notMem hnm, zero_mul]
          norm_num
      have hintR : Integrable (fun ω =>
          Set.indicator {ω | (ofLp (z (smark j ω) ω)).2 = r} (fun _ => (1:ℝ)) ω
            * lf (S (smark j ω) ω)) μ := by
        refine Integrable.mono' (integrable_const (1:ℝ))
          ((measurable_const.indicator hRjmeas).mul
            (hrandidx (smark j) hσmeas (fun m ω => lf (S m ω))
              (fun m => hgSmeas lf m))).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        have e3 := hlf0 (S (smark j ω) ω)
        have e4 := hlf1 (S (smark j ω) ω)
        by_cases hc : ω ∈ {ω | (ofLp (z (smark j ω) ω)).2 = r}
        · rw [Set.indicator_of_mem hc, one_mul, Real.norm_eq_abs, abs_of_nonneg e3]
          exact e4
        · rw [Set.indicator_of_notMem hc, zero_mul, norm_zero]
          norm_num
      calc ∫ ω, Set.indicator {ω | (ofLp (z (smark j ω) ω)).2 = r} (fun _ => (1:ℝ)) ω
            * lf (S (smark j ω) ω) ∂μ
          ≤ ∫ _ω, (1/8 : ℝ) ∂μ := integral_mono hintR (integrable_const _) hptR
        _ = 1 / 8 := by rw [integral_const]; simp
    have hlim : ∫ ω, indR ω * lf (S (tau' ω) ω) ∂μ ≤ 1 / 8 := by
      have hFint : ∀ n : ℕ, Integrable (fun ω =>
          indR ω * lf (S (min (max (smark j ω) n) (tau' ω)) ω)) μ := by
        intro n
        have hm1 : Measurable (fun ω => lf (S (min (max (smark j ω) n) (tau' ω)) ω)) :=
          hrandidx2 (smark j) tau' hσmeas htau'meas
            (fun i m ω => lf (S (min (max i n) m) ω)) (fun i m => hgSmeas _ _)
        refine Integrable.mono' (integrable_const (1:ℝ))
          (hindRmeas.mul hm1).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        obtain ⟨e1, e2⟩ := hindR01 ω
        have e3 := hlf0 (S (min (max (smark j ω) n) (tau' ω)) ω)
        have e4 := hlf1 (S (min (max (smark j ω) n) (tau' ω)) ω)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith only [e1, e2, e3, e4]
      have hFbd : ∀ n : ℕ, ∫ ω, indR ω
          * lf (S (min (max (smark j ω) n) (tau' ω)) ω) ∂μ ≤ 1 / 8 := by
        intro n
        have h1 := hcl n
        rw [integral_congr_ae (Filter.Eventually.of_forall (hclean n))] at h1
        linarith only [h1, hRbd]
      refine le_of_tendsto (MeasureTheory.tendsto_integral_of_dominated_convergence
        (fun _ => (1:ℝ)) (fun n => (hFint n).aestronglyMeasurable) (integrable_const 1)
        (fun n => ?_) ?_) (Filter.Eventually.of_forall hFbd)
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        obtain ⟨e1, e2⟩ := hindR01 ω
        have e3 := hlf0 (S (min (max (smark j ω) n) (tau' ω)) ω)
        have e4 := hlf1 (S (min (max (smark j ω) n) (tau' ω)) ω)
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        nlinarith only [e1, e2, e3, e4]
      · refine Filter.Eventually.of_forall (fun ω => ?_)
        refine tendsto_atTop_of_eventually_const (i₀ := tau' ω) (fun n hn => ?_)
        have e1 : min (max (smark j ω) n) (tau' ω) = tau' ω := by
          have := hσtau' ω; omega
        rw [e1]
    have hptB2 : ∀ ω ∈ ({ω | (ofLp (z (smark j ω) ω)).2 = r}
        ∩ {ω | 8 * r ≤ (ofLp (z (tau' ω) ω)).2}), (1:ℝ) ≤ indR ω * lf (S (tau' ω) ω) := by
      intro ω hω
      obtain ⟨hR, hT⟩ := hω
      have hRm : ω ∈ {ω | (ofLp (z (smark j ω) ω)).2 = r} := hR
      have hT' : 8 * r ≤ (ofLp (z (tau' ω) ω)).2 := hT
      have h1 : (bb:ℤ) ≤ S (tau' ω) ω := by
        rw [hlat (tau' ω) ω, ← hεbb] at hT'
        have h2 : (bb:ℝ) ≤ (S (tau' ω) ω : ℝ) :=
          le_of_mul_le_mul_left (by linarith only [hT']) hε0
        exact_mod_cast h2
      rw [hindRd, Set.indicator_of_mem hRm, one_mul, hlfbb _ h1]
    have h3 := hmarkov _ _ 1 hB2meas one_pos hprodint
      (fun ω => by
        obtain ⟨e1, e2⟩ := hindR01 ω
        have e3 := hlf0 (S (tau' ω) ω)
        positivity) hptB2
    rw [mul_one] at h3
    linarith only [h3, hlim]
  exact ⟨hB1, hB2⟩
