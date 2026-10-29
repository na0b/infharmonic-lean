import InfHarmonic.Preamble
open MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Doob's `L²` maximal inequality in the vector-valued form used at paper
(6.26): for an `F`-valued square-integrable martingale the expected supremum of
the norms of the first `N + 1` terms is at most `2 (E‖M N‖²)^{1/2}`, and the
second moment splits orthogonally over the increments. -/
theorem DoobL2Maximal {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (M : ℕ → Ω → F) (hM : Martingale M 𝒢 μ)
    (hsq : ∀ n, Integrable (fun ω => ‖M n ω‖ ^ 2) μ) (N : ℕ) :
    Integrable (fun ω => (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => ‖M k ω‖) μ ∧
    ∫ ω, ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
        fun k => ‖M k ω‖) ∂μ ≤ 2 * Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ) ∧
    ∫ ω, ‖M N ω‖ ^ 2 ∂μ
      = ∫ ω, ‖M 0 ω‖ ^ 2 ∂μ
        + ∑ k ∈ Finset.range N, ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ := by
  -- Step 5: orthogonality of the increments, which gives the third conclusion.
  have horth : ∫ ω, ‖M N ω‖ ^ 2 ∂μ
      = ∫ ω, ‖M 0 ω‖ ^ 2 ∂μ
        + ∑ k ∈ Finset.range N, ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ := by
    -- increments are integrable
    have hdint : ∀ k, Integrable (fun ω => M (k + 1) ω - M k ω) μ := fun k =>
      (hM.integrable (k + 1)).sub (hM.integrable k)
    -- squared increments are integrable
    have hd2 : ∀ k, Integrable (fun ω => ‖M (k + 1) ω - M k ω‖ ^ 2) μ := by
      intro k
      refine Integrable.mono' (g := fun ω => 2 * ‖M (k + 1) ω‖ ^ 2 + 2 * ‖M k ω‖ ^ 2)
        (((hsq (k + 1)).const_mul 2).add ((hsq k).const_mul 2))
        ((hdint k).aestronglyMeasurable.norm.pow 2) ?_
      filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have h1 := norm_sub_sq_real (M (k + 1) ω) (M k ω)
      have h2 := abs_le.mp (abs_real_inner_le_norm (M (k + 1) ω) (M k ω))
      have h3 := sq_nonneg (‖M (k + 1) ω‖ - ‖M k ω‖)
      nlinarith [h1, h2.1, h2.2, h3]
    -- the cross term is integrable
    have hcrossint : ∀ k, Integrable (fun ω => (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ)) μ := by
      intro k
      refine Integrable.mono' (g := fun ω => ‖M k ω‖ ^ 2 / 2 + ‖M (k + 1) ω - M k ω‖ ^ 2 / 2)
        (((hsq k).div_const 2).add ((hd2 k).div_const 2))
        (((hM.integrable k).aestronglyMeasurable.inner (hdint k).aestronglyMeasurable)) ?_
      filter_upwards with ω
      have h := abs_real_inner_le_norm (M k ω) (M (k + 1) ω - M k ω)
      rw [Real.norm_eq_abs]
      nlinarith [sq_nonneg (‖M k ω‖ - ‖M (k+1) ω - M k ω‖), norm_nonneg (M k ω),
        norm_nonneg (M (k+1) ω - M k ω)]
    -- conditional expectation of the increment vanishes
    have hdcond : ∀ k, μ[fun ω => M (k + 1) ω - M k ω | 𝒢 k] =ᵐ[μ] 0 := by
      intro k
      have h1 : μ[fun ω => M (k + 1) ω - M k ω | 𝒢 k]
          =ᵐ[μ] μ[M (k + 1) | 𝒢 k] - μ[M k | 𝒢 k] :=
        condExp_sub (hM.integrable (k + 1)) (hM.integrable k) _
      have h2 : μ[M k | 𝒢 k] = M k :=
        condExp_of_stronglyMeasurable (𝒢.le k) (hM.stronglyMeasurable k) (hM.integrable k)
      filter_upwards [h1, hM.2 k (k + 1) (by omega)] with ω e1 e2
      simp only [h2, Pi.sub_apply, e1, e2, sub_self, Pi.zero_apply]
    -- the cross term has zero mean
    have hcross : ∀ k, ∫ ω, (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ) ∂μ = 0 := by
      intro k
      have hpull : μ[fun ω => (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ) | 𝒢 k]
          =ᵐ[μ] fun ω =>
            (inner ℝ (M k ω) ((μ[fun ω => M (k + 1) ω - M k ω | 𝒢 k]) ω) : ℝ) :=
        condExp_bilin_of_stronglyMeasurable_left (innerSL ℝ)
          (hM.stronglyMeasurable k) (hcrossint k) (hdint k)
      have hz : μ[fun ω => (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ) | 𝒢 k] =ᵐ[μ] 0 := by
        filter_upwards [hpull, hdcond k] with ω h1 h2
        rw [h1, h2]
        simp
      calc ∫ ω, (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ) ∂μ
          = ∫ ω, (μ[fun ω => (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ) | 𝒢 k]) ω ∂μ :=
            (integral_condExp (𝒢.le k)).symm
        _ = 0 := by rw [integral_congr_ae hz]; simp
    -- one step of the telescoping identity
    have hstep : ∀ k, ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ
        = ∫ ω, ‖M k ω‖ ^ 2 ∂μ + ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ := by
      intro k
      have hpt : ∀ ω, ‖M (k + 1) ω‖ ^ 2
          = ‖M k ω‖ ^ 2 + 2 * (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ)
            + ‖M (k + 1) ω - M k ω‖ ^ 2 := by
        intro ω
        have e : M k ω + (M (k + 1) ω - M k ω) = M (k + 1) ω := by abel
        have h := norm_add_sq_real (M k ω) (M (k + 1) ω - M k ω)
        rw [e] at h
        exact h
      calc ∫ ω, ‖M (k + 1) ω‖ ^ 2 ∂μ
          = ∫ ω, (‖M k ω‖ ^ 2 + 2 * (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ)
              + ‖M (k + 1) ω - M k ω‖ ^ 2) ∂μ := by
            exact integral_congr_ae (Filter.Eventually.of_forall hpt)
        _ = (∫ ω, (‖M k ω‖ ^ 2 + 2 * (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ)) ∂μ)
            + ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ :=
            integral_add ((hsq k).add ((hcrossint k).const_mul 2)) (hd2 k)
        _ = (∫ ω, ‖M k ω‖ ^ 2 ∂μ
              + ∫ ω, 2 * (inner ℝ (M k ω) (M (k + 1) ω - M k ω) : ℝ) ∂μ)
            + ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ := by
            rw [integral_add (hsq k) ((hcrossint k).const_mul 2)]
        _ = ∫ ω, ‖M k ω‖ ^ 2 ∂μ + ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ := by
            rw [integral_const_mul, hcross k]; ring
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ← ih, hstep n]
  have hCnn : (0:ℝ) ≤ ∫ ω, ‖M N ω‖ ^ 2 ∂μ := integral_nonneg fun ω => by positivity
  -- Step 1: `‖M·‖²` is a nonnegative submartingale.
  have hpow : ∀ x : F, ‖x‖ ^ (2:ℝ) = ‖x‖ ^ 2 := fun x => by
    rw [show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hnn : (0 : ℕ → Ω → ℝ) ≤ fun n ω => ‖M n ω‖ ^ 2 := fun n ω => by positivity
  have hsub : Submartingale (fun n ω => ‖M n ω‖ ^ 2) 𝒢 μ := by
    refine ⟨fun n => ((hM.stronglyMeasurable n).norm.pow 2), fun i j hij => ?_, hsq⟩
    have hrp : Integrable (fun ω => ‖M j ω‖ ^ (2:ℝ)) μ := by simpa only [hpow] using hsq j
    have hJ := Integrable.norm_condExp_rpow_le (m := 𝒢 i) (f := M j)
      (by norm_num : (1:ℝ) ≤ 2) hrp
    simp only [hpow] at hJ
    filter_upwards [hJ, hM.2 i j hij] with ω h1 h3
    rw [← h3]
    exact h1
  -- the running maximum: measurability, nonnegativity, integrability
  have hSmeas : Measurable fun ω => (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M k ω‖ :=
    Finset.measurable_range_sup''
      (fun k _ => (((hM.stronglyMeasurable k).mono (𝒢.le k)).norm).measurable)
  have hSnn : ∀ ω, (0:ℝ) ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M k ω‖ := by
    intro ω
    exact le_trans (norm_nonneg (M 0 ω))
      (Finset.le_sup' (fun k => ‖M k ω‖) (Finset.mem_range.mpr (Nat.succ_pos N)))
  have hSint : Integrable (fun ω => (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M k ω‖) μ := by
    refine Integrable.mono' (g := fun ω => ∑ k ∈ Finset.range (N + 1), ‖M k ω‖)
      (integrable_finsetSum _ (fun k _ => (hM.integrable k).norm))
      hSmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hSnn ω)]
    exact Finset.sup'_le _ _ (fun k hk =>
      Finset.single_le_sum (f := fun i => ‖M i ω‖) (fun i _ => norm_nonneg _) hk)
  -- Step 2: the weak-type bound.
  have hweak : ∀ l : ℝ, 0 < l →
      μ {ω | l ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => ‖M k ω‖}
        ≤ ENNReal.ofReal ((∫ ω, ‖M N ω‖ ^ 2 ∂μ) / l ^ 2) := by
    intro l hl
    have hl2 : (0:ℝ) < l ^ 2 := by positivity
    have hcoe : (((l ^ 2).toNNReal : NNReal) : ℝ) = l ^ 2 := Real.coe_toNNReal _ hl2.le
    have hset : {ω | l ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => ‖M k ω‖}
        = {ω | (((l ^ 2).toNNReal : NNReal) : ℝ)
            ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
              fun k => ‖M k ω‖ ^ 2} := by
      rw [hcoe]
      ext ω
      simp only [Set.mem_ofPred_eq, Finset.le_sup'_iff]
      constructor
      · rintro ⟨b, hb, hle⟩
        exact ⟨b, hb, by nlinarith [norm_nonneg (M b ω)]⟩
      · rintro ⟨b, hb, hle⟩
        exact ⟨b, hb, by nlinarith [norm_nonneg (M b ω)]⟩
    rw [hset]
    have hmax := MeasureTheory.maximal_ineq hsub hnn (ε := (l ^ 2).toNNReal) N
    have hle2 := setIntegral_le_integral (s := {ω | (((l ^ 2).toNNReal : NNReal) : ℝ)
        ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => ‖M k ω‖ ^ 2}) (hsq N)
      (Filter.Eventually.of_forall fun ω => by positivity)
    have hstep := le_trans hmax (ENNReal.ofReal_le_ofReal hle2)
    rw [ENNReal.ofReal_div_of_pos hl2,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hl2.ne'))
        (Or.inl ENNReal.ofReal_ne_top), mul_comm]
    exact hstep
  -- Step 3: the tail of the layer-cake integral.
  have htail : ∀ C a : ℝ, 0 ≤ C → 0 < a →
      ∫⁻ t in Set.Ioi a, ENNReal.ofReal (C / t ^ 2) ≤ ENNReal.ofReal (C / a) := by
    intro C a hC ha
    have hmeas : Measurable fun t : ℝ => ENNReal.ofReal (C / t ^ 2) := by fun_prop
    have hcnn : ∀ t : ℝ, 0 ≤ C / t ^ 2 := fun t => by positivity
    have hne : ∀ b : ℝ, a ≤ b → ∀ x ∈ Set.uIcc a b, x ≠ 0 := by
      intro b hab x hx
      rw [Set.uIcc_of_le hab] at hx
      exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    have hcontint : ∀ b : ℝ, a ≤ b →
        IntervalIntegrable (fun t : ℝ => C / t ^ 2) volume a b := by
      intro b hab
      apply ContinuousOn.intervalIntegrable
      exact ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
        (fun x hx => pow_ne_zero 2 (hne b hab x hx))
    have hvalue : ∀ b : ℝ, a ≤ b → ∫ t in Set.Ioc a b, C / t ^ 2 = C / a - C / b := by
      intro b hab
      have hderiv : ∀ x ∈ Set.uIcc a b,
          HasDerivAt (fun t : ℝ => -C * t⁻¹) (C / x ^ 2) x := by
        intro x hx
        have he : C / x ^ 2 = -C * -(x ^ 2)⁻¹ := by rw [div_eq_mul_inv]; ring
        rw [he]
        exact HasDerivAt.const_mul (-C) (hasDerivAt_inv (hne b hab x hx))
      have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcontint b hab)
      rw [intervalIntegral.integral_of_le hab] at h
      rw [h]; field_simp; ring
    have hpiece : ∀ n : ℕ, ∫⁻ t in Set.Ioc a (a + n), ENNReal.ofReal (C / t ^ 2)
        ≤ ENNReal.ofReal (C / a) := by
      intro n
      have hab : a ≤ a + (n : ℝ) := by
        have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        linarith
      have hint : IntegrableOn (fun t : ℝ => C / t ^ 2) (Set.Ioc a (a + (n : ℝ))) := by
        have h2 := hcontint (a + (n : ℝ)) hab
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab] at h2
        exact h2
      rw [← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun t => hcnn t)), hvalue _ hab]
      exact ENNReal.ofReal_le_ofReal (by
        have : 0 ≤ C / (a + (n : ℝ)) := by positivity
        linarith)
    have hcover : ∀ t : ℝ, t ∈ Set.Ioi a → ∃ n : ℕ, t ∈ Set.Ioc a (a + (n : ℝ)) := by
      intro t ht
      obtain ⟨n, hn⟩ := exists_nat_ge (t - a)
      exact ⟨n, ⟨ht, by linarith⟩⟩
    have hmono : Monotone fun n : ℕ => (Set.Ioc a (a + (n : ℝ))).indicator
        fun t : ℝ => ENNReal.ofReal (C / t ^ 2) := by
      intro n m hnm
      have hle : a + (n : ℝ) ≤ a + (m : ℝ) := by
        have : (n : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hnm
        linarith
      exact Set.indicator_le_indicator_of_subset (Set.Ioc_subset_Ioc_right hle)
        (fun _ => by positivity)
    have heq : (Set.Ioi a).indicator (fun t : ℝ => ENNReal.ofReal (C / t ^ 2))
        = fun t => ⨆ n : ℕ, (Set.Ioc a (a + (n : ℝ))).indicator
            (fun t : ℝ => ENNReal.ofReal (C / t ^ 2)) t := by
      funext t
      by_cases ht : t ∈ Set.Ioi a
      · rw [Set.indicator_of_mem ht]
        obtain ⟨n, hn⟩ := hcover t ht
        refine le_antisymm (le_iSup_of_le n (by rw [Set.indicator_of_mem hn]))
          (iSup_le fun m => ?_)
        exact Set.indicator_apply_le fun _ => le_rfl
      · rw [Set.indicator_of_notMem ht]
        symm
        refine le_antisymm (iSup_le fun m => ?_) (by positivity)
        rw [Set.indicator_of_notMem (fun hm => ht hm.1)]
    calc ∫⁻ t in Set.Ioi a, ENNReal.ofReal (C / t ^ 2)
        = ∫⁻ t, (Set.Ioi a).indicator (fun t : ℝ => ENNReal.ofReal (C / t ^ 2)) t :=
          (lintegral_indicator measurableSet_Ioi _).symm
      _ = ⨆ n : ℕ, ∫⁻ t in Set.Ioc a (a + (n : ℝ)), ENNReal.ofReal (C / t ^ 2) := by
          rw [heq, lintegral_iSup (fun n => hmeas.indicator measurableSet_Ioc) hmono]
          simp_rw [lintegral_indicator measurableSet_Ioc]
      _ ≤ ENNReal.ofReal (C / a) := iSup_le hpiece
  -- Step 3 continued: the two-parameter bound.
  have hbound : ∀ a : ℝ, 0 < a →
      ∫ ω, ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => ‖M k ω‖) ∂μ ≤ a + (∫ ω, ‖M N ω‖ ^ 2 ∂μ) / a := by
    intro a ha
    have hlc := lintegral_eq_lintegral_meas_le μ
      (Filter.Eventually.of_forall hSnn) hSmeas.aemeasurable
    have hsplit : ∫⁻ t in Set.Ioi (0:ℝ),
          μ {ω | t ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
            fun k => ‖M k ω‖}
        = (∫⁻ t in Set.Ioc (0:ℝ) a,
            μ {ω | t ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
              fun k => ‖M k ω‖})
          + ∫⁻ t in Set.Ioi a,
            μ {ω | t ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
              fun k => ‖M k ω‖} := by
      rw [← lintegral_union measurableSet_Ioi Set.Ioc_disjoint_Ioi_same,
        Set.Ioc_union_Ioi_eq_Ioi ha.le]
    have h1 : (∫⁻ t in Set.Ioc (0:ℝ) a,
        μ {ω | t ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => ‖M k ω‖}) ≤ ENNReal.ofReal a := by
      calc _ ≤ ∫⁻ _ in Set.Ioc (0:ℝ) a, (1 : ENNReal) :=
            lintegral_mono (fun t => prob_le_one)
        _ = volume (Set.Ioc (0:ℝ) a) := setLIntegral_one _
        _ = ENNReal.ofReal a := by rw [Real.volume_Ioc, sub_zero]
    have h2 : (∫⁻ t in Set.Ioi a,
        μ {ω | t ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
          fun k => ‖M k ω‖}) ≤ ENNReal.ofReal ((∫ ω, ‖M N ω‖ ^ 2 ∂μ) / a) := by
      refine le_trans (lintegral_mono_ae ?_) (htail _ a hCnn ha)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact hweak t (lt_trans ha ht)
    have hfin : ENNReal.ofReal (∫ ω, ((Finset.range (N + 1)).sup'
        Finset.nonempty_range_add_one fun k => ‖M k ω‖) ∂μ)
        ≤ ENNReal.ofReal (a + (∫ ω, ‖M N ω‖ ^ 2 ∂μ) / a) := by
      rw [ofReal_integral_eq_lintegral_ofReal hSint
        (Filter.Eventually.of_forall hSnn), hlc, hsplit,
        ENNReal.ofReal_add ha.le (by positivity)]
      exact add_le_add h1 h2
    rwa [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hfin
  -- Step 4: the optimal choice of `a`.
  have hL2 : ∫ ω, ((Finset.range (N + 1)).sup' Finset.nonempty_range_add_one
      fun k => ‖M k ω‖) ∂μ ≤ 2 * Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ) := by
    rcases eq_or_lt_of_le hCnn with hC0 | hCpos
    · rw [← hC0, Real.sqrt_zero, mul_zero]
      refine le_of_forall_pos_le_add fun ε hε => ?_
      have h := hbound ε hε
      rw [← hC0] at h
      simpa using h
    · have hsp : 0 < Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ) := Real.sqrt_pos.mpr hCpos
      have hss : Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ) * Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ)
          = ∫ ω, ‖M N ω‖ ^ 2 ∂μ := Real.mul_self_sqrt hCnn
      have h := hbound _ hsp
      have hdiv : (∫ ω, ‖M N ω‖ ^ 2 ∂μ) / Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ)
          = Real.sqrt (∫ ω, ‖M N ω‖ ^ 2 ∂μ) := by
        field_simp
        linarith [hss]
      rw [hdiv] at h
      linarith
  exact ⟨hSint, hL2, horth⟩
