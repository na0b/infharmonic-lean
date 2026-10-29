import InfHarmonic.Preamble
set_option maxHeartbeats 400000
open Set Filter Topology MeasureTheory

/-- Claim T' of Proposition 6.7: the conditional supersolution bound along a
stopped portion of the lattice time walk. If `hf` is a discrete supersolution on
the window `(aa, bb)` with nonnegative defect `uf`, then along the portion from
the mark time `σm` to the portion stopping time `tau'` the quantity
`hf (S ·) + ∑ uf (S ·)` is a supermartingale when weighted by the indicator of
an adapted event `A`, so its integral at any time `n` is at most its integral at
the mark time. -/
theorem StoppedLatticeSupersolutionBound {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (ξ : ℕ → Ω → ℝ) (Ξ : ℕ → Ω → ℤ) (S : ℕ → Ω → ℤ)
    (τ σm tau' : Ω → ℕ) (aa bb qq : ℕ)
    (hξpm : ∀ n ω, ξ n ω = 1 ∨ ξ n ω = -1)
    (hξmeas : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (ξ n))
    (hξcond : ∀ n, μ[ξ n | 𝒢 n] =ᵐ[μ] 0)
    (hΞd : Ξ = fun n ω => if ξ n ω = 1 then 1 else -1)
    (hSstep : ∀ n ω, S (n + 1) ω = S n ω + (if n < τ ω then Ξ n ω else 0))
    (hSrange : ∀ n ω, (aa : ℤ) ≤ S n ω ∧ S n ω ≤ (qq : ℤ))
    (hσst : IsStoppingTime 𝒢 (fun ω => (σm ω : ℕ∞))) (hσmeas : Measurable σm)
    (htau'st : IsStoppingTime 𝒢 (fun ω => (tau' ω : ℕ∞))) (htau'meas : Measurable tau')
    (hσtau' : ∀ ω, σm ω ≤ tau' ω) (htau'τ : ∀ ω, tau' ω ≤ τ ω)
    (hstG : ∀ (ζ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) →
      ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | ζ ω ≤ n})
    (hrandidx2 : ∀ (ζ η : Ω → ℕ), Measurable ζ → Measurable η →
      ∀ G : ℕ → ℕ → Ω → ℝ, (∀ n m, Measurable (G n m)) →
      Measurable (fun ω => G (ζ ω) (η ω) ω))
    (hbddg : ∀ g : ℤ → ℝ, ∃ C : ℝ, ∀ i : ℤ, (aa:ℤ) ≤ i → i ≤ (qq:ℤ) → |g i| ≤ C)
    (hgSmeasG : ∀ (g : ℤ → ℝ) (k n : ℕ), k ≤ n → Measurable[𝒢 n] (fun ω => g (S k ω)))
    (hgSmeas : ∀ (g : ℤ → ℝ) (k : ℕ), Measurable (fun ω => g (S k ω)))
    (hSwin : ∀ (n : ℕ) (ω : Ω), σm ω ≤ n → n < tau' ω →
      (aa:ℤ) < S n ω ∧ S n ω < (bb:ℤ)) :
    ∀ (hf uf : ℤ → ℝ) (A : Set Ω), (∀ i : ℤ, 0 ≤ uf i) →
    (∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) → (hf (i + 1) + hf (i - 1)) / 2 - hf i ≤ -(uf i)) →
    MeasurableSet A → (∀ n : ℕ, MeasurableSet[𝒢 n] (A ∩ {ω | σm ω ≤ n})) →
    ∀ n : ℕ,
      ∫ ω, Set.indicator A (fun _ => (1:ℝ)) ω *
          (hf (S (min (max (σm ω) n) (tau' ω)) ω)
            + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)) ∂μ
        ≤ ∫ ω, Set.indicator A (fun _ => (1:ℝ)) ω * hf (S (σm ω) ω) ∂μ := by
  intro hf uf A hu0 hpoi hAm hAG
  obtain ⟨Ch, hCh⟩ := hbddg hf
  obtain ⟨Ch1, hCh1⟩ := hbddg (fun i => hf (i + 1))
  obtain ⟨Ch2, hCh2⟩ := hbddg (fun i => hf (i - 1))
  obtain ⟨Cu, hCu⟩ := hbddg uf
  obtain ⟨ind, hindd⟩ : ∃ f : Ω → ℝ, f = Set.indicator A (fun _ => (1:ℝ)) := ⟨_, rfl⟩
  have hindmeas : Measurable ind := by
    rw [hindd]
    exact (measurable_const).indicator hAm
  have hindbd : ∀ ω, |ind ω| ≤ 1 := by
    intro ω
    rw [hindd]
    by_cases hc : ω ∈ A
    · rw [Set.indicator_of_mem hc]; norm_num
    · rw [Set.indicator_of_notMem hc]; norm_num
  -- the clipped indices are measurable
  have hidxmeas : ∀ n : ℕ, Measurable (fun ω => hf (S (min (max (σm ω) n) (tau' ω)) ω)) :=
    fun n => hrandidx2 (σm) tau' hσmeas htau'meas
      (fun i m ω => hf (S (min (max i n) m) ω)) (fun i m => hgSmeas _ _)
  have hsummeas : ∀ n : ℕ, Measurable (fun ω =>
      ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)) :=
    fun n => hrandidx2 (σm) tau' hσmeas htau'meas
      (fun i m ω => ∑ k ∈ Finset.Ico i (min n m), uf (S k ω))
      (fun i m => Finset.measurable_sum _ (fun k _ => hgSmeas uf k))
  have hidxbd : ∀ (n : ℕ) (ω : Ω), |hf (S (min (max (σm ω) n) (tau' ω)) ω)| ≤ Ch := by
    intro n ω
    obtain ⟨h1, h2⟩ := hSrange (min (max (σm ω) n) (tau' ω)) ω
    exact hCh _ h1 h2
  have hsumbd : ∀ (n : ℕ) (ω : Ω),
      |∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)| ≤ (n : ℝ) * |Cu| := by
    intro n ω
    have h1 : |∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)|
        ≤ ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), |uf (S m ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), |uf (S m ω)|
        ≤ ∑ _m ∈ Finset.Ico (σm ω) (min n (tau' ω)), |Cu| := by
      refine Finset.sum_le_sum (fun m _ => ?_)
      obtain ⟨e1, e2⟩ := hSrange m ω
      exact le_trans (hCu _ e1 e2) (le_abs_self Cu)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
    have h3 : ((min n (tau' ω) - σm ω : ℕ) : ℝ) ≤ (n:ℝ) := by
      have h4 : min n (tau' ω) - σm ω ≤ n := by omega
      exact_mod_cast h4
    have h5 : (0:ℝ) ≤ |Cu| := abs_nonneg Cu
    calc |∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)|
        ≤ ((min n (tau' ω) - σm ω : ℕ) : ℝ) * |Cu| := le_trans h1 h2
      _ ≤ (n : ℝ) * |Cu| := mul_le_mul_of_nonneg_right h3 h5
  have hYint : ∀ n : ℕ, Integrable (fun ω => ind ω *
      (hf (S (min (max (σm ω) n) (tau' ω)) ω)
        + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω))) μ := by
    intro n
    refine Integrable.mono' (integrable_const (|Ch| + (n:ℝ) * |Cu|))
      ((hindmeas.mul ((hidxmeas n).add (hsummeas n))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hidxbd n ω
    have h2 := hsumbd n ω
    have h3 := hindbd ω
    have h4 : (0:ℝ) ≤ |ind ω| := abs_nonneg _
    have h5 : |hf (S (min (max (σm ω) n) (tau' ω)) ω)
        + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)|
        ≤ |Ch| + (n:ℝ) * |Cu| := by
      refine le_trans (abs_add_le _ _) ?_
      have h6 : |hf (S (min (max (σm ω) n) (tau' ω)) ω)| ≤ |Ch| :=
        le_trans h1 (le_abs_self Ch)
      linarith only [h6, h2]
    have h7 : (0:ℝ) ≤ |Ch| + (n:ℝ) * |Cu| := by positivity
    calc |ind ω| * |hf (S (min (max (σm ω) n) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)|
        ≤ 1 * (|Ch| + (n:ℝ) * |Cu|) := by
          exact mul_le_mul h3 h5 (abs_nonneg _) (by norm_num)
      _ = |Ch| + (n:ℝ) * |Cu| := one_mul _
  -- the one-step difference
  have hdiff : ∀ (n : ℕ) (ω : Ω),
      (hf (S (min (max (σm ω) (n + 1)) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min (n + 1) (tau' ω)), uf (S m ω))
        - (hf (S (min (max (σm ω) n) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω))
      = (if (σm ω ≤ n ∧ n < tau' ω) then
          (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0)
        + (if (σm ω ≤ n ∧ n < tau' ω) then
          (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) * ξ n ω := by
    intro n ω
    by_cases hc : σm ω ≤ n ∧ n < tau' ω
    · obtain ⟨hc1, hc2⟩ := hc
      have he1 : min (max (σm ω) n) (tau' ω) = n := by omega
      have he2 : min (max (σm ω) (n + 1)) (tau' ω) = n + 1 := by omega
      have he3 : min n (tau' ω) = n := by omega
      have he4 : min (n + 1) (tau' ω) = n + 1 := by omega
      have hnτ : n < τ ω := lt_of_lt_of_le hc2 (htau'τ ω)
      rw [he1, he2, he3, he4, Finset.sum_Ico_succ_top hc1, if_pos ⟨hc1, hc2⟩,
        if_pos ⟨hc1, hc2⟩, hSstep n ω, if_pos hnτ]
      simp only [hΞd]
      rcases hξpm n ω with h1 | h1
      · simp only [h1]
        push_cast
        ring
      · have hne : ¬ (ξ n ω = 1) := by rw [h1]; norm_num
        rw [if_neg hne, h1, show S n ω + (-1 : ℤ) = S n ω - 1 by ring]
        ring
    · rw [if_neg hc, if_neg hc]
      have hor : n < σm ω ∨ tau' ω ≤ n := by omega
      rcases hor with h | h
      · have he1 : min (max (σm ω) n) (tau' ω) = σm ω := by
          have := hσtau' ω; omega
        have he2 : min (max (σm ω) (n + 1)) (tau' ω) = σm ω := by
          have := hσtau' ω; omega
        have he3 : Finset.Ico (σm ω) (min n (tau' ω)) = ∅ := by
          refine Finset.Ico_eq_empty ?_
          omega
        have he4 : Finset.Ico (σm ω) (min (n + 1) (tau' ω)) = ∅ := by
          refine Finset.Ico_eq_empty ?_
          omega
        rw [he1, he2, he3, he4]
        simp
      · have he1 : min (max (σm ω) n) (tau' ω) = tau' ω := by
          have := hσtau' ω; omega
        have he2 : min (max (σm ω) (n + 1)) (tau' ω) = tau' ω := by
          have := hσtau' ω; omega
        have he3 : min n (tau' ω) = tau' ω := by omega
        have he4 : min (n + 1) (tau' ω) = tau' ω := by omega
        rw [he1, he2, he3, he4]
        simp
  -- the martingale part integrates to zero
  have hzero : ∀ n : ℕ, ∫ ω, ind ω * ((if (σm ω ≤ n ∧ n < tau' ω) then
      (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) * ξ n ω) ∂μ = 0 := by
    intro n
    obtain ⟨En, hEnd⟩ : ∃ s : Set Ω,
        s = (A ∩ {ω | σm ω ≤ n}) ∩ {ω | n < tau' ω} := ⟨_, rfl⟩
    have hEnG : MeasurableSet[𝒢 n] En := by
      rw [hEnd]
      refine MeasurableSet.inter (hAG n) ?_
      have he : {ω | n < tau' ω} = {ω | tau' ω ≤ n}ᶜ := by
        ext ω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      rw [he]
      exact MeasurableSet.compl (hstG tau' htau'st n)
    obtain ⟨g, hgd⟩ : ∃ f : Ω → ℝ, f = Set.indicator En
        (fun ω => (hf (S n ω + 1) - hf (S n ω - 1)) / 2) := ⟨_, rfl⟩
    have hgval : ∀ ω, ind ω * (if (σm ω ≤ n ∧ n < tau' ω) then
        (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) = g ω := by
      intro ω
      rw [hgd]
      by_cases hc : ω ∈ En
      · have hc' := hc
        rw [hEnd] at hc'
        obtain ⟨⟨hA, h1⟩, h2⟩ := hc'
        rw [Set.indicator_of_mem hc, if_pos ⟨h1, h2⟩, hindd, Set.indicator_of_mem hA, one_mul]
      · rw [Set.indicator_of_notMem hc]
        by_cases hc2 : (σm ω ≤ n ∧ n < tau' ω)
        · have hnA : ω ∉ A := by
            intro hA
            rw [hEnd] at hc
            exact hc ⟨⟨hA, hc2.1⟩, hc2.2⟩
          rw [hindd, Set.indicator_of_notMem hnA, zero_mul]
        · rw [if_neg hc2, mul_zero]
    have hgmeasG : StronglyMeasurable[𝒢 n] g := by
      rw [hgd]
      refine StronglyMeasurable.indicator ?_ hEnG
      exact Measurable.stronglyMeasurable
        (((hgSmeasG (fun i => hf (i + 1)) n n le_rfl).sub
          (hgSmeasG (fun i => hf (i - 1)) n n le_rfl)).div_const 2)
    have hgbd : ∀ ω, ‖g ω‖ ≤ (|Ch1| + |Ch2|) / 2 := by
      intro ω
      rw [hgd]
      obtain ⟨e1, e2⟩ := hSrange n ω
      have h1 : |hf (S n ω + 1)| ≤ |Ch1| := le_trans (hCh1 _ e1 e2) (le_abs_self Ch1)
      have h2 : |hf (S n ω - 1)| ≤ |Ch2| := le_trans (hCh2 _ e1 e2) (le_abs_self Ch2)
      by_cases hc : ω ∈ En
      · rw [Set.indicator_of_mem hc, Real.norm_eq_abs, abs_div, abs_two]
        rw [div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
        calc |hf (S n ω + 1) - hf (S n ω - 1)| ≤ |hf (S n ω + 1)| + |hf (S n ω - 1)| :=
              abs_sub _ _
          _ ≤ |Ch1| + |Ch2| := by linarith only [h1, h2]
      · rw [Set.indicator_of_notMem hc, norm_zero]
        have h3 : (0:ℝ) ≤ |Ch1| := abs_nonneg _
        have h4 : (0:ℝ) ≤ |Ch2| := abs_nonneg _
        linarith only [h3, h4]
    have hξint : Integrable (ξ n) μ := by
      refine Integrable.mono' (integrable_const (1:ℝ))
        (((hξmeas n).mono (𝒢.le (n + 1))).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => ?_))
      rcases hξpm n ω with h1 | h1 <;> rw [h1] <;> norm_num
    have hpull := condExp_stronglyMeasurable_mul_of_bound (𝒢.le n) hgmeasG hξint
      ((|Ch1| + |Ch2|) / 2) (Filter.Eventually.of_forall hgbd)
    have hz : μ[(g * ξ n : Ω → ℝ) | 𝒢 n] =ᵐ[μ] 0 := by
      filter_upwards [hpull, hξcond n] with ω h1 h2
      rw [h1]
      simp only [Pi.mul_apply, h2, Pi.zero_apply, mul_zero]
    have hfin : ∫ ω, (g * ξ n : Ω → ℝ) ω ∂μ = 0 := by
      rw [← integral_condExp (𝒢.le n) (f := (g * ξ n : Ω → ℝ)), integral_congr_ae hz]
      simp
    have hcongr : ∀ ω, ind ω * ((if (σm ω ≤ n ∧ n < tau' ω) then
        (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) * ξ n ω)
        = (g * ξ n : Ω → ℝ) ω := by
      intro ω
      simp only [Pi.mul_apply]
      rw [← hgval ω]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hcongr)]
    exact hfin
  -- the integrals decrease along the portion
  have hmono : ∀ n : ℕ, ∫ ω, ind ω *
        (hf (S (min (max (σm ω) (n + 1)) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min (n + 1) (tau' ω)), uf (S m ω)) ∂μ
      ≤ ∫ ω, ind ω * (hf (S (min (max (σm ω) n) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)) ∂μ := by
    intro n
    have hAint : Integrable (fun ω => ind ω * (if (σm ω ≤ n ∧ n < tau' ω) then
        (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0)) μ := by
      have hsetm : MeasurableSet {ω | σm ω ≤ n ∧ n < tau' ω} := by
        have he : {ω | σm ω ≤ n ∧ n < tau' ω}
            = {ω | σm ω ≤ n} ∩ {ω | tau' ω ≤ n}ᶜ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
        rw [he]
        exact ((𝒢.le n) _ (hstG (σm) hσst n)).inter
          (((𝒢.le n) _ (hstG tau' htau'st n)).compl)
      have hmeasA : Measurable (fun ω => ind ω * (if (σm ω ≤ n ∧ n < tau' ω) then
          (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0)) := by
        refine hindmeas.mul (Measurable.ite hsetm ?_ measurable_const)
        exact ((((hgSmeas (fun i => hf (i + 1)) n).add
          (hgSmeas (fun i => hf (i - 1)) n)).div_const 2).sub (hgSmeas hf n)).add
            (hgSmeas uf n)
      refine Integrable.mono' (integrable_const ((|Ch1| + |Ch2|) / 2 + |Ch| + |Cu|))
        hmeasA.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
      obtain ⟨e1, e2⟩ := hSrange n ω
      have h1 : |hf (S n ω + 1)| ≤ |Ch1| := le_trans (hCh1 _ e1 e2) (le_abs_self Ch1)
      have h2 : |hf (S n ω - 1)| ≤ |Ch2| := le_trans (hCh2 _ e1 e2) (le_abs_self Ch2)
      have h3 : |hf (S n ω)| ≤ |Ch| := le_trans (hCh _ e1 e2) (le_abs_self Ch)
      have h4 : |uf (S n ω)| ≤ |Cu| := le_trans (hCu _ e1 e2) (le_abs_self Cu)
      have h5 := hindbd ω
      have h6 : (0:ℝ) ≤ (|Ch1| + |Ch2|) / 2 + |Ch| + |Cu| := by positivity
      rw [Real.norm_eq_abs, abs_mul]
      have h7 : |(if (σm ω ≤ n ∧ n < tau' ω) then
          (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0)|
          ≤ (|Ch1| + |Ch2|) / 2 + |Ch| + |Cu| := by
        by_cases hc : (σm ω ≤ n ∧ n < tau' ω)
        · rw [if_pos hc]
          have e3 := abs_le.mp h1
          have e4 := abs_le.mp h2
          have e5 := abs_le.mp h3
          have e6 := abs_le.mp h4
          rw [abs_le]
          constructor <;>
            linarith only [e3.1, e3.2, e4.1, e4.2, e5.1, e5.2, e6.1, e6.2]
        · rw [if_neg hc, abs_zero]
          exact h6
      calc |ind ω| * |(if (σm ω ≤ n ∧ n < tau' ω) then
            (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0)|
          ≤ 1 * ((|Ch1| + |Ch2|) / 2 + |Ch| + |Cu|) :=
            mul_le_mul h5 h7 (abs_nonneg _) (by norm_num)
        _ = (|Ch1| + |Ch2|) / 2 + |Ch| + |Cu| := one_mul _
    have hBint : Integrable (fun ω => ind ω * ((if (σm ω ≤ n ∧ n < tau' ω) then
        (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) * ξ n ω)) μ := by
      have hsetm : MeasurableSet {ω | σm ω ≤ n ∧ n < tau' ω} := by
        have he : {ω | σm ω ≤ n ∧ n < tau' ω}
            = {ω | σm ω ≤ n} ∩ {ω | tau' ω ≤ n}ᶜ := by
          ext ω
          simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_le]
        rw [he]
        exact ((𝒢.le n) _ (hstG (σm) hσst n)).inter
          (((𝒢.le n) _ (hstG tau' htau'st n)).compl)
      have hmeasB : Measurable (fun ω => ind ω * ((if (σm ω ≤ n ∧ n < tau' ω) then
          (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) * ξ n ω)) := by
        refine hindmeas.mul (Measurable.mul ?_ ?_)
        · refine Measurable.ite hsetm ?_ measurable_const
          exact ((hgSmeas (fun i => hf (i + 1)) n).sub
            (hgSmeas (fun i => hf (i - 1)) n)).div_const 2
        · exact ((hξmeas n).mono (𝒢.le (n + 1))).measurable
      refine Integrable.mono' (integrable_const ((|Ch1| + |Ch2|) / 2))
        hmeasB.aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
      obtain ⟨e1, e2⟩ := hSrange n ω
      have h1 : |hf (S n ω + 1)| ≤ |Ch1| := le_trans (hCh1 _ e1 e2) (le_abs_self Ch1)
      have h2 : |hf (S n ω - 1)| ≤ |Ch2| := le_trans (hCh2 _ e1 e2) (le_abs_self Ch2)
      have h5 := hindbd ω
      have h8 : |ξ n ω| = 1 := by
        rcases hξpm n ω with h | h <;> rw [h] <;> norm_num
      have h6 : (0:ℝ) ≤ (|Ch1| + |Ch2|) / 2 := by positivity
      rw [Real.norm_eq_abs, abs_mul, abs_mul, h8, mul_one]
      have h7 : |(if (σm ω ≤ n ∧ n < tau' ω) then
          (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0)| ≤ (|Ch1| + |Ch2|) / 2 := by
        by_cases hc : (σm ω ≤ n ∧ n < tau' ω)
        · rw [if_pos hc, abs_div, abs_two,
            div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 2)]
          calc |hf (S n ω + 1) - hf (S n ω - 1)| ≤ |hf (S n ω + 1)| + |hf (S n ω - 1)| :=
                abs_sub _ _
            _ ≤ |Ch1| + |Ch2| := by linarith only [h1, h2]
        · rw [if_neg hc, abs_zero]
          exact h6
      calc |ind ω| * |(if (σm ω ≤ n ∧ n < tau' ω) then
            (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0)|
          ≤ 1 * ((|Ch1| + |Ch2|) / 2) := mul_le_mul h5 h7 (abs_nonneg _) (by norm_num)
        _ = (|Ch1| + |Ch2|) / 2 := one_mul _
    have hApt : ∀ ω, ind ω * (if (σm ω ≤ n ∧ n < tau' ω) then
        (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0) ≤ 0 := by
      intro ω
      have hind0 : (0:ℝ) ≤ ind ω := by
        rw [hindd]
        by_cases hc : ω ∈ A
        · rw [Set.indicator_of_mem hc]; norm_num
        · rw [Set.indicator_of_notMem hc]
      by_cases hc : (σm ω ≤ n ∧ n < tau' ω)
      · rw [if_pos hc]
        obtain ⟨h1, h2⟩ := hSwin n ω hc.1 hc.2
        have h3 := hpoi (S n ω) h1 h2
        have h4 : (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) ≤ 0 := by
          linarith only [h3]
        exact mul_nonpos_of_nonneg_of_nonpos hind0 h4
      · rw [if_neg hc, mul_zero]
    have hdiffint : ∫ ω, (ind ω *
          (hf (S (min (max (σm ω) (n + 1)) (tau' ω)) ω)
            + ∑ m ∈ Finset.Ico (σm ω) (min (n + 1) (tau' ω)), uf (S m ω))
        - ind ω * (hf (S (min (max (σm ω) n) (tau' ω)) ω)
            + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω))) ∂μ ≤ 0 := by
      have he : ∀ ω, ind ω *
            (hf (S (min (max (σm ω) (n + 1)) (tau' ω)) ω)
              + ∑ m ∈ Finset.Ico (σm ω) (min (n + 1) (tau' ω)), uf (S m ω))
          - ind ω * (hf (S (min (max (σm ω) n) (tau' ω)) ω)
              + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω))
          = ind ω * (if (σm ω ≤ n ∧ n < tau' ω) then
              (hf (S n ω + 1) + hf (S n ω - 1)) / 2 - hf (S n ω) + uf (S n ω) else 0)
            + ind ω * ((if (σm ω ≤ n ∧ n < tau' ω) then
              (hf (S n ω + 1) - hf (S n ω - 1)) / 2 else 0) * ξ n ω) := by
        intro ω
        rw [← mul_add, ← hdiff n ω]
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall he), integral_add hAint hBint,
        hzero n, add_zero]
      exact integral_nonpos (fun ω => hApt ω)
    rw [integral_sub (hYint (n + 1)) (hYint n)] at hdiffint
    linarith only [hdiffint]
  have hY0 : ∫ ω, ind ω * (hf (S (min (max (σm ω) 0) (tau' ω)) ω)
      + ∑ m ∈ Finset.Ico (σm ω) (min 0 (tau' ω)), uf (S m ω)) ∂μ
      = ∫ ω, ind ω * hf (S (σm ω) ω) ∂μ := by
    refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
    have h1 : min (max (σm ω) 0) (tau' ω) = σm ω := by
      have := hσtau' ω; omega
    have h2 : Finset.Ico (σm ω) (min 0 (tau' ω)) = ∅ := by
      refine Finset.Ico_eq_empty ?_
      omega
    simp only [h1, h2, Finset.sum_empty, add_zero]
  intro n
  rw [← hindd]
  induction n with
  | zero => exact le_of_eq hY0
  | succ n ih => exact le_trans (hmono n) ih
