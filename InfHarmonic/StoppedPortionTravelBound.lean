module

public import InfHarmonic.DoobL2Maximal
public import InfHarmonic.IntegralSqrtProductCauchySchwarz

@[expose] public section
set_option maxHeartbeats 600000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The travel inequality (6.22) of Proposition 6.7 in the generality used by
the stopped-walk argument: between two stopping times `ρ ≤ σ ≤ τ` of a stopped
contact walk, the expected supremum of the displacement from the start of the
portion, measured in the sheared frame of slope `p` and scale `r`, is bounded by
the velocity-defect term plus the geometric-mean term. All five components --- the
four integrabilities and the inequality --- are asserted. -/
theorem StoppedPortionTravelBound {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0) (hΩ : Nonempty Ω)
    (ε : ℝ) (hε0 : 0 < ε) (ξ : ℕ → Ω → ℝ)
    (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ)
    (hξpm : ∀ n ω, ξ n ω = 1 ∨ ξ n ω = -1)
    (hξmeas : ∀ n, StronglyMeasurable[𝒢 (n + 1)] (ξ n))
    (hξcond : ∀ n, μ[ξ n | 𝒢 n] =ᵐ[μ] 0)
    (hzmeas : ∀ n, StronglyMeasurable[𝒢 n] (z n))
    (hzpmeas : ∀ n, StronglyMeasurable[𝒢 n] (zp n))
    (hzmmeas : ∀ n, StronglyMeasurable[𝒢 n] (zm n))
    (hQmeas : ∀ n, StronglyMeasurable[𝒢 n] (Q₀ n))
    (hrec : ∀ n ω, z (n + 1) ω
      = if n < τ ω then (if ξ n ω = 1 then zp n ω else zm n ω) else z n ω)
    (hτint : Integrable (fun ω => (τ ω : ℝ)) μ)
    (htstep : ∀ n ω, (ofLp (z (n + 1) ω)).2
      = (ofLp (z n ω)).2 + (if n < τ ω then ε * ξ n ω else 0))
    (ΛQ ΛE : ℝ) (hΛE0 : (0:ℝ) ≤ ΛE)
    (hQbd : ∀ (n : ℕ) (ω : Ω), ‖Q₀ n ω‖ ≤ ΛQ)
    (hEbd : ∀ (n : ℕ) (ω : Ω), n < τ ω →
      ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2 ≤ ΛE)
    (hstmeas : ∀ ζ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) → Measurable ζ)
    (hlimmeas : ∀ (G : ℕ → Ω → ℝ) (g : Ω → ℝ), (∀ h, Measurable (G h)) →
      (∀ ω, ∃ H : ℕ, ∀ h, H ≤ h → G h ω = g ω) → Measurable g)
    (hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ,
      (∀ m, Measurable (G m)) → Measurable (fun ω => G (ζ ω) ω)) :
    ∀ (ρ σ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ρ ω : ℕ∞)) →
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
                    - Q₀ n ω‖ ^ 2)) ∂μ) := by
  have hεne : ε ≠ 0 := ne_of_gt hε0
  intro ρ σ hρst hσst hρσ hστ p Cp r hr hpb hpmeas
  have hρmeas : Measurable ρ := hstmeas ρ hρst
  have hσmeas : Measurable σ := hstmeas σ hσst
  have hCp0 : (0:ℝ) ≤ Cp := le_trans (norm_nonneg (p hΩ.some)) (hpb hΩ.some)
  have hpsm : StronglyMeasurable p := by
    refine stronglyMeasurable_of_tendsto Filter.atTop
      (fun n => (hpmeas n).mono (𝒢.le n)) (tendsto_pi_nhds.mpr (fun ω => ?_))
    refine tendsto_atTop_of_eventually_const (i₀ := ρ ω) (fun n hn => ?_)
    rw [if_pos hn]
  have hεr : (0:ℝ) < ε / r := by positivity
  have hΛQ0 : (0:ℝ) ≤ ΛQ := le_trans (norm_nonneg (Q₀ 0 hΩ.some)) (hQbd 0 hΩ.some)
  -- the live window is predictable
  have hwinG : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | n ∈ Finset.Ico (ρ ω) (σ ω)} := by
    intro n
    have h1 : MeasurableSet[𝒢 n] {ω | ρ ω ≤ n} := by
      have h0 := hρst n
      have he : {ω | ρ ω ≤ n} = {ω | ((fun ω => (ρ ω : ℕ∞)) ω) ≤ (n : ℕ∞)} := by
        ext ω; simp only [Set.mem_ofPred_eq, Nat.cast_le]
      rw [he]; exact h0
    have h2 : MeasurableSet[𝒢 n] {ω | n < σ ω} := by
      have h0 := hσst n
      have he : {ω | n < σ ω} = {ω | ((fun ω => (σ ω : ℕ∞)) ω) ≤ (n : ℕ∞)}ᶜ := by
        ext ω; simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le, Nat.cast_lt]
      rw [he]; exact MeasurableSet.compl h0
    have he : {ω | n ∈ Finset.Ico (ρ ω) (σ ω)} = {ω | ρ ω ≤ n} ∩ {ω | n < σ ω} := by
      ext ω; simp only [Finset.mem_Ico, Set.mem_inter_iff, Set.mem_ofPred_eq]
    rw [he]; exact h1.inter h2
  -- random-range sums: measurability, integrability and the pathwise bound
  have hrsum : ∀ (c : ℕ → Ω → ℝ) (Λc : ℝ), (∀ n, Measurable (c n)) →
      (∀ n ω, 0 ≤ c n ω) → 0 ≤ Λc → (∀ n ω, n < τ ω → c n ω ≤ Λc) →
      Measurable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω) ∧
      Integrable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω) μ ∧
      (∀ ω, ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω ≤ Λc * (τ ω : ℝ)) := by
    intro c Λc hcmeas hc0 hΛc hcb
    have hpt : ∀ ω, ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω ≤ Λc * (τ ω : ℝ) := by
      intro ω
      have h1 : ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω
          ≤ ∑ n ∈ Finset.Ico (ρ ω) (σ ω), Λc :=
        Finset.sum_le_sum (fun n hn => hcb n ω
          (lt_of_lt_of_le (Finset.mem_Ico.mp hn).2 (hστ ω)))
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h1
      have h2 : ((σ ω - ρ ω : ℕ) : ℝ) ≤ (τ ω : ℝ) := by
        have : σ ω - ρ ω ≤ τ ω := le_trans (Nat.sub_le _ _) (hστ ω)
        exact_mod_cast this
      calc ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω ≤ ((σ ω - ρ ω : ℕ) : ℝ) * Λc := h1
        _ ≤ Λc * (τ ω : ℝ) := by
            rw [mul_comm]
            exact mul_le_mul_of_nonneg_left h2 hΛc
    have hmeas : Measurable (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω), c n ω) := by
      refine hlimmeas (fun h ω => ∑ n ∈ Finset.range h,
        (if n ∈ Finset.Ico (ρ ω) (σ ω) then c n ω else 0)) _ (fun h => ?_) (fun ω => ?_)
      · exact Finset.measurable_sum _ (fun n _ =>
          ((hcmeas n).ite ((𝒢.le n) _ (hwinG n)) measurable_const))
      · refine ⟨τ ω, fun h hh => ?_⟩
        have hsub : Finset.Ico (ρ ω) (σ ω) ⊆ Finset.range h := by
          intro x hx
          exact Finset.mem_range.mpr
            (lt_of_lt_of_le (Finset.mem_Ico.mp hx).2 (le_trans (hστ ω) hh))
        have h1 : ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
            (if n ∈ Finset.Ico (ρ ω) (σ ω) then c n ω else 0)
            = ∑ n ∈ Finset.range h, (if n ∈ Finset.Ico (ρ ω) (σ ω) then c n ω else 0) :=
          Finset.sum_subset hsub (fun m _ hm' => by rw [if_neg hm'])
        rw [← h1]
        exact Finset.sum_congr rfl (fun m hm => if_pos hm)
    refine ⟨hmeas, ?_, hpt⟩
    refine Integrable.mono' (hτint.const_mul Λc) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun n _ => hc0 n ω))]
    exact hpt ω
  -- the three auxiliary integrands
  have hQmeas' : ∀ n, Measurable (fun ω => (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) := by
    intro n
    have h1 : StronglyMeasurable (fun ω => Q₀ n ω - p ω) :=
      ((hQmeas n).mono (𝒢.le n)).sub hpsm
    exact ((h1.norm.measurable.pow_const 2).const_mul _)
  have hEmeas' : ∀ n, Measurable (fun ω =>
      ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2) := by
    intro n
    have hc : Continuous fun u : WithLp 2 (F × ℝ) => (ofLp u).1 :=
      continuous_fst.comp (WithLp.prod_continuous_ofLp 2 F ℝ)
    have hz1 : StronglyMeasurable (fun ω => (ofLp (z n ω)).1) :=
      hc.comp_stronglyMeasurable ((hzmeas n).mono (𝒢.le n))
    have hz2 : StronglyMeasurable (fun ω => (ofLp (zp n ω)).1) :=
      hc.comp_stronglyMeasurable ((hzpmeas n).mono (𝒢.le n))
    have hz3 : StronglyMeasurable (fun ω => (ofLp (zm n ω)).1) :=
      hc.comp_stronglyMeasurable ((hzmmeas n).mono (𝒢.le n))
    have hq : StronglyMeasurable (Q₀ n) := (hQmeas n).mono (𝒢.le n)
    exact ((((hz2.sub hz1).const_smul ε⁻¹).sub hq).norm.measurable.pow_const 2).add
      ((((hz1.sub hz3).const_smul ε⁻¹).sub hq).norm.measurable.pow_const 2)
  obtain ⟨hQsm, hQsi, hQsb⟩ := hrsum (fun n ω => (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2)
    ((ε / r) ^ 2 * (ΛQ + Cp) ^ 2) hQmeas' (fun n ω => by positivity) (by positivity)
    (fun n ω _ => by
      have h1 : ‖Q₀ n ω - p ω‖ ≤ ΛQ + Cp :=
        le_trans (norm_sub_le _ _) (by linarith only [hQbd n ω, hpb ω])
      have h2 := mul_self_le_mul_self (norm_nonneg (Q₀ n ω - p ω)) h1
      have h3 : (0:ℝ) ≤ (ε / r) ^ 2 := by positivity
      nlinarith only [h2, h3])
  obtain ⟨hEsm, hEsi, hEsb⟩ := hrsum (fun n ω =>
      ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)
    ΛE hEmeas' (fun n ω => by positivity) hΛE0 (fun n ω hn => hEbd n ω hn)
  have hTsi : Integrable (fun ω => (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ))) μ := by
    refine Integrable.mono' (hτint.const_mul ((ε / r) ^ 2))
      ((((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp hσmeas).sub
        ((measurable_from_top (f := fun k : ℕ => (k : ℝ))).comp hρmeas)).const_mul
          _).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    have h1 : (0:ℝ) ≤ (σ ω : ℝ) - (ρ ω : ℝ) := by
      have : (ρ ω : ℝ) ≤ (σ ω : ℝ) := by exact_mod_cast hρσ ω
      linarith only [this]
    have h2 : (σ ω : ℝ) - (ρ ω : ℝ) ≤ (τ ω : ℝ) := by
      have h3 : (σ ω : ℝ) ≤ (τ ω : ℝ) := by exact_mod_cast hστ ω
      have h4 : (0:ℝ) ≤ (ρ ω : ℝ) := Nat.cast_nonneg _
      linarith only [h3, h4]
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h5 : (0:ℝ) ≤ (ε / r) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_left h2 h5
  -- the increments of the walk in the sheared frame
  have hc1 : Continuous fun u : WithLp 2 (F × ℝ) => (ofLp u).1 :=
    continuous_fst.comp (WithLp.prod_continuous_ofLp 2 F ℝ)
  have hc2 : Continuous fun u : WithLp 2 (F × ℝ) => (ofLp u).2 :=
    continuous_snd.comp (WithLp.prod_continuous_ofLp 2 F ℝ)
  have hzx : ∀ n, StronglyMeasurable (fun ω => (ofLp (z n ω)).1) := fun n =>
    hc1.comp_stronglyMeasurable ((hzmeas n).mono (𝒢.le n))
  have hzt : ∀ n, StronglyMeasurable (fun ω => (ofLp (z n ω)).2) := fun n =>
    hc2.comp_stronglyMeasurable ((hzmeas n).mono (𝒢.le n))
  obtain ⟨w, hwd⟩ : ∃ f : ℕ → Ω → F, f = fun n ω =>
      if n ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) • (Q₀ n ω - p ω) else 0 := ⟨_, rfl⟩
  have hwmeasG : ∀ n, StronglyMeasurable[𝒢 n] (w n) := by
    intro n
    have he : w n = fun ω => if n ∈ Finset.Ico (ρ ω) (σ ω)
        then (ε / r) • (Q₀ n ω - (if ρ ω ≤ n then p ω else 0)) else 0 := by
      simp only [hwd]; funext ω
      by_cases hc : n ∈ Finset.Ico (ρ ω) (σ ω)
      · rw [if_pos hc, if_pos hc, if_pos (Finset.mem_Ico.mp hc).1]
      · rw [if_neg hc, if_neg hc]
    rw [he]
    exact StronglyMeasurable.ite (hwinG n)
      (((hQmeas n).sub (hpmeas n)).const_smul (ε / r)) stronglyMeasurable_const
  have hwbd : ∀ n ω, ‖w n ω‖ ≤ (ε / r) * (ΛQ + Cp) := by
    intro n ω
    simp only [hwd]
    by_cases hc : n ∈ Finset.Ico (ρ ω) (σ ω)
    · rw [if_pos hc, norm_smul, Real.norm_eq_abs, abs_of_pos hεr]
      have h1 : ‖Q₀ n ω - p ω‖ ≤ ΛQ + Cp :=
        le_trans (norm_sub_le _ _) (by linarith only [hQbd n ω, hpb ω])
      exact mul_le_mul_of_nonneg_left h1 hεr.le
    · rw [if_neg hc, norm_zero]
      have h2 : (0:ℝ) ≤ (ε / r) * (ΛQ + Cp) :=
        mul_nonneg hεr.le (by linarith only [hΛQ0, hCp0])
      linarith only [h2]
  obtain ⟨M, hMd⟩ : ∃ f : ℕ → Ω → F, f = fun n ω =>
      ∑ k ∈ Finset.range n, ξ k ω • w k ω := ⟨_, rfl⟩
  have hdmeasG : ∀ k n : ℕ, k < n → StronglyMeasurable[𝒢 n] (fun ω => ξ k ω • w k ω) := by
    intro k n hkn
    exact StronglyMeasurable.smul ((hξmeas k).mono (𝒢.mono (by omega)))
      ((hwmeasG k).mono (𝒢.mono (by omega)))
  have hMmeasG : ∀ n, StronglyMeasurable[𝒢 n] (M n) := by
    intro n
    simp only [hMd]
    exact Finset.stronglyMeasurable_fun_sum _
      (fun k hk => hdmeasG k n (Finset.mem_range.mp hk))
  have hdbd : ∀ n ω, ‖ξ n ω • w n ω‖ ≤ (ε / r) * (ΛQ + Cp) := by
    intro n ω
    rw [norm_smul]
    have h1 : ‖ξ n ω‖ = 1 := by
      rcases hξpm n ω with h | h <;> rw [h] <;> simp
    rw [h1, one_mul]
    exact hwbd n ω
  have hdint : ∀ n, Integrable (fun ω => ξ n ω • w n ω) μ := by
    intro n
    exact Integrable.mono' (integrable_const ((ε / r) * (ΛQ + Cp)))
      ((hdmeasG n (n + 1) (by omega)).mono (𝒢.le (n + 1))).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => hdbd n ω))
  have hMint : ∀ n, Integrable (M n) μ := by
    intro n
    simp only [hMd]
    exact integrable_finsetSum _ (fun k _ => hdint k)
  have hMbd : ∀ n ω, ‖M n ω‖ ≤ (n : ℝ) * ((ε / r) * (ΛQ + Cp)) := by
    intro n ω
    simp only [hMd]
    calc ‖∑ k ∈ Finset.range n, ξ k ω • w k ω‖
        ≤ ∑ k ∈ Finset.range n, ‖ξ k ω • w k ω‖ := norm_sum_le _ _
      _ ≤ ∑ _k ∈ Finset.range n, ((ε / r) * (ΛQ + Cp)) :=
          Finset.sum_le_sum (fun k _ => hdbd k ω)
      _ = (n : ℝ) * ((ε / r) * (ΛQ + Cp)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hMsq : ∀ n, Integrable (fun ω => ‖M n ω‖ ^ 2) μ := by
    intro n
    refine Integrable.mono' (integrable_const (((n : ℝ) * ((ε / r) * (ΛQ + Cp))) ^ 2))
      (((hMmeasG n).mono (𝒢.le n)).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖M n ω‖))]
    have h := hMbd n ω
    nlinarith only [h, norm_nonneg (M n ω)]
  have hmart : Martingale M 𝒢 μ := by
    refine martingale_of_condExp_sub_eq_zero_nat (fun n => hMmeasG n) hMint (fun n => ?_)
    have he : (M (n + 1) - M n) = fun ω => ξ n ω • w n ω := by
      funext ω
      simp only [hMd, Pi.sub_apply, Finset.sum_range_succ]
      abel
    rw [he]
    let B : F →L[ℝ] ℝ →L[ℝ] F := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).flip
    have hB : ∀ (u : F) (s : ℝ), B u s = s • u := fun u s => rfl
    have hξint : Integrable (ξ n) μ := by
      refine Integrable.mono' (integrable_const (1:ℝ))
        (((hξmeas n).mono (𝒢.le (n + 1))).aestronglyMeasurable)
        (Filter.Eventually.of_forall (fun ω => ?_))
      rcases hξpm n ω with h1 | h1 <;> rw [h1] <;> norm_num
    have hgoal : (fun ω => ξ n ω • w n ω) = fun ω => B (w n ω) (ξ n ω) := by
      funext ω; rw [hB]
    rw [hgoal]
    have h := condExp_bilin_of_stronglyMeasurable_left (B := B) (hwmeasG n)
      (by simpa only [hB] using hdint n) hξint
    filter_upwards [h, hξcond n] with ω h1 h2
    rw [h1, h2]
    simp only [Pi.zero_apply, hB, zero_smul]
  -- the running maximum of the martingale
  obtain ⟨Φ, hΦd⟩ : ∃ f : ℕ → Ω → ℝ, f = fun h ω =>
      (Finset.range (h + 1)).sup' Finset.nonempty_range_add_one (fun k => ‖M k ω‖) := ⟨_, rfl⟩
  have hΦmeas : ∀ h, Measurable (Φ h) := by
    intro h
    simp only [hΦd]
    exact Finset.measurable_range_sup'' (fun k _ =>
      (((hMmeasG k).mono (𝒢.le k)).norm).measurable)
  have hΦnn : ∀ h ω, 0 ≤ Φ h ω := by
    intro h ω
    simp only [hΦd]
    exact le_trans (norm_nonneg (M 0 ω))
      (Finset.le_sup' (fun k => ‖M k ω‖) (Finset.mem_range.mpr (Nat.succ_pos h)))
  have hΦle : ∀ (h n : ℕ) (ω : Ω), n ≤ h → ‖M n ω‖ ≤ Φ h ω := by
    intro h n ω hnh
    simp only [hΦd]
    exact Finset.le_sup' (fun k => ‖M k ω‖) (Finset.mem_range.mpr (by omega))
  have hΦmono : ∀ (h h' : ℕ) (ω : Ω), h ≤ h' → Φ h ω ≤ Φ h' ω := by
    intro h h' ω hh
    simp only [hΦd]
    refine Finset.sup'_le _ _ (fun k hk => ?_)
    exact Finset.le_sup' (fun k => ‖M k ω‖)
      (Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hk) (by omega)))
  have hwout : ∀ (k : ℕ) (ω : Ω), ¬ (k ∈ Finset.Ico (ρ ω) (σ ω)) → w k ω = 0 := by
    intro k ω hk
    simp only [hwd, if_neg hk]
  have hMfroz : ∀ (k : ℕ) (ω : Ω), σ ω ≤ k → M k ω = M (σ ω) ω := by
    intro k ω hk
    induction k with
    | zero => rw [Nat.le_zero.mp hk]
    | succ k ih =>
        rcases Nat.lt_or_ge (σ ω) (k + 1) with h | h
        · have h2 : σ ω ≤ k := by omega
          have h3 : w k ω = 0 := hwout k ω (by
            rw [Finset.mem_Ico]
            omega)
          simp only [hMd, Finset.sum_range_succ, h3, smul_zero, add_zero]
          simpa only [hMd] using ih h2
        · rw [show σ ω = k + 1 by omega]
  have hΦfroz : ∀ (h : ℕ) (ω : Ω), σ ω ≤ h → Φ h ω = Φ (σ ω) ω := by
    intro h ω hh
    refine le_antisymm ?_ (hΦmono (σ ω) h ω hh)
    simp only [hΦd]
    refine Finset.sup'_le _ _ (fun k hk => ?_)
    rcases Nat.lt_or_ge k (σ ω + 1) with hc | hc
    · exact Finset.le_sup' (fun k => ‖M k ω‖) (Finset.mem_range.mpr hc)
    · rw [hMfroz k ω (by omega)]
      exact Finset.le_sup' (fun k => ‖M k ω‖)
        (Finset.mem_range.mpr (Nat.lt_succ_self (σ ω)))
  have hΦint : ∀ h, Integrable (Φ h) μ := by
    intro h
    simp only [hΦd]
    exact (DoobL2Maximal μ 𝒢 M hmart hMsq h).1
  -- the second moment of the martingale is at most the velocity sum
  have hdsq : ∀ (k : ℕ) (ω : Ω), ‖M (k + 1) ω - M k ω‖ ^ 2
      = if k ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) ^ 2 * ‖Q₀ k ω - p ω‖ ^ 2 else 0 := by
    intro k ω
    have he : M (k + 1) ω - M k ω = ξ k ω • w k ω := by
      simp only [hMd, Finset.sum_range_succ]
      abel
    rw [he, norm_smul]
    have h1 : ‖ξ k ω‖ = 1 := by
      rcases hξpm k ω with h | h <;> rw [h] <;> simp
    rw [h1, one_mul]
    by_cases hc : k ∈ Finset.Ico (ρ ω) (σ ω)
    · simp only [hwd, if_pos hc, norm_smul, Real.norm_eq_abs, abs_of_pos hεr]
      ring
    · simp only [hwd, if_neg hc, norm_zero]
      norm_num
  have hpartial : ∀ (c : ℕ → Ω → ℝ), (∀ n ω, 0 ≤ c n ω) → ∀ (h : ℕ) (ω : Ω),
      ∑ k ∈ Finset.range h, (if k ∈ Finset.Ico (ρ ω) (σ ω) then c k ω else 0)
        ≤ ∑ k ∈ Finset.Ico (ρ ω) (σ ω), c k ω := by
    intro c hc0 h ω
    calc ∑ k ∈ Finset.range h, (if k ∈ Finset.Ico (ρ ω) (σ ω) then c k ω else 0)
        = ∑ k ∈ (Finset.range h).filter (fun k => k ∈ Finset.Ico (ρ ω) (σ ω)), c k ω :=
          (Finset.sum_filter _ _).symm
      _ ≤ ∑ k ∈ Finset.Ico (ρ ω) (σ ω), c k ω :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun x hx => (Finset.mem_filter.mp hx).2) (fun k _ _ => hc0 k ω)
  have hMsqle : ∀ h, ∫ ω, ‖M h ω‖ ^ 2 ∂μ
      ≤ ∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω), (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ := by
    intro h
    have horth := (DoobL2Maximal μ 𝒢 M hmart hMsq h).2.2
    have hM0 : ∫ ω, ‖M 0 ω‖ ^ 2 ∂μ = 0 := by
      have he : ∀ ω, ‖M 0 ω‖ ^ 2 = 0 := by
        intro ω; simp only [hMd]; simp
      rw [integral_congr_ae (Filter.Eventually.of_forall he)]
      simp
    rw [hM0, zero_add] at horth
    have hterm : ∀ k, Integrable (fun ω =>
        if k ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) ^ 2 * ‖Q₀ k ω - p ω‖ ^ 2 else 0) μ := by
      intro k
      refine Integrable.mono' (integrable_const ((ε / r) ^ 2 * (ΛQ + Cp) ^ 2))
        (((hQmeas' k).ite ((𝒢.le k) _ (hwinG k)) measurable_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      have h1 : ‖Q₀ k ω - p ω‖ ≤ ΛQ + Cp :=
        le_trans (norm_sub_le _ _) (by linarith only [hQbd k ω, hpb ω])
      have h2 := mul_self_le_mul_self (norm_nonneg (Q₀ k ω - p ω)) h1
      have h3 : (0:ℝ) ≤ (ε / r) ^ 2 := by positivity
      rw [Real.norm_eq_abs]
      by_cases hc : k ∈ Finset.Ico (ρ ω) (σ ω)
      · rw [if_pos hc, abs_of_nonneg (by positivity)]
        nlinarith only [h2, h3]
      · rw [if_neg hc, abs_zero]
        nlinarith only [h2, h3]
    have hsum : ∑ k ∈ Finset.range h, ∫ ω, ‖M (k + 1) ω - M k ω‖ ^ 2 ∂μ
        = ∫ ω, (∑ k ∈ Finset.range h,
            (if k ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) ^ 2 * ‖Q₀ k ω - p ω‖ ^ 2 else 0)) ∂μ := by
      rw [integral_finsetSum _ (fun k _ => hterm k)]
      exact Finset.sum_congr rfl (fun k _ =>
        integral_congr_ae (Filter.Eventually.of_forall (fun ω => hdsq k ω)))
    rw [horth, hsum]
    refine integral_mono (integrable_finsetSum _ (fun k _ => hterm k)) hQsi (fun ω => ?_)
    exact hpartial (fun n ω => (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2)
      (fun n ω => by positivity) h ω
  have hJ1nn : (0:ℝ) ≤ ∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
      (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ :=
    integral_nonneg (fun ω => Finset.sum_nonneg (fun n _ => by positivity))
  have hΦbd : ∀ h, ∫ ω, Φ h ω ∂μ ≤ 2 * Real.sqrt (∫ ω,
      (∑ n ∈ Finset.Ico (ρ ω) (σ ω), (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ) := by
    intro h
    have h1 := (DoobL2Maximal μ 𝒢 M hmart hMsq h).2.1
    have h2 : Real.sqrt (∫ ω, ‖M h ω‖ ^ 2 ∂μ)
        ≤ Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
            (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ) := Real.sqrt_le_sqrt (hMsqle h)
    simp only [hΦd]
    linarith only [h1, h2]
  -- the maximum over the whole stopped range
  have hPhiSmeas : Measurable (fun ω => Φ (σ ω) ω) := hrandidx σ hσmeas Φ hΦmeas
  have hPhiSnn : ∀ ω, 0 ≤ Φ (σ ω) ω := fun ω => hΦnn (σ ω) ω
  have hPhiSlint : ∫⁻ ω, ENNReal.ofReal (Φ (σ ω) ω) ∂μ
      ≤ ENNReal.ofReal (2 * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
          (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ)) := by
    have hmono : Monotone (fun h => fun ω => ENNReal.ofReal (Φ h ω)) := by
      intro a b hab ω
      exact ENNReal.ofReal_le_ofReal (hΦmono a b ω hab)
    have hsup : ∀ ω, (⨆ h : ℕ, ENNReal.ofReal (Φ h ω)) = ENNReal.ofReal (Φ (σ ω) ω) := by
      intro ω
      refine le_antisymm (iSup_le (fun h => ?_)) (le_iSup_of_le (σ ω) le_rfl)
      rcases Nat.lt_or_ge h (σ ω) with hc | hc
      · exact ENNReal.ofReal_le_ofReal (hΦmono h (σ ω) ω (le_of_lt hc))
      · rw [hΦfroz h ω hc]
    calc ∫⁻ ω, ENNReal.ofReal (Φ (σ ω) ω) ∂μ
        = ∫⁻ ω, ⨆ h : ℕ, ENNReal.ofReal (Φ h ω) ∂μ := by
          exact lintegral_congr (fun ω => (hsup ω).symm)
      _ = ⨆ h : ℕ, ∫⁻ ω, ENNReal.ofReal (Φ h ω) ∂μ :=
          lintegral_iSup (fun h => (hΦmeas h).ennreal_ofReal) hmono
      _ ≤ _ := by
          refine iSup_le (fun h => ?_)
          rw [← ofReal_integral_eq_lintegral_ofReal (hΦint h)
            (Filter.Eventually.of_forall (hΦnn h))]
          exact ENNReal.ofReal_le_ofReal (hΦbd h)
  have hPhiSint : Integrable (fun ω => Φ (σ ω) ω) μ := by
    refine ⟨hPhiSmeas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hPhiSnn)]
    exact lt_of_le_of_lt hPhiSlint ENNReal.ofReal_lt_top
  have hPhiSbd : ∫ ω, Φ (σ ω) ω ∂μ ≤ 2 * Real.sqrt (∫ ω,
      (∑ n ∈ Finset.Ico (ρ ω) (σ ω), (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ) := by
    have h1 := ofReal_integral_eq_lintegral_ofReal hPhiSint
      (Filter.Eventually.of_forall hPhiSnn)
    rw [← h1] at hPhiSlint
    have h2 : (0:ℝ) ≤ 2 * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
        (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ) := by positivity
    exact (ENNReal.ofReal_le_ofReal_iff h2).mp hPhiSlint
  -- the selected step velocity and the error increments
  have hzpx : ∀ n, StronglyMeasurable (fun ω => (ofLp (zp n ω)).1) := fun n =>
    hc1.comp_stronglyMeasurable ((hzpmeas n).mono (𝒢.le n))
  have hzmx : ∀ n, StronglyMeasurable (fun ω => (ofLp (zm n ω)).1) := fun n =>
    hc1.comp_stronglyMeasurable ((hzmmeas n).mono (𝒢.le n))
  obtain ⟨Qs, hQsd⟩ : ∃ f : ℕ → Ω → F, f = fun k ω =>
      if ξ k ω = 1 then ε⁻¹ • ((ofLp (zp k ω)).1 - (ofLp (z k ω)).1)
      else ε⁻¹ • ((ofLp (z k ω)).1 - (ofLp (zm k ω)).1) := ⟨_, rfl⟩
  have hQssm : ∀ k, StronglyMeasurable (Qs k) := by
    intro k
    simp only [hQsd]
    refine StronglyMeasurable.ite ?_ ?_ ?_
    · exact ((hξmeas k).mono (𝒢.le (k + 1))).measurable (measurableSet_singleton 1)
    · exact ((hzpx k).sub (hzx k)).const_smul ε⁻¹
    · exact ((hzx k).sub (hzmx k)).const_smul ε⁻¹
  have hQsE : ∀ (k : ℕ) (ω : Ω), ‖Qs k ω - Q₀ k ω‖ ^ 2
      ≤ ‖ε⁻¹ • ((ofLp (zp k ω)).1 - (ofLp (z k ω)).1) - Q₀ k ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z k ω)).1 - (ofLp (zm k ω)).1) - Q₀ k ω‖ ^ 2 := by
    intro k ω
    by_cases hc : ξ k ω = 1
    · simp only [hQsd, if_pos hc]
      have h1 : (0:ℝ) ≤ ‖ε⁻¹ • ((ofLp (z k ω)).1 - (ofLp (zm k ω)).1) - Q₀ k ω‖ ^ 2 := by
        positivity
      linarith only [h1]
    · simp only [hQsd, if_neg hc]
      have h1 : (0:ℝ) ≤ ‖ε⁻¹ • ((ofLp (zp k ω)).1 - (ofLp (z k ω)).1) - Q₀ k ω‖ ^ 2 := by
        positivity
      linarith only [h1]
  obtain ⟨e, hed⟩ : ∃ f : ℕ → Ω → F, f = fun k ω =>
      if k ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) • (ξ k ω • (Qs k ω - Q₀ k ω))
      else 0 := ⟨_, rfl⟩
  have henorm : ∀ (k : ℕ) (ω : Ω), ‖e k ω‖
      = if k ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) * ‖Qs k ω - Q₀ k ω‖ else 0 := by
    intro k ω
    by_cases hc : k ∈ Finset.Ico (ρ ω) (σ ω)
    · simp only [hed, if_pos hc, norm_smul, Real.norm_eq_abs, abs_of_pos hεr]
      have h1 : |ξ k ω| = 1 := by
        rcases hξpm k ω with h | h <;> rw [h] <;> norm_num
      rw [h1, one_mul]
    · simp only [hed, if_neg hc, norm_zero]
  have hemeas : ∀ k, Measurable (fun ω => ‖e k ω‖) := by
    intro k
    have he : (fun ω => ‖e k ω‖) = fun ω =>
        if k ∈ Finset.Ico (ρ ω) (σ ω) then (ε / r) * ‖Qs k ω - Q₀ k ω‖ else 0 := by
      funext ω; exact henorm k ω
    rw [he]
    exact Measurable.ite ((𝒢.le k) _ (hwinG k))
      ((((hQssm k).sub ((hQmeas k).mono (𝒢.le k))).norm.measurable).const_mul _)
      measurable_const
  -- the increments of the walk
  have hxstep : ∀ (k : ℕ) (ω : Ω), k < τ ω →
      (ofLp (z (k + 1) ω)).1 - (ofLp (z k ω)).1 = (ε * ξ k ω) • Qs k ω := by
    intro k ω hk
    rcases hξpm k ω with h1 | h1
    · rw [hrec k ω, if_pos hk, if_pos h1]
      simp only [hQsd, if_pos h1, h1, mul_one]
      rw [smul_smul, mul_inv_cancel₀ hεne, one_smul]
    · have hne : ¬ (ξ k ω = 1) := by rw [h1]; norm_num
      rw [hrec k ω, if_pos hk, if_neg hne]
      simp only [hQsd, if_neg hne, h1]
      rw [smul_smul, show ε * (-1:ℝ) * ε⁻¹ = -1 by field_simp]
      module
  have htstep' : ∀ (k : ℕ) (ω : Ω), k < τ ω →
      (ofLp (z (k + 1) ω)).2 - (ofLp (z k ω)).2 = ε * ξ k ω := by
    intro k ω hk
    rw [htstep k ω, if_pos hk]
    ring
  -- the pathwise decomposition of the sheared displacement
  have hyid : ∀ (n : ℕ) (ω : Ω), ρ ω ≤ n → n ≤ σ ω →
      r⁻¹ • ((ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
          - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω)
        = M n ω + ∑ k ∈ Finset.Ico (ρ ω) n, e k ω := by
    intro n ω hn1
    induction n, hn1 using Nat.le_induction with
    | base =>
        intro _
        have hM0 : M (ρ ω) ω = 0 := by
          simp only [hMd]
          refine Finset.sum_eq_zero (fun k hk => ?_)
          have hk' : k < ρ ω := Finset.mem_range.mp hk
          rw [hwout k ω (by rw [Finset.mem_Ico]; omega), smul_zero]
        rw [hM0, Finset.Ico_self, Finset.sum_empty, add_zero]
        simp
    | succ n hn ih =>
        intro hn2
        have hn2' : n ≤ σ ω := by omega
        have hnτ : n < τ ω := lt_of_lt_of_le (by omega) (hστ ω)
        have hwin : n ∈ Finset.Ico (ρ ω) (σ ω) := Finset.mem_Ico.mpr ⟨hn, by omega⟩
        have ih' := ih hn2'
        have hMs : M (n + 1) ω = M n ω + ξ n ω • w n ω := by
          simp only [hMd, Finset.sum_range_succ]
        have hes : ∑ k ∈ Finset.Ico (ρ ω) (n + 1), e k ω
            = (∑ k ∈ Finset.Ico (ρ ω) n, e k ω) + e n ω :=
          Finset.sum_Ico_succ_top hn _
        have hinc : ξ n ω • w n ω + e n ω
            = r⁻¹ • (((ofLp (z (n + 1) ω)).1 - (ofLp (z n ω)).1)
                - ((ofLp (z (n + 1) ω)).2 - (ofLp (z n ω)).2) • p ω) := by
          rw [hxstep n ω hnτ, htstep' n ω hnτ]
          simp only [hwd, hed, if_pos hwin]
          module
        rw [hMs, hes]
        have hsplit : r⁻¹ • ((ofLp (z (n + 1) ω)).1 - (ofLp (z (ρ ω) ω)).1
              - ((ofLp (z (n + 1) ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω)
            = r⁻¹ • ((ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
                - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω)
              + r⁻¹ • (((ofLp (z (n + 1) ω)).1 - (ofLp (z n ω)).1)
                - ((ofLp (z (n + 1) ω)).2 - (ofLp (z n ω)).2) • p ω) := by
          module
        rw [hsplit, ih', ← hinc]
        abel
  -- the error sum: integrability and the pathwise Cauchy-Schwarz bound
  have hebd : ∀ (k : ℕ) (ω : Ω), k < τ ω → ‖e k ω‖ ≤ (ε / r) * Real.sqrt ΛE := by
    intro k ω hk
    have h1 : ‖Qs k ω - Q₀ k ω‖ ≤ Real.sqrt ΛE := by
      have h2 := le_trans (hQsE k ω) (hEbd k ω hk)
      have h3 := Real.sqrt_le_sqrt h2
      rwa [Real.sqrt_sq (norm_nonneg _)] at h3
    rw [henorm k ω]
    by_cases hc : k ∈ Finset.Ico (ρ ω) (σ ω)
    · rw [if_pos hc]
      exact mul_le_mul_of_nonneg_left h1 hεr.le
    · rw [if_neg hc]
      positivity
  obtain ⟨hErrm, hErri, hErrb⟩ := hrsum (fun k ω => ‖e k ω‖) ((ε / r) * Real.sqrt ΛE)
    hemeas (fun k ω => norm_nonneg _) (by positivity) hebd
  have hTnn : ∀ ω, (0:ℝ) ≤ (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)) := by
    intro ω
    have h1 : (ρ ω : ℝ) ≤ (σ ω : ℝ) := by exact_mod_cast hρσ ω
    have h2 : (0:ℝ) ≤ (ε / r) ^ 2 := by positivity
    have h3 : (0:ℝ) ≤ (σ ω : ℝ) - (ρ ω : ℝ) := by linarith only [h1]
    positivity
  have hEnn : ∀ ω, (0:ℝ) ≤ ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
      (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2) :=
    fun ω => Finset.sum_nonneg (fun n _ => by positivity)
  have hErrCS : ∀ ω, ∑ k ∈ Finset.Ico (ρ ω) (σ ω), ‖e k ω‖
      ≤ Real.sqrt ((ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)))
        * Real.sqrt (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
            (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) := by
    intro ω
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (Finset.Ico (ρ ω) (σ ω))
      (r := fun k => ‖e k ω‖) (f := fun _ => (ε / r) ^ 2)
      (g := fun n => ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)
      (fun i _ => by positivity) (fun i _ => by positivity) (fun i hi => ?_)
    · have hsum1 : ∑ _k ∈ Finset.Ico (ρ ω) (σ ω), (ε / r) ^ 2
          = (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        have h1 : ((σ ω - ρ ω : ℕ) : ℝ) = (σ ω : ℝ) - (ρ ω : ℝ) := by
          have := hρσ ω
          push_cast [Nat.cast_sub this]
          ring
        rw [h1]
        ring
      rw [hsum1] at hcs
      have h4 := Real.sqrt_le_sqrt hcs
      rw [Real.sqrt_sq (Finset.sum_nonneg (fun k _ => norm_nonneg _)),
        Real.sqrt_mul (hTnn ω)] at h4
      exact h4
    · have hiτ : i < τ ω :=
        lt_of_lt_of_le (Finset.mem_Ico.mp hi).2 (hστ ω)
      rw [henorm i ω, if_pos hi]
      have h5 := hQsE i ω
      have h6 : (0:ℝ) ≤ (ε / r) ^ 2 := by positivity
      nlinarith only [h5, h6, norm_nonneg (Qs i ω - Q₀ i ω)]
  have hErrbd : ∫ ω, (∑ k ∈ Finset.Ico (ρ ω) (σ ω), ‖e k ω‖) ∂μ
      ≤ Real.sqrt (∫ ω, (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)) ∂μ)
        * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
            (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ) := by
    obtain ⟨hprodint, hprodbd⟩ := IntegralSqrtProductCauchySchwarz μ
      (fun ω => (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)))
      (fun ω => ∑ n ∈ Finset.Ico (ρ ω) (σ ω),
        (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2))
      hTnn hEnn hTsi hEsi
    exact le_trans (integral_mono hErri hprodint (fun ω => hErrCS ω)) hprodbd
  -- the supremum: measurability, the pathwise bound, integrability
  obtain ⟨Ynm, hYnmd⟩ : ∃ f : ℕ → ℕ → Ω → ℝ, f = fun n m ω =>
      r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z m ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z m ω)).2) • p ω‖ := ⟨_, rfl⟩
  have hYnmmeas : ∀ n m, Measurable (Ynm n m) := by
    intro n m
    simp only [hYnmd]
    exact ((((hzx n).sub (hzx m)).sub (((hzt n).sub (hzt m)).smul hpsm)).norm.measurable).const_mul _
  have hYnmnn : ∀ n m ω, 0 ≤ Ynm n m ω := by
    intro n m ω
    simp only [hYnmd]
    positivity
  have hSpnn : ∀ ω, 0 ≤ (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖) := by
    intro ω
    refine le_trans (hYnmnn (ρ ω) (ρ ω) ω) ?_
    have h1 := Finset.le_sup' (f := fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖)
      (Finset.mem_Icc.mpr ⟨le_rfl, hρσ ω⟩)
    simp only [hYnmd]
    exact h1
  have hSpbd : ∀ ω, (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖)
      ≤ Φ (σ ω) ω + ∑ k ∈ Finset.Ico (ρ ω) (σ ω), ‖e k ω‖ := by
    intro ω
    refine Finset.sup'_le _ _ (fun n hn => ?_)
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hyn := hyid n ω hn1 hn2
    have hnorm : r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖
        = ‖M n ω + ∑ k ∈ Finset.Ico (ρ ω) n, e k ω‖ := by
      rw [← hyn, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r⁻¹)]
    rw [hnorm]
    have h1 : ‖M n ω + ∑ k ∈ Finset.Ico (ρ ω) n, e k ω‖
        ≤ ‖M n ω‖ + ∑ k ∈ Finset.Ico (ρ ω) n, ‖e k ω‖ :=
      le_trans (norm_add_le _ _) (by
        have := norm_sum_le (Finset.Ico (ρ ω) n) (fun k => e k ω)
        linarith only [this])
    have h2 : ‖M n ω‖ ≤ Φ (σ ω) ω := hΦle (σ ω) n ω hn2
    have h3 : ∑ k ∈ Finset.Ico (ρ ω) n, ‖e k ω‖
        ≤ ∑ k ∈ Finset.Ico (ρ ω) (σ ω), ‖e k ω‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Ico_subset_Ico le_rfl hn2) (fun k _ _ => norm_nonneg _)
    linarith only [h1, h2, h3]
  have hSpY : (fun ω => (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖))
      = fun ω => (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
        (fun n => Ynm n (ρ ω) ω) := by
    funext ω
    simp only [hYnmd]
  have hSpmeas : Measurable (fun ω => (Finset.Icc (ρ ω) (σ ω)).sup'
      (Finset.nonempty_Icc.mpr (hρσ ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖)) := by
    rw [hSpY]
    refine hlimmeas (fun h ω => (Finset.range (h + 1)).sup' Finset.nonempty_range_add_one
      (fun n => if n ∈ Finset.Icc (ρ ω) (σ ω) then Ynm n (ρ ω) ω else 0)) _
      (fun h => ?_) (fun ω => ?_)
    · refine Finset.measurable_range_sup'' (fun n _ => ?_)
      refine Measurable.ite ?_ (hrandidx ρ hρmeas (fun m => Ynm n m) (fun m => hYnmmeas n m))
        measurable_const
      have he : {ω | n ∈ Finset.Icc (ρ ω) (σ ω)} = {ω | ρ ω ≤ n} ∩ {ω | n ≤ σ ω} := by
        ext ω; simp only [Finset.mem_Icc, Set.mem_inter_iff, Set.mem_ofPred_eq]
      rw [he]
      exact ((hρmeas (measurableSet_Iic (a := n))).inter
        (hσmeas (measurableSet_Ici (a := n))))
    · have hSpnn' : ∀ ω, 0 ≤ (Finset.Icc (ρ ω) (σ ω)).sup'
          (Finset.nonempty_Icc.mpr (hρσ ω)) (fun n => Ynm n (ρ ω) ω) := by
        intro ω
        refine le_trans (hYnmnn (ρ ω) (ρ ω) ω) ?_
        exact Finset.le_sup' (fun k => Ynm k (ρ ω) ω) (Finset.mem_Icc.mpr ⟨le_rfl, hρσ ω⟩)
      refine ⟨σ ω, fun h hh => ?_⟩
      refine le_antisymm (Finset.sup'_le _ _ (fun n hn => ?_))
        (Finset.sup'_le _ _ (fun n hn => ?_))
      · by_cases hc : n ∈ Finset.Icc (ρ ω) (σ ω)
        · rw [if_pos hc]
          exact Finset.le_sup' (fun k => Ynm k (ρ ω) ω) hc
        · rw [if_neg hc]
          exact hSpnn' ω
      · have hn' : n ∈ Finset.range (h + 1) := by
          obtain ⟨-, h2⟩ := Finset.mem_Icc.mp hn
          exact Finset.mem_range.mpr (by omega)
        have h3 := Finset.le_sup' (fun k => if k ∈ Finset.Icc (ρ ω) (σ ω)
          then Ynm k (ρ ω) ω else 0) hn'
        rw [if_pos hn] at h3
        exact h3
  have hI1 : Integrable (fun ω => (Finset.Icc (ρ ω) (σ ω)).sup'
      (Finset.nonempty_Icc.mpr (hρσ ω))
      (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
        - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖)) μ := by
    refine Integrable.mono' (hPhiSint.add hErri) hSpmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hSpnn ω)]
    exact hSpbd ω
  refine ⟨hI1, hQsi, hTsi, hEsi, ?_⟩
  calc ∫ ω, (Finset.Icc (ρ ω) (σ ω)).sup' (Finset.nonempty_Icc.mpr (hρσ ω))
          (fun n => r⁻¹ * ‖(ofLp (z n ω)).1 - (ofLp (z (ρ ω) ω)).1
            - ((ofLp (z n ω)).2 - (ofLp (z (ρ ω) ω)).2) • p ω‖) ∂μ
      ≤ ∫ ω, (Φ (σ ω) ω + ∑ k ∈ Finset.Ico (ρ ω) (σ ω), ‖e k ω‖) ∂μ :=
        integral_mono hI1 (hPhiSint.add hErri) hSpbd
    _ = (∫ ω, Φ (σ ω) ω ∂μ) + ∫ ω, (∑ k ∈ Finset.Ico (ρ ω) (σ ω), ‖e k ω‖) ∂μ :=
        integral_add hPhiSint hErri
    _ ≤ 2 * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
            (ε / r) ^ 2 * ‖Q₀ n ω - p ω‖ ^ 2) ∂μ)
          + Real.sqrt (∫ ω, (ε / r) ^ 2 * ((σ ω : ℝ) - (ρ ω : ℝ)) ∂μ)
            * Real.sqrt (∫ ω, (∑ n ∈ Finset.Ico (ρ ω) (σ ω),
                (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
                  + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1)
                      - Q₀ n ω‖ ^ 2)) ∂μ) :=
        add_le_add hPhiSbd hErrbd
