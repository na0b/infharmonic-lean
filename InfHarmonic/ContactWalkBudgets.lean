module

public import InfHarmonic.IsContactWalk
public import InfHarmonic.DPDrift
public import InfHarmonic.JUpperBound
public import InfHarmonic.FittedEnvelopeBounds
public import InfHarmonic.OptionalStoppingErrorBudget
public import InfHarmonic.JGapLowerBoundAndContinuity

@[expose] public section
set_option maxHeartbeats 400000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.7, the two budgets of part 1: a constant `C_*`, independent of
`T`, `R` and `N`, such that every stopped contact walk for `(κ, H, T, R, v, N, ε)`
satisfies the stopped expectation bound (6.18) at every stopping time below `τ`
and the error budget (6.19) with `B₀ = C_* L(B)⁴`, `B = R + T + 2`. -/
theorem ContactWalkBudgets (C₀ κ H : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJbd : HasJensenBound Set.univ v κ)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ)) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ T : ℕ, 2 ≤ T → ∀ R : ℝ, 2 ≤ R → ∀ N : ℕ, 1 ≤ N →
        ∀ (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω)
          (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
          (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ),
          IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ →
          ((∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → (∀ ω, σ ω ≤ τ ω) →
            Integrable (fun ω => JGap v κ ε (z (σ ω) ω)) μ ∧
            JGap v κ ε (toLp 2 ((0 : F), (1 : ℝ)))
              ≤ ∫ ω, JGap v κ ε (z (σ ω) ω) ∂μ) ∧
          Integrable (fun ω => ∑ n ∈ Finset.range (τ ω),
            (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) μ ∧
          ∫ ω, (∑ n ∈ Finset.range (τ ω),
            (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ
            ≤ Cstar * (1 + Real.log (R + (T : ℝ) + 2)) ^ 4) := by
  classical
  -- ## the constants, fixed before `T`, `R` and `N`
  obtain ⟨C₁, hC₁0, hC₁⟩ := FittedEnvelopeBounds (F := F) C₀ hC₀
  set c : ℝ := 1 / (16 * (1 + Real.log 2)) with hcdef
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hc0 : 0 < c := by
    rw [hcdef]
    positivity
  refine ⟨(C₁ + |H| + 1) / c, by positivity, ?_⟩
  intro T hT R hR N hN ε Ω m0 μ 𝒢 ξ z zp zm Q₀ τ hcw
  obtain ⟨hμ1, ⟨kk, hεk⟩, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
    hstep, hrec, hgradc, hτst, hτint, hlive, hexit, hxbd, hstart⟩ := hcw
  have hprob : IsProbabilityMeasure μ := ⟨hμ1⟩
  -- ## elementary numerical facts
  set d : ℝ := (1 / 2 : ℝ) ^ N with hd
  have hd0 : 0 < d := by rw [hd]; positivity
  have hdle : d ≤ 1 / 2 := by
    rw [hd]
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
      _ = 1 / 2 := by norm_num
  have hTR : (2 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  have hεd : ε ≤ d / 4 := hεN
  have hεsmall : ε ≤ 1 / 8 := by linarith
  set B : ℝ := R + (T : ℝ) + 2 with hB
  have hB2 : (2 : ℝ) ≤ B := by rw [hB]; linarith
  have hB1 : (1 : ℝ) ≤ B := by linarith
  set L : ℝ := 1 + Real.log B with hL
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hL]
    have : (0 : ℝ) ≤ Real.log B := Real.log_nonneg hB1
    linarith
  -- ## the walk is frozen after `τ`
  have hfrz : ∀ (n : ℕ) (ω : Ω), τ ω ≤ n → z n ω = z (τ ω) ω := by
    intro n ω hn
    induction n with
    | zero =>
      have h0 : τ ω = 0 := by omega
      rw [h0]
    | succ n ih =>
      rcases Nat.lt_or_ge (τ ω) (n + 1) with h | h
      · have hn' : τ ω ≤ n := by omega
        rw [hrec n ω, if_neg (by omega), ih hn']
      · have h1 : τ ω = n + 1 := by omega
        rw [h1]
  -- ## the time coordinate stays in `[d - ε, T + ε]` and the space coordinate in the ball
  have htb : ∀ (n : ℕ) (ω : Ω),
      d - ε ≤ (ofLp (z n ω)).2 ∧ (ofLp (z n ω)).2 ≤ (T : ℝ) + ε := by
    intro n ω
    induction n with
    | zero =>
      rw [hz0 ω]
      have h1 : (ofLp (toLp 2 ((0 : F), (1 : ℝ))) : F × ℝ).2 = 1 := by simp
      rw [h1]
      constructor
      · linarith
      · linarith
    | succ n ih =>
      rcases Nat.lt_or_ge n (τ ω) with h | h
      · obtain ⟨Yp, Ym, -, -, hzpe, hzme⟩ := hstep n ω h
        have hlv := hlive n ω h
        rw [hrec n ω, if_pos h]
        by_cases hb : ξ n ω = 1
        · rw [if_pos hb, hzpe]
          have h2 : (ofLp (toLp 2 ((2 : ℝ)⁻¹ • ((ofLp (z n ω)).1 + Yp),
              (ofLp (z n ω)).2 + ε)) : F × ℝ).2 = (ofLp (z n ω)).2 + ε := by simp
          rw [h2]
          constructor
          · linarith [hlv.1]
          · linarith [hlv.2.1]
        · rw [if_neg hb, hzme]
          have h2 : (ofLp (toLp 2 ((2 : ℝ)⁻¹ • ((ofLp (z n ω)).1 + Ym),
              (ofLp (z n ω)).2 - ε)) : F × ℝ).2 = (ofLp (z n ω)).2 - ε := by simp
          rw [h2]
          constructor
          · linarith [hlv.1]
          · linarith [hlv.2.1]
      · rw [hrec n ω, if_neg (by omega)]
        exact ih
  have hxb : ∀ (n : ℕ) (ω : Ω), ‖(ofLp (z n ω)).1‖ ≤ R + 1 := by
    intro n ω
    rcases Nat.lt_or_ge n (τ ω + 1) with h | h
    · exact hxbd n ω (by omega)
    · rw [hfrz n ω (by omega)]
      exact hxbd (τ ω) ω le_rfl
  have ht0 : ∀ (n : ℕ) (ω : Ω), 0 < (ofLp (z n ω)).2 := by
    intro n ω
    have h1 := (htb n ω).1
    linarith
  -- ## the upper bound for `J_ε` on the box
  have hεB : ε ≤ B := by linarith
  have hJup : ∀ w : WithLp 2 (F × ℝ), ‖(ofLp w).1‖ ≤ B → |(ofLp w).2| ≤ B → 0 < (ofLp w).2 →
      JGap v κ ε w ≤ C₁ * L ^ 4 := by
    intro w hx ht hpos
    have h1 := JUpperBound C₀ κ hC₀ hκ.le v hv hcent hJbd ε w hε0 hpos
    have h2 := (hC₁ v hv (Or.inr hcent) B hB2 w hx ht).1 ε hε0 hεB
    rw [hL]
    linarith [h2.1, h2.2]
  have hJupb : ∀ w : WithLp 2 (F × ℝ), ‖(ofLp w).1‖ ≤ R + 1 → d - ε ≤ (ofLp w).2 →
      (ofLp w).2 ≤ (T : ℝ) + ε → JGap v κ ε w ≤ C₁ * L ^ 4 := by
    intro w hx ht1 ht2
    refine hJup _ ?_ ?_ (by linarith)
    · rw [hB]; linarith
    · rw [abs_le, hB]
      constructor
      · linarith
      · linarith
  have hJupz : ∀ (n : ℕ) (ω : Ω), JGap v κ ε (z n ω) ≤ C₁ * L ^ 4 :=
    fun n ω => hJupb _ (hxb n ω) (htb n ω).1 (htb n ω).2
  -- ## the lower bound for `J_ε` on the box and the continuity of its time retract
  -- both are `JGapLowerBoundAndContinuity`, which sees only the fit class, the envelope
  -- and the scales `R + 1`, `T`, `d`, `ε`; `Lam0` is the constant it produces.
  obtain ⟨Lam0, hLam00, hJlow, hJretr⟩ :=
    JGapLowerBoundAndContinuity C₀ κ hC₀ v hv hcent hWcont hWgrow (R + 1) (T : ℝ) d ε
      (by linarith only [hR]) (Nat.cast_nonneg T) hd0 hdle hε0 hεd
  have hc1 : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).1) := by fun_prop
  have hc2 : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) := by fun_prop
  set Jr : WithLp 2 (F × ℝ) → ℝ :=
    fun w => JGap v κ ε (toLp 2 ((ofLp w).1, max (ofLp w).2 (d / 2))) with hJrdef
  have hJreq : ∀ w : WithLp 2 (F × ℝ), d / 2 ≤ (ofLp w).2 → Jr w = JGap v κ ε w := by
    intro w hw
    simp only [hJrdef]
    have h1 : max (ofLp w).2 (d / 2) = (ofLp w).2 := max_eq_left hw
    rw [h1]
  have hJzSM : ∀ n, StronglyMeasurable[𝒢 n] (fun ω => JGap v κ ε (z n ω)) := by
    intro n
    have heq : (fun ω => JGap v κ ε (z n ω))
        = fun ω => JGap v κ ε (toLp 2 ((ofLp (z n ω)).1, max (ofLp (z n ω)).2 (d / 2))) := by
      funext ω
      have h1 : max (ofLp (z n ω)).2 (d / 2) = (ofLp (z n ω)).2 :=
        max_eq_left (by linarith [(htb n ω).1])
      rw [h1]
    rw [heq]
    exact hJretr.comp_stronglyMeasurable (hzSM n)
  -- ## the error terms
  set En : ℕ → Ω → ℝ := fun n ω =>
    ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
      + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2 with hEndef
  have hEn0 : ∀ (n : ℕ) (ω : Ω), 0 ≤ En n ω := by
    intro n ω
    rw [hEndef]
    positivity
  have hEnSM : ∀ n, StronglyMeasurable[𝒢 n] (En n) := by
    intro n
    have hx : StronglyMeasurable[𝒢 n] (fun ω => (ofLp (z n ω)).1) :=
      hc1.comp_stronglyMeasurable (hzSM n)
    have hxp : StronglyMeasurable[𝒢 n] (fun ω => (ofLp (zp n ω)).1) :=
      hc1.comp_stronglyMeasurable (hzpSM n)
    have hxm : StronglyMeasurable[𝒢 n] (fun ω => (ofLp (zm n ω)).1) :=
      hc1.comp_stronglyMeasurable (hzmSM n)
    have h1 : StronglyMeasurable[𝒢 n]
        (fun ω => ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖) :=
      (((hxp.sub hx).const_smul ε⁻¹).sub (hQSM n)).norm
    have h2 : StronglyMeasurable[𝒢 n]
        (fun ω => ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖) :=
      (((hx.sub hxm).const_smul ε⁻¹).sub (hQSM n)).norm
    have h3 : ∀ a : ℝ, a ^ 2 = a * a := fun a => sq a
    rw [hEndef]
    simp only [h3]
    exact (h1.mul h1).add (h2.mul h2)
  have hJlowz : ∀ (n : ℕ) (ω : Ω), -Lam0 ≤ JGap v κ ε (z n ω) :=
    fun n ω => hJlow _ (hxb n ω) (htb n ω).1 (htb n ω).2
  -- ## the sign events
  have hξbd : ∀ (n : ℕ) (ω : Ω), ‖ξ n ω‖ = 1 := by
    intro n ω
    rcases hξpm n ω with h | h <;> rw [h] <;> simp
  have hξintg : ∀ n : ℕ, Integrable (ξ n) μ := by
    intro n
    refine Integrable.mono' (integrable_const (1 : ℝ))
      (((hξsm n).mono (𝒢.le (n + 1))).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall (fun ω => le_of_eq (hξbd n ω))
  have hτle : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | τ ω ≤ n} := by
    intro n
    have h1 : MeasurableSet[𝒢 n] {ω | ((τ ω : ℕ∞)) ≤ (n : ℕ∞)} := hτst n
    have heq : {ω | ((τ ω : ℕ∞)) ≤ (n : ℕ∞)} = {ω | τ ω ≤ n} := by
      ext ω
      show ((τ ω : ℕ∞)) ≤ (n : ℕ∞) ↔ τ ω ≤ n
      exact Nat.cast_le
    rw [heq] at h1
    exact h1
  have hτgt : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | n < τ ω} := by
    intro n
    have heq : {ω | n < τ ω} = {ω | τ ω ≤ n}ᶜ := by
      ext ω
      show n < τ ω ↔ ¬ (τ ω ≤ n)
      exact not_le.symm
    rw [heq]
    exact (hτle n).compl
  have hzero : ∀ (n : ℕ) (b : ℝ) (S : Set Ω), (b = 1 ∨ b = -1) → MeasurableSet[𝒢 n] S →
      S ∩ {ω | ξ n ω = b} = ∅ → μ S = 0 := by
    intro n b S hb hS hempty
    have hSm : MeasurableSet S := 𝒢.le n _ hS
    have h1 : ∫ ω in S, ξ n ω ∂μ = 0 := by
      have h2 := setIntegral_condExp (𝒢.le n) (hξintg n) hS
      rw [← h2]
      have h3 : ∀ᵐ ω ∂μ, (μ[ξ n|𝒢 n]) ω = 0 := hξce n
      calc ∫ ω in S, (μ[ξ n|𝒢 n]) ω ∂μ = ∫ _ω in S, (0 : ℝ) ∂μ := by
            refine setIntegral_congr_ae hSm ?_
            filter_upwards [h3] with ω hω _
            exact hω
        _ = 0 := by simp
    have h4 : ∀ ω ∈ S, ξ n ω = -b := by
      intro ω hω
      have hne : ξ n ω ≠ b := by
        intro hc
        have hmem : ω ∈ S ∩ {ω | ξ n ω = b} := ⟨hω, hc⟩
        rw [hempty] at hmem
        exact hmem
      rcases hb with hb1 | hb1
      · subst hb1
        rcases hξpm n ω with h | h
        · exact absurd h hne
        · exact h
      · subst hb1
        rcases hξpm n ω with h | h
        · rw [h]
          norm_num
        · exact absurd h hne
    have h5 : ∫ ω in S, ξ n ω ∂μ = -b * (μ.real S) := by
      calc ∫ ω in S, ξ n ω ∂μ = ∫ _ω in S, (-b : ℝ) ∂μ :=
            setIntegral_congr_ae hSm (Filter.Eventually.of_forall h4)
        _ = -b * (μ.real S) := by rw [setIntegral_const]; ring
    have hbne : b ≠ 0 := by
      rcases hb with hb1 | hb1 <;> rw [hb1] <;> norm_num
    have h6 : (μ S).toReal = 0 := by
      have h7 : -b * (μ.real S) = 0 := by rw [← h5]; exact h1
      have h8 : μ.real S = 0 := by
        rcases mul_eq_zero.mp h7 with h | h
        · exact absurd (by linarith : b = 0) hbne
        · exact h
      exact h8
    rcases (ENNReal.toReal_eq_zero_iff (μ S)).mp h6 with h | h
    · exact h
    · exact absurd h (measure_ne_top μ S)
  -- ## the two step states satisfy the walk's bounds almost everywhere before the stop
  have hgoodmeas : ∀ (n : ℕ) (y : ℕ → Ω → WithLp 2 (F × ℝ)),
      StronglyMeasurable[𝒢 n] (y n) →
      MeasurableSet[𝒢 n] {ω | ‖(ofLp (y n ω)).1‖ ≤ R + 1 ∧
        (ofLp (y n ω)).2 ∈ Set.Icc (d - ε) ((T : ℝ) + ε)} := by
    intro n y hy
    have hm1 : Measurable[𝒢 n] (fun ω => ‖(ofLp (y n ω)).1‖) :=
      ((hc1.comp_stronglyMeasurable hy).norm).measurable
    have hm2 : Measurable[𝒢 n] (fun ω => (ofLp (y n ω)).2) :=
      (hc2.comp_stronglyMeasurable hy).measurable
    have heq : {ω | ‖(ofLp (y n ω)).1‖ ≤ R + 1 ∧
          (ofLp (y n ω)).2 ∈ Set.Icc (d - ε) ((T : ℝ) + ε)}
        = ((fun ω => ‖(ofLp (y n ω)).1‖) ⁻¹' (Set.Iic (R + 1)))
            ∩ ((fun ω => (ofLp (y n ω)).2) ⁻¹' (Set.Icc (d - ε) ((T : ℝ) + ε))) := by
      ext ω
      exact Iff.rfl
    rw [heq]
    exact (hm1 measurableSet_Iic).inter (hm2 measurableSet_Icc)
  have hstepb : ∀ (b : ℝ) (y : ℕ → Ω → WithLp 2 (F × ℝ)), (b = 1 ∨ b = -1) →
      (∀ n, StronglyMeasurable[𝒢 n] (y n)) →
      (∀ (n : ℕ) (ω : Ω), n < τ ω → ξ n ω = b → z (n + 1) ω = y n ω) →
      ∀ n : ℕ, ∀ᵐ ω ∂μ, n < τ ω →
        (‖(ofLp (y n ω)).1‖ ≤ R + 1 ∧
          (ofLp (y n ω)).2 ∈ Set.Icc (d - ε) ((T : ℝ) + ε)) := by
    intro b y hb hySM hsel n
    set G : Set Ω := {ω | ‖(ofLp (y n ω)).1‖ ≤ R + 1 ∧
      (ofLp (y n ω)).2 ∈ Set.Icc (d - ε) ((T : ℝ) + ε)} with hG
    have hGm : MeasurableSet[𝒢 n] G := hgoodmeas n y (hySM n)
    have hSz : μ ({ω | n < τ ω} ∩ Gᶜ) = 0 := by
      refine hzero n b _ hb ((hτgt n).inter hGm.compl) ?_
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
      intro hmem hx
      obtain ⟨hlt, hnot⟩ := hmem
      have hlt' : n < τ ω := hlt
      have hx' : ξ n ω = b := hx
      refine hnot ?_
      have h1 : z (n + 1) ω = y n ω := hsel n ω hlt' hx'
      rw [hG]
      refine ⟨?_, ?_, ?_⟩
      · rw [← h1]; exact hxb (n + 1) ω
      · rw [← h1]; exact (htb (n + 1) ω).1
      · rw [← h1]; exact (htb (n + 1) ω).2
    rw [ae_iff]
    refine measure_mono_null ?_ hSz
    intro ω hω
    simp only [Set.mem_ofPred_eq, Classical.not_imp] at hω
    exact ⟨hω.1, hω.2⟩
  have hzpb := hstepb 1 zp (Or.inl rfl) hzpSM (by
    intro n ω hlt hx
    rw [hrec n ω, if_pos hlt, if_pos hx])
  have hzmb := hstepb (-1) zm (Or.inr rfl) hzmSM (by
    intro n ω hlt hx
    have hne : ξ n ω ≠ 1 := by rw [hx]; norm_num
    rw [hrec n ω, if_pos hlt, if_neg hne])
  -- ## the one-step drift along the walk
  have hdrift : ∀ (n : ℕ) (ω : Ω), n < τ ω →
      c * En n ω ≤ (JGap v κ ε (zp n ω) + JGap v κ ε (zm n ω)) / 2 - JGap v κ ε (z n ω) := by
    intro n ω hn
    have hlv := hlive n ω hn
    have hεt : ε < (ofLp (z n ω)).2 := by
      have h1 := hlv.1
      linarith
    have hDP := DPDrift C₀ κ hC₀ hκ.le v hv hcent hJbd ε hε0 (z n ω) (zp n ω) (zm n ω) hεt
      (hstep n ω hn) (Q₀ n ω) (hgradc n ω) _ _ _ _ rfl rfl rfl rfl
    have h6 := hDP.2.2.2.2.2.1
    have h7 := hDP.2.2.2.2.2.2
    rw [hcdef, hEndef]
    linarith
  set Lam : ℝ := C₁ * L ^ 4 + Lam0 with hLamdef
  have hLam0nn : 0 ≤ Lam := by
    rw [hLamdef]
    have h2 : (0:ℝ) < C₁ * L ^ 4 := by positivity
    linarith
  have hEb : ∀ n : ℕ, ∀ᵐ ω ∂μ, n < τ ω → c * En n ω ≤ Lam := by
    intro n
    filter_upwards [hzpb n, hzmb n] with ω h1 h2 hn
    have hd1 := hdrift n ω hn
    have hJp : JGap v κ ε (zp n ω) ≤ C₁ * L ^ 4 := hJupb _ (h1 hn).1 (h1 hn).2.1 (h1 hn).2.2
    have hJm : JGap v κ ε (zm n ω) ≤ C₁ * L ^ 4 := hJupb _ (h2 hn).1 (h2 hn).2.1 (h2 hn).2.2
    have hJz : -Lam0 ≤ JGap v κ ε (z n ω) := hJlowz n ω
    rw [hLamdef]
    linarith
  have hEball : ∀ᵐ ω ∂μ, ∀ n : ℕ, n < τ ω → c * En n ω ≤ Lam := ae_all_iff.mpr hEb
  -- ## the drift submartingale
  set Mp : ℕ → Ω → ℝ := fun n ω =>
    JGap v κ ε (z n ω) - c * ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0) with hMpdef
  have hsumSM : ∀ n : ℕ, StronglyMeasurable[𝒢 n]
      (fun ω => ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0)) := by
    intro n
    refine Finset.stronglyMeasurable_fun_sum _ (fun k hk => ?_)
    have hkn : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    refine StronglyMeasurable.ite ?_ ?_ stronglyMeasurable_const
    · exact 𝒢.mono hkn _ (hτgt k)
    · exact (hEnSM k).mono (𝒢.mono hkn)
  have hMpSM : ∀ n : ℕ, StronglyMeasurable[𝒢 n] (Mp n) := by
    intro n
    rw [hMpdef]
    exact (hJzSM n).sub ((hsumSM n).const_mul c)
  have hJrz : ∀ (n : ℕ) (ω : Ω), Jr (z n ω) = JGap v κ ε (z n ω) :=
    fun n ω => hJreq _ (by linarith [(htb n ω).1])
  have hJrSM : ∀ (n : ℕ) (y : ℕ → Ω → WithLp 2 (F × ℝ)), StronglyMeasurable[𝒢 n] (y n) →
      StronglyMeasurable[𝒢 n] (fun ω => Jr (y n ω)) :=
    fun n y hy => hJretr.comp_stronglyMeasurable hy
  have hMpint : ∀ n : ℕ, Integrable (Mp n) μ := by
    intro n
    refine Integrable.mono' (integrable_const (max (C₁ * L ^ 4) Lam0 + c * n * (Lam / c)))
      ((hMpSM n).mono (𝒢.le n)).aestronglyMeasurable ?_
    filter_upwards [hEball] with ω hω
    have h1 : JGap v κ ε (z n ω) ≤ max (C₁ * L ^ 4) Lam0 :=
      le_trans (hJupz n ω) (le_max_left _ _)
    have h2 : -(max (C₁ * L ^ 4) Lam0) ≤ JGap v κ ε (z n ω) :=
      le_trans (neg_le_neg (le_max_right _ _)) (hJlowz n ω)
    have h3 : 0 ≤ ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0) := by
      refine Finset.sum_nonneg (fun k _ => ?_)
      by_cases hk : k < τ ω
      · rw [if_pos hk]
        exact hEn0 k ω
      · rw [if_neg hk]
    have h4 : ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0) ≤ n * (Lam / c) := by
      have h5 : ∀ k ∈ Finset.range n, (if k < τ ω then En k ω else 0) ≤ Lam / c := by
        intro k _
        by_cases hk : k < τ ω
        · rw [if_pos hk]
          have h6 := hω k hk
          rw [le_div_iff₀ hc0]
          linarith
        · rw [if_neg hk]
          positivity
      calc ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0)
          ≤ ∑ _k ∈ Finset.range n, (Lam / c) := Finset.sum_le_sum h5
        _ = n * (Lam / c) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Real.norm_eq_abs, abs_le]
    rw [hMpdef]
    constructor
    · have h7 : c * ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0) ≤ c * (n * (Lam / c)) :=
        mul_le_mul_of_nonneg_left h4 hc0.le
      have h8 : c * (n * (Lam / c)) = c * n * (Lam / c) := by ring
      linarith
    · have h9 : 0 ≤ c * ∑ k ∈ Finset.range n, (if k < τ ω then En k ω else 0) :=
        mul_nonneg hc0.le h3
      have h10 : (0:ℝ) ≤ c * n * (Lam / c) := by positivity
      linarith
  -- ## the one-step decomposition
  set Ap : ℕ → Ω → ℝ := fun n ω => if n < τ ω then
      ((Jr (zp n ω) + Jr (zm n ω)) / 2 - Jr (z n ω) - c * En n ω) else 0 with hApdef
  set Dp : ℕ → Ω → ℝ := fun n ω => if n < τ ω then
      ((Jr (zp n ω) - Jr (zm n ω)) / 2) else 0 with hDpdef
  have hApSM : ∀ n : ℕ, StronglyMeasurable[𝒢 n] (Ap n) := by
    intro n
    rw [hApdef]
    refine StronglyMeasurable.ite (hτgt n) ?_ stronglyMeasurable_const
    have ha : StronglyMeasurable[𝒢 n] (fun ω => (Jr (zp n ω) + Jr (zm n ω)) / 2) :=
      ((hJrSM n zp (hzpSM n)).add (hJrSM n zm (hzmSM n))).div
        (stronglyMeasurable_const : StronglyMeasurable[𝒢 n] (fun _ : Ω => (2 : ℝ)))
    have hb : StronglyMeasurable[𝒢 n] (fun ω => Jr (z n ω) + c * En n ω) :=
      (hJrSM n z (hzSM n)).add ((hEnSM n).const_mul c)
    have heq : (fun ω => (Jr (zp n ω) + Jr (zm n ω)) / 2 - Jr (z n ω) - c * En n ω)
        = fun ω => (Jr (zp n ω) + Jr (zm n ω)) / 2 - (Jr (z n ω) + c * En n ω) := by
      funext ω
      ring
    rw [heq]
    exact ha.sub hb
  have hDpSM : ∀ n : ℕ, StronglyMeasurable[𝒢 n] (Dp n) := by
    intro n
    rw [hDpdef]
    refine StronglyMeasurable.ite (hτgt n) ?_ stronglyMeasurable_const
    exact ((hJrSM n zp (hzpSM n)).sub (hJrSM n zm (hzmSM n))).div
      (stronglyMeasurable_const : StronglyMeasurable[𝒢 n] (fun _ : Ω => (2 : ℝ)))
  have hdiff : ∀ n : ℕ, ∀ ω : Ω, Mp (n + 1) ω - Mp n ω = Ap n ω + Dp n ω * ξ n ω := by
    intro n ω
    rw [hMpdef, hApdef, hDpdef]
    by_cases hn : n < τ ω
    · simp only [if_pos hn]
      rw [Finset.sum_range_succ, if_pos hn]
      have hJn1 : JGap v κ ε (z (n + 1) ω)
          = (Jr (zp n ω) + Jr (zm n ω)) / 2
            + (Jr (zp n ω) - Jr (zm n ω)) / 2 * ξ n ω := by
        rcases hξpm n ω with hx | hx
        · have h1 : z (n + 1) ω = zp n ω := by rw [hrec n ω, if_pos hn, if_pos hx]
          rw [h1, hx, ← hJreq (zp n ω) ?_]
          · ring
          · rw [← h1]
            linarith [(htb (n + 1) ω).1]
        · have hne : ξ n ω ≠ 1 := by rw [hx]; norm_num
          have h1 : z (n + 1) ω = zm n ω := by rw [hrec n ω, if_pos hn, if_neg hne]
          rw [h1, hx, ← hJreq (zm n ω) ?_]
          · ring
          · rw [← h1]
            linarith [(htb (n + 1) ω).1]
      rw [hJn1, ← hJrz n ω]
      ring
    · simp only [if_neg hn]
      have h1 : z (n + 1) ω = z n ω := by rw [hrec n ω, if_neg hn]
      rw [Finset.sum_range_succ, if_neg hn, h1]
      ring
  have hApnn : ∀ n : ℕ, 0 ≤ᵐ[μ] Ap n := by
    intro n
    filter_upwards [hzpb n, hzmb n] with ω h1 h2
    simp only [Pi.zero_apply, hApdef]
    by_cases hn : n < τ ω
    · simp only [if_pos hn]
      have hp1 : Jr (zp n ω) = JGap v κ ε (zp n ω) := hJreq _ (by linarith [(h1 hn).2.1])
      have hm1 : Jr (zm n ω) = JGap v κ ε (zm n ω) := hJreq _ (by linarith [(h2 hn).2.1])
      have hd1 := hdrift n ω hn
      rw [hp1, hm1, hJrz n ω]
      linarith
    · simp only [if_neg hn]
      exact le_refl 0
  have hDpbd : ∀ n : ℕ, ∀ᵐ ω ∂μ, ‖Dp n ω‖ ≤ max (C₁ * L ^ 4) Lam0 := by
    intro n
    filter_upwards [hzpb n, hzmb n] with ω h1 h2
    rw [hDpdef]
    by_cases hn : n < τ ω
    · simp only [if_pos hn]
      have hp1 : Jr (zp n ω) = JGap v κ ε (zp n ω) := hJreq _ (by linarith [(h1 hn).2.1])
      have hm1 : Jr (zm n ω) = JGap v κ ε (zm n ω) := hJreq _ (by linarith [(h2 hn).2.1])
      have hpu : JGap v κ ε (zp n ω) ≤ C₁ * L ^ 4 := hJupb _ (h1 hn).1 (h1 hn).2.1 (h1 hn).2.2
      have hmu : JGap v κ ε (zm n ω) ≤ C₁ * L ^ 4 := hJupb _ (h2 hn).1 (h2 hn).2.1 (h2 hn).2.2
      have hpl : -Lam0 ≤ JGap v κ ε (zp n ω) := hJlow _ (h1 hn).1 (h1 hn).2.1 (h1 hn).2.2
      have hml : -Lam0 ≤ JGap v κ ε (zm n ω) := hJlow _ (h2 hn).1 (h2 hn).2.1 (h2 hn).2.2
      have hmx1 : C₁ * L ^ 4 ≤ max (C₁ * L ^ 4) Lam0 := le_max_left _ _
      have hmx2 : Lam0 ≤ max (C₁ * L ^ 4) Lam0 := le_max_right _ _
      rw [hp1, hm1, Real.norm_eq_abs, abs_le]
      constructor
      · linarith
      · linarith
    · simp only [if_neg hn]
      have : (0:ℝ) ≤ max (C₁ * L ^ 4) Lam0 := le_trans hLam00 (le_max_right _ _)
      simpa using this
  have hApint : ∀ n : ℕ, Integrable (Ap n) μ := by
    intro n
    have h1 : Ap n = fun ω => (Mp (n + 1) ω - Mp n ω) - Dp n ω * ξ n ω := by
      funext ω
      rw [hdiff n ω]
      ring
    rw [h1]
    refine Integrable.sub ((hMpint (n + 1)).sub (hMpint n)) ?_
    refine Integrable.mono' (integrable_const (max (C₁ * L ^ 4) Lam0 * 1))
      (((hDpSM n).mono (𝒢.le n)).aestronglyMeasurable.mul
        (((hξsm n).mono (𝒢.le (n + 1))).aestronglyMeasurable)) ?_
    filter_upwards [hDpbd n] with ω hω
    rw [Real.norm_eq_abs, abs_mul]
    have h2 : |ξ n ω| = 1 := by
      have := hξbd n ω
      rwa [Real.norm_eq_abs] at this
    rw [h2]
    have h3 : |Dp n ω| ≤ max (C₁ * L ^ 4) Lam0 := by
      have := hω
      rwa [Real.norm_eq_abs] at this
    linarith
  have hsub : Submartingale Mp 𝒢 μ := by
    refine submartingale_of_condExp_sub_nonneg_nat (fun n => hMpSM n) hMpint (fun n => ?_)
    have h1 : Mp (n + 1) - Mp n = Ap n + Dp n * ξ n := by
      funext ω
      exact hdiff n ω
    rw [h1]
    have h2 : μ[Ap n + Dp n * ξ n|𝒢 n] =ᵐ[μ] μ[Ap n|𝒢 n] + μ[Dp n * ξ n|𝒢 n] :=
      condExp_add (hApint n) (by
        refine Integrable.mono' (integrable_const (max (C₁ * L ^ 4) Lam0 * 1))
          (((hDpSM n).mono (𝒢.le n)).aestronglyMeasurable.mul
            (((hξsm n).mono (𝒢.le (n + 1))).aestronglyMeasurable)) ?_
        filter_upwards [hDpbd n] with ω hω
        rw [Real.norm_eq_abs, Pi.mul_apply, abs_mul]
        have h2 : |ξ n ω| = 1 := by
          have := hξbd n ω
          rwa [Real.norm_eq_abs] at this
        rw [h2]
        have h3 : |Dp n ω| ≤ max (C₁ * L ^ 4) Lam0 := by
          have := hω
          rwa [Real.norm_eq_abs] at this
        linarith) _
    have h3 : μ[Ap n|𝒢 n] = Ap n :=
      condExp_of_stronglyMeasurable (𝒢.le n) (hApSM n) (hApint n)
    have h4 : μ[Dp n * ξ n|𝒢 n] =ᵐ[μ] Dp n * μ[ξ n|𝒢 n] :=
      condExp_stronglyMeasurable_mul_of_bound (𝒢.le n) (hDpSM n) (hξintg n)
        (max (C₁ * L ^ 4) Lam0) (hDpbd n)
    filter_upwards [h2, h4, hApnn n, hξce n] with ω e2 e4 e5 e6
    rw [e2]
    simp only [Pi.add_apply]
    rw [h3, e4]
    simp only [Pi.mul_apply, e6, Pi.zero_apply, mul_zero, add_zero]
    simpa using e5
  -- ## the two budgets, by optional stopping
  -- the whole measure-theoretic tail is `OptionalStoppingErrorBudget`, stated for an
  -- abstract submartingale: here `J n ω = JGap v κ ε (z n ω)` and `E = En`, the walk and
  -- the ambient space playing no part in it.  Its budget carries the symbolic numerator
  -- `Ju - J0`, which is specialized to the paper's constant below.
  obtain ⟨hconc1, hSτint, hSτbd⟩ :=
    OptionalStoppingErrorBudget μ 𝒢 (fun n ω => JGap v κ ε (z n ω)) En τ c
      (JGap v κ ε (toLp 2 ((0 : F), (1 : ℝ)))) Lam (C₁ * L ^ 4) Lam0 hc0
      (by rw [hLamdef]; exact add_nonneg (mul_nonneg hC₁0.le (by positivity)) hLam00)
      hJzSM hEnSM hEn0 hτst (fun ω => by rw [hz0 ω]) hJupz hJlowz hEball hsub
  refine ⟨hconc1, hSτint, ?_⟩
  -- `(C₁ L⁴ - J_ε(z_*)) / c ≤ (C₁ + |H| + 1) / c * L⁴`, by `hstart` and `1 ≤ L⁴`
  have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL1
  have h7 : -H ≤ |H| := neg_le_abs H
  have h8 : (0 : ℝ) ≤ |H| := abs_nonneg H
  refine le_trans hSτbd ?_
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hc0]
  have h9 : (0 : ℝ) ≤ (|H| + 1) * (L ^ 4 - 1) :=
    mul_nonneg (by linarith only [h8]) (by linarith only [hL4])
  linarith only [hstart, h7, h9]
