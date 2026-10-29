import InfHarmonic.IsContactWalk
import InfHarmonic.IsMarkData
import InfHarmonic.IsFitClass
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.7, part 3: a stopped contact walk whose state at each index
takes only countably many values carries mark data — for each level `j ≤ N` the
mark index `σ_j`, together with a fit of radius `2⁻ʲ` at the mark, chosen so that
the parameters are adapted to the stopped σ-algebra. -/
theorem ContactWalkMarkData (C₀ κ H : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (T : ℕ) (R : ℝ) (N : ℕ) (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω)
    (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
    (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ) :
    IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ →
    (∀ n : ℕ, (Set.range (z n)).Countable) →
    ∃ (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (aj : ℕ → Ω → ℝ),
      IsMarkData C₀ v N 𝒢 z τ smark pj aj := by
  classical
  intro hcw hcount
  obtain ⟨hμ1, hεk, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
    hstep, hrec, hgradc, hτst, hτint, hlive, hexit, hxbd, hstart⟩ := hcw
  -- `Ω` is nonempty, because `μ` is a probability measure
  have hne : Nonempty Ω := by
    rcases Set.eq_empty_or_nonempty (Set.univ : Set Ω) with h | h
    · exfalso
      rw [h] at hμ1
      simp at hμ1
    · exact ⟨h.choose⟩
  -- the time coordinate and the level sets of the walk
  have hc1 : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).1) := by fun_prop
  have hc2 : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) := by fun_prop
  have htmeas : ∀ i : ℕ, Measurable[𝒢 i] (fun ω => (ofLp (z i ω)).2) :=
    fun i => (hc2.comp_stronglyMeasurable (hzSM i)).measurable
  have hzeq : ∀ (i : ℕ) (c : WithLp 2 (F × ℝ)), MeasurableSet[𝒢 i] {ω | z i ω = c} :=
    fun i c => (hzSM i).measurableSet_eq_fun stronglyMeasurable_const
  -- a measurable coding of the countably many states the walk can occupy at time `i`
  have hcode : ∀ i : ℕ, ∃ (e : ℕ → WithLp 2 (F × ℝ)) (cd : Ω → ℕ),
      Measurable[𝒢 i] cd ∧ ∀ ω, e (cd ω) = z i ω := by
    intro i
    obtain ⟨e, he⟩ := (hcount i).exists_eq_range ⟨z i (Classical.arbitrary Ω), ⟨_, rfl⟩⟩
    have hex : ∀ ω, ∃ m, e m = z i ω := by
      intro ω
      have h1 : z i ω ∈ Set.range (z i) := ⟨ω, rfl⟩
      rw [he] at h1
      obtain ⟨m, hm⟩ := h1
      exact ⟨m, hm⟩
    refine ⟨e, fun ω => Nat.find (hex ω), ?_, fun ω => Nat.find_spec (hex ω)⟩
    refine @measurable_to_countable' ℕ Ω _ _ (𝒢 i) _ (fun m => ?_)
    have heq : {ω | Nat.find (hex ω) = m}
        = {ω | z i ω = e m} ∩ ⋂ m' ∈ Finset.range m, {ω | z i ω = e m'}ᶜ := by
      ext ω
      show Nat.find (hex ω) = m ↔ _
      rw [Nat.find_eq_iff]
      constructor
      · intro h
        refine ⟨h.1.symm, ?_⟩
        refine Set.mem_iInter₂.2 (fun m' hm' => ?_)
        have h2 := h.2 m' (Finset.mem_range.mp hm')
        intro hc
        exact h2 hc.symm
      · intro h
        refine ⟨h.1.symm, fun m' hm' hc => ?_⟩
        have h3 := Set.mem_iInter₂.1 h.2 m' (Finset.mem_range.mpr hm')
        exact h3 hc.symm
    show MeasurableSet[𝒢 i] {ω | Nat.find (hex ω) = m}
    rw [heq]
    refine MeasurableSet.inter (hzeq i (e m)) ?_
    exact MeasurableSet.biInter (Finset.range m).countable_toSet
      (fun m' _ => (hzeq i (e m')).compl)
  -- any function of the state at a fixed time is adapted
  have hselSM : ∀ (i : ℕ) (g : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ)),
      StronglyMeasurable[𝒢 i] (fun ω => g (z i ω)) := by
    intro i g
    obtain ⟨e, cd, hcdmeas, hcdspec⟩ := hcode i
    have hfkSM : ∀ k : ℕ, StronglyMeasurable[𝒢 i]
        (fun ω => ∑ m ∈ Finset.range k,
          Set.indicator {ω | cd ω = m} (fun _ => g (e m)) ω) := by
      intro k
      refine Finset.stronglyMeasurable_fun_sum _ (fun m _ => ?_)
      exact stronglyMeasurable_const.indicator (hcdmeas (measurableSet_singleton m))
    refine stronglyMeasurable_of_tendsto atTop hfkSM (tendsto_pi_nhds.mpr (fun ω => ?_))
    refine tendsto_atTop_of_eventually_const (i₀ := cd ω + 1) (fun k hk => ?_)
    rw [Finset.sum_eq_single_of_mem (cd ω) (Finset.mem_range.mpr (by omega))]
    · have hmem : ω ∈ {ω' | cd ω' = cd ω} := rfl
      rw [Set.indicator_of_mem hmem, hcdspec ω]
    · intro m _ hm
      refine Set.indicator_of_notMem ?_ _
      exact fun hc => hm hc.symm
  -- ## the mark index
  set sm : ℕ → Ω → ℕ := fun j ω =>
    if h : ∃ n, n ≤ τ ω ∧ (ofLp (z n ω)).2 = (1 / 2 : ℝ) ^ j then Nat.find h else τ ω with hsm
  have hsmle : ∀ (j : ℕ) (ω : Ω), sm j ω ≤ τ ω := by
    intro j ω
    simp only [hsm]
    by_cases h : ∃ n, n ≤ τ ω ∧ (ofLp (z n ω)).2 = (1 / 2 : ℝ) ^ j
    · rw [dif_pos h]
      exact (Nat.find_spec h).1
    · rw [dif_neg h]
  have hsmlt : ∀ (j : ℕ) (ω : Ω) (n : ℕ), n < sm j ω →
      n < τ ω ∧ (ofLp (z n ω)).2 ≠ (1 / 2 : ℝ) ^ j := by
    intro j ω n hn
    simp only [hsm] at hn
    by_cases h : ∃ n, n ≤ τ ω ∧ (ofLp (z n ω)).2 = (1 / 2 : ℝ) ^ j
    · rw [dif_pos h] at hn
      have h1 : n < τ ω := lt_of_lt_of_le hn (Nat.find_spec h).1
      have h2 := Nat.find_min h hn
      refine ⟨h1, fun hc => ?_⟩
      exact h2 ⟨le_of_lt h1, hc⟩
    · rw [dif_neg h] at hn
      refine ⟨hn, fun hc => ?_⟩
      exact h ⟨n, le_of_lt hn, hc⟩
  have hsmalt : ∀ (j : ℕ) (ω : Ω),
      sm j ω = τ ω ∨ (ofLp (z (sm j ω) ω)).2 = (1 / 2 : ℝ) ^ j := by
    intro j ω
    by_cases h : ∃ n, n ≤ τ ω ∧ (ofLp (z n ω)).2 = (1 / 2 : ℝ) ^ j
    · refine Or.inr ?_
      have h1 : sm j ω = Nat.find h := by
        simp only [hsm]
        rw [dif_pos h]
      rw [h1]
      exact (Nat.find_spec h).2
    · refine Or.inl ?_
      simp only [hsm]
      rw [dif_neg h]
  -- ## the measurable sets attached to `τ`
  have hτle : ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | τ ω ≤ n} := by
    intro n
    have h1 : MeasurableSet[𝒢 n] {ω | ((τ ω : ℕ∞)) ≤ (n : ℕ∞)} := hτst n
    have heq : {ω | ((τ ω : ℕ∞)) ≤ (n : ℕ∞)} = {ω | τ ω ≤ n} := by
      ext ω
      show ((τ ω : ℕ∞)) ≤ (n : ℕ∞) ↔ τ ω ≤ n
      exact Nat.cast_le
    rw [heq] at h1
    exact h1
  have hτeqset : ∀ k : ℕ, MeasurableSet[𝒢 k] {ω | τ ω = k} := by
    intro k
    have h1 : MeasurableSet[𝒢 k] {ω | ((τ ω : ℕ∞)) = (k : ℕ∞)} :=
      hτst.measurableSet_eq_of_countable k
    have heq : {ω | ((τ ω : ℕ∞)) = (k : ℕ∞)} = {ω | τ ω = k} := by
      ext ω
      show ((τ ω : ℕ∞)) = (k : ℕ∞) ↔ τ ω = k
      exact Nat.cast_inj
    rw [heq] at h1
    exact h1
  have hτge : ∀ m n : ℕ, m ≤ n → MeasurableSet[𝒢 n] {ω | m ≤ τ ω} := by
    intro m n hmn
    have heq : {ω | m ≤ τ ω} = (⋃ k ∈ Finset.range m, {ω | τ ω = k})ᶜ := by
      ext ω
      show m ≤ τ ω ↔ ω ∈ (⋃ k ∈ Finset.range m, {ω | τ ω = k})ᶜ
      constructor
      · intro h hc
        obtain ⟨k, hk, hk2⟩ := Set.mem_iUnion₂.1 hc
        have h1 : k < m := Finset.mem_range.mp hk
        have h2 : τ ω = k := hk2
        omega
      · intro h
        by_contra hc
        refine h (Set.mem_iUnion₂.2 ⟨τ ω, Finset.mem_range.mpr (by omega), rfl⟩)
    rw [heq]
    refine MeasurableSet.compl ?_
    refine MeasurableSet.biUnion (Finset.range m).countable_toSet (fun k hk => ?_)
    have hkm : k ≤ n := by
      have := Finset.mem_range.mp hk
      omega
    exact 𝒢.mono hkm _ (hτeqset k)
  have hsmst : ∀ j : ℕ, IsStoppingTime 𝒢 (fun ω => (sm j ω : ℕ∞)) := by
    intro j n
    show MeasurableSet[𝒢 n] {ω | ((sm j ω : ℕ∞)) ≤ (n : ℕ∞)}
    have heq : {ω | ((sm j ω : ℕ∞)) ≤ (n : ℕ∞)}
        = {ω | τ ω ≤ n} ∪ ⋃ m ∈ Finset.range (n + 1),
            ({ω | m ≤ τ ω} ∩ {ω | (ofLp (z m ω)).2 = (1 / 2 : ℝ) ^ j}) := by
      ext ω
      show ((sm j ω : ℕ∞)) ≤ (n : ℕ∞) ↔ _
      rw [Nat.cast_le]
      constructor
      · intro hle
        by_cases h : ∃ n', n' ≤ τ ω ∧ (ofLp (z n' ω)).2 = (1 / 2 : ℝ) ^ j
        · have h1 : sm j ω = Nat.find h := by
            simp only [hsm]
            rw [dif_pos h]
          refine Or.inr (Set.mem_iUnion₂.2 ⟨Nat.find h, Finset.mem_range.mpr (by omega), ?_⟩)
          exact ⟨(Nat.find_spec h).1, (Nat.find_spec h).2⟩
        · have h1 : sm j ω = τ ω := by
            simp only [hsm]
            rw [dif_neg h]
          exact Or.inl (show τ ω ≤ n by omega)
      · intro hmem
        rcases hmem with h1 | h1
        · have h2 : τ ω ≤ n := h1
          exact le_trans (hsmle j ω) h2
        · obtain ⟨m, hm, hm1, hm2⟩ := Set.mem_iUnion₂.1 h1
          have h : ∃ n', n' ≤ τ ω ∧ (ofLp (z n' ω)).2 = (1 / 2 : ℝ) ^ j := ⟨m, hm1, hm2⟩
          have h2 : sm j ω = Nat.find h := by
            simp only [hsm]
            rw [dif_pos h]
          have h3 : Nat.find h ≤ m := Nat.find_le ⟨hm1, hm2⟩
          have h4 : m ≤ n := by
            have := Finset.mem_range.mp hm
            omega
          omega
    rw [heq]
    refine MeasurableSet.union (hτle n) ?_
    refine MeasurableSet.biUnion (Finset.range (n + 1)).countable_toSet (fun m hm => ?_)
    have hmn : m ≤ n := by
      have := Finset.mem_range.mp hm
      omega
    refine MeasurableSet.inter (hτge m n hmn) ?_
    exact 𝒢.mono hmn _ ((htmeas m) (measurableSet_singleton _))
  have hsmeqset : ∀ (j i : ℕ), MeasurableSet[𝒢 i] {ω | sm j ω = i} := by
    intro j i
    have h1 : MeasurableSet[𝒢 i] {ω | ((sm j ω : ℕ∞)) = (i : ℕ∞)} :=
      (hsmst j).measurableSet_eq_of_countable i
    have heq : {ω | ((sm j ω : ℕ∞)) = (i : ℕ∞)} = {ω | sm j ω = i} := by
      ext ω
      show ((sm j ω : ℕ∞)) = (i : ℕ∞) ↔ sm j ω = i
      exact Nat.cast_inj
    rw [heq] at h1
    exact h1
  -- ## the fit selection at a state
  have hfitex : ∀ (j : ℕ) (w : WithLp 2 (F × ℝ)),
      ∃ pa : F × ℝ, IsFit C₀ v w ((1 / 2 : ℝ) ^ j) pa.1 pa.2 := by
    intro j w
    obtain ⟨p, a, hpa⟩ := hv.2 w ((1 / 2 : ℝ) ^ j) (by positivity)
    exact ⟨(p, a), hpa⟩
  set G : ℕ → WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ) := fun j w =>
    if (ofLp w).2 = (1 / 2 : ℝ) ^ j
      then toLp 2 ((hfitex j w).choose.1, (hfitex j w).choose.2)
      else toLp 2 ((0 : F), (0 : ℝ)) with hG
  set pjf : ℕ → Ω → F := fun j ω => (ofLp (G j (z (sm j ω) ω))).1 with hpjf
  set ajf : ℕ → Ω → ℝ := fun j ω => (ofLp (G j (z (sm j ω) ω))).2 with hajf
  have hfit7 : ∀ (j : ℕ) (ω : Ω), (ofLp (z (sm j ω) ω)).2 = (1 / 2 : ℝ) ^ j →
      IsFit C₀ v (z (sm j ω) ω) ((1 / 2 : ℝ) ^ j) (pjf j ω) (ajf j ω) := by
    intro j ω hw
    have h1 : G j (z (sm j ω) ω)
        = toLp 2 ((hfitex j (z (sm j ω) ω)).choose.1, (hfitex j (z (sm j ω) ω)).choose.2) := by
      simp only [hG]
      rw [if_pos hw]
    simp only [hpjf, hajf, h1, WithLp.ofLp_toLp]
    exact (hfitex j (z (sm j ω) ω)).choose_spec
  have hfit8 : ∀ (j : ℕ) (ω : Ω), (ofLp (z (sm j ω) ω)).2 ≠ (1 / 2 : ℝ) ^ j →
      pjf j ω = 0 ∧ ajf j ω = 0 := by
    intro j ω hw
    have h1 : G j (z (sm j ω) ω) = toLp 2 ((0 : F), (0 : ℝ)) := by
      simp only [hG]
      rw [if_neg hw]
    simp [hpjf, hajf, h1]
  have hmeas56 : ∀ (j n : ℕ), StronglyMeasurable[𝒢 n]
      (fun ω => if sm j ω ≤ n then G j (z (sm j ω) ω) else (0 : WithLp 2 (F × ℝ))) := by
    intro j n
    have heq : (fun ω => if sm j ω ≤ n then G j (z (sm j ω) ω) else (0 : WithLp 2 (F × ℝ)))
        = fun ω => ∑ i ∈ Finset.range (n + 1),
            Set.indicator {ω | sm j ω = i} (fun ω' => G j (z i ω')) ω := by
      funext ω
      by_cases hn : sm j ω ≤ n
      · rw [if_pos hn]
        rw [Finset.sum_eq_single_of_mem (sm j ω) (Finset.mem_range.mpr (by omega))]
        · have hmem : ω ∈ {ω' | sm j ω' = sm j ω} := rfl
          rw [Set.indicator_of_mem hmem]
        · intro i _ hi
          refine Set.indicator_of_notMem ?_ _
          exact fun hc => hi hc.symm
      · rw [if_neg hn]
        refine (Finset.sum_eq_zero (fun i hi => ?_)).symm
        refine Set.indicator_of_notMem ?_ _
        intro hc
        have h1 : sm j ω = i := hc
        have h2 : i < n + 1 := Finset.mem_range.mp hi
        omega
    rw [heq]
    refine Finset.stronglyMeasurable_fun_sum _ (fun i hi => ?_)
    have hin : i ≤ n := by
      have := Finset.mem_range.mp hi
      omega
    exact ((hselSM i (G j)).mono (𝒢.mono hin)).indicator (𝒢.mono hin _ (hsmeqset j i))
  have hconj5 : ∀ (j n : ℕ), StronglyMeasurable[𝒢 n]
      (fun ω => if sm j ω ≤ n then pjf j ω else (0 : F)) := by
    intro j n
    have heq : (fun ω => if sm j ω ≤ n then pjf j ω else (0 : F))
        = fun ω => (ofLp (if sm j ω ≤ n then G j (z (sm j ω) ω)
            else (0 : WithLp 2 (F × ℝ)))).1 := by
      funext ω
      by_cases hn : sm j ω ≤ n
      · rw [if_pos hn, if_pos hn, hpjf]
      · rw [if_neg hn, if_neg hn]
        simp
    rw [heq]
    exact hc1.comp_stronglyMeasurable (hmeas56 j n)
  have hconj6 : ∀ (j n : ℕ), StronglyMeasurable[𝒢 n]
      (fun ω => if sm j ω ≤ n then ajf j ω else (0 : ℝ)) := by
    intro j n
    have heq : (fun ω => if sm j ω ≤ n then ajf j ω else (0 : ℝ))
        = fun ω => (ofLp (if sm j ω ≤ n then G j (z (sm j ω) ω)
            else (0 : WithLp 2 (F × ℝ)))).2 := by
      funext ω
      by_cases hn : sm j ω ≤ n
      · rw [if_pos hn, if_pos hn, hajf]
      · rw [if_neg hn, if_neg hn]
        simp
    rw [heq]
    exact hc2.comp_stronglyMeasurable (hmeas56 j n)
  -- ## the assembly
  refine ⟨sm, pjf, ajf, ?_⟩
  intro j hj1 hjN
  exact ⟨hsmst j, fun ω => hsmle j ω, fun ω n hn => hsmlt j ω n hn, fun ω => hsmalt j ω,
    fun n => hconj5 j n, fun n => hconj6 j n, fun ω hw => hfit7 j ω hw, fun ω hw => hfit8 j ω hw⟩
