import InfHarmonic.Preamble
-- The project's standing variable block is not used by this statement, which is
-- about an abstract finite measure space, so the unused-section-variable linter
-- is switched off here.
set_option linter.unusedSectionVars false
open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Selection from a sequence of events of uniformly positive measure, with no
independence: if each of the measurable sets `E j`, `j ≥ 1`, has measure at
least a fixed `c > 0` under a finite measure `μ`, and `G` has full measure,
then some point of `G` lies in `E j` for infinitely many `j ≥ 1`. -/
theorem TailEventSelection {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (c : ℝ≥0∞) (hc : 0 < c) (E : ℕ → Set X)
    (hEm : ∀ j, MeasurableSet (E j)) (hE : ∀ j, 1 ≤ j → c ≤ μ (E j))
    (G : Set X) (hG : μ Gᶜ = 0) :
    ∃ x ∈ G, {j : ℕ | 1 ≤ j ∧ x ∈ E j}.Infinite := by
  set U : ℕ → Set X := fun h => ⋃ j, ⋃ _ : h ≤ j, E j with hU
  have hUm : ∀ h, MeasurableSet (U h) := by
    intro h
    exact MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hEm j
  have hUanti : Antitone U := by
    intro a b hab x hx
    simp only [hU, Set.mem_iUnion] at hx ⊢
    obtain ⟨j, hj, hxj⟩ := hx
    exact ⟨j, le_trans hab hj, hxj⟩
  have hUc : ∀ h, c ≤ μ (U h) := by
    intro h
    refine le_trans (hE (max h 1) (le_max_right h 1)) (measure_mono ?_)
    intro x hx
    exact Set.mem_iUnion.mpr ⟨max h 1, Set.mem_iUnion.mpr ⟨le_max_left h 1, hx⟩⟩
  have hinter : c ≤ μ (⋂ h, U h) := by
    rw [hUanti.measure_iInter (fun i => (hUm i).nullMeasurableSet)
      ⟨0, measure_ne_top μ _⟩]
    exact le_iInf hUc
  have hpos : μ ((⋂ h, U h) ∩ G) ≠ 0 := by
    rw [measure_inter_conull hG]
    exact fun h0 => absurd (h0 ▸ hinter) (by simp [hc.ne'])
  obtain ⟨x, hxU, hxG⟩ := nonempty_of_measure_ne_zero hpos
  refine ⟨x, hxG, Set.infinite_of_not_bddAbove ?_⟩
  rintro ⟨b, hb⟩
  have hmemU := Set.mem_iInter.mp hxU (b + 1)
  simp only [hU, Set.mem_iUnion] at hmemU
  obtain ⟨j, hj, hxj⟩ := hmemU
  have hmem : j ∈ {j : ℕ | 1 ≤ j ∧ x ∈ E j} := ⟨by omega, hxj⟩
  have := hb hmem
  omega
