import InfHarmonic.IsBaryConfig
import Mathlib.Analysis.Convex.Caratheodory
open Set

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 4 of Lemma 5.2, the finite-combination half (Claim B): in a
finite-dimensional space every point of the convex hull of a set `E` is the mean of
a finite horizontal probability configuration, with strictly positive weights,
supported in `E`; and the convex hull of a compact set is compact. -/
theorem BaryConfigOfConvexHull (E : Set F) :
    (∀ x ∈ convexHull ℝ E, ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
        IsBaryConfig n θ y x ∧ ∀ i, y i ∈ E) ∧
    (IsCompact E → IsCompact (convexHull ℝ E)) := by
  constructor
  · -- Clause (1): Caratheodory in positive-weight form, reindexed onto `Fin n`.
    intro x hx
    obtain ⟨ι, _, z, w, hzE, _hai, hwpos, hwsum, hwx⟩ :=
      eq_pos_convex_span_of_mem_convexHull hx
    refine ⟨Fintype.card ι, fun j => w ((Fintype.equivFin ι).symm j),
      fun j => z ((Fintype.equivFin ι).symm j), ⟨fun j => hwpos _, ?_, ?_⟩,
      fun j => hzE (Set.mem_range_self _)⟩
    · rw [(Fintype.equivFin ι).symm.sum_comp w]; exact hwsum
    · rw [(Fintype.equivFin ι).symm.sum_comp (fun i => w i • z i)]; exact hwx
  · -- Clause (2): the hull is a finite union of continuous images of compact sets.
    intro hE
    rcases E.eq_empty_or_nonempty with rfl | ⟨y₀, hy₀⟩
    · simp
    -- Caratheodory bounds the number of points by `finrank + 1`, so the combinations
    -- of at most that many points of `E` exhaust the hull in finitely many strata.
    have key : convexHull ℝ E
        = ⋃ k : Fin (Module.finrank ℝ F + 2),
            (fun p : (Fin (k : ℕ) → ℝ) × (Fin (k : ℕ) → F) => ∑ i, p.1 i • p.2 i) ''
              (stdSimplex ℝ (Fin (k : ℕ)) ×ˢ (Set.univ.pi fun _ : Fin (k : ℕ) => E)) := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨ι, _, z, w, hzE, hai, hwpos, hwsum, hwx⟩ :=
          eq_pos_convex_span_of_mem_convexHull hx
        have hcard : Fintype.card ι ≤ Module.finrank ℝ F + 1 :=
          le_trans hai.card_le_finrank_succ (Nat.add_le_add_right (Submodule.finrank_le _) 1)
        refine Set.mem_iUnion.2 ⟨⟨Fintype.card ι, Nat.lt_succ_of_le hcard⟩, ?_⟩
        refine ⟨⟨fun j => w ((Fintype.equivFin ι).symm j),
          fun j => z ((Fintype.equivFin ι).symm j)⟩, ⟨⟨fun j => (hwpos _).le, ?_⟩, ?_⟩, ?_⟩
        · rw [(Fintype.equivFin ι).symm.sum_comp w]; exact hwsum
        · exact fun j _ => hzE (Set.mem_range_self _)
        · show ∑ j, w ((Fintype.equivFin ι).symm j) • z ((Fintype.equivFin ι).symm j) = x
          rw [(Fintype.equivFin ι).symm.sum_comp (fun i => w i • z i)]; exact hwx
      · refine Set.iUnion_subset fun k => ?_
        rintro x ⟨⟨w, z⟩, ⟨⟨hw0, hw1⟩, hz⟩, rfl⟩
        exact mem_convexHull_of_exists_fintype w z hw0 hw1 (fun i => hz i (Set.mem_univ i)) rfl
    rw [key]
    exact isCompact_iUnion fun k =>
      ((isCompact_stdSimplex ℝ (Fin (k : ℕ))).prod
        (isCompact_univ_pi fun _ => hE)).image (by fun_prop)
