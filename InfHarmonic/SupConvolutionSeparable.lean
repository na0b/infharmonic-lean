module

public import InfHarmonic.SupConvolution

@[expose] public section
open Set MeasureTheory
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The sup-convolution of a separated sum separates: on an `ℓ²`-product the
sup-convolution of `W ↦ ∑ G j (w j)` at `Z` is the sum of the sup-convolutions of
the `G j` at the components of `Z`.  The hypothesis is a uniform upper bound on
the `G j`, which is what makes every defining set bounded above and the suprema
genuine rather than the junk value of an unbounded set. -/
theorem SupConvolutionSeparable (N : ℕ) (ε C : ℝ) (hε : 0 < ε)
    (G : Fin N → E → ℝ) (hGb : ∀ (j : Fin N) (w : E), G j w ≤ C)
    (Z : PiLp 2 (fun _ : Fin N => E)) :
    SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
      = ∑ j, SupConvolution ε (G j) (ofLp Z j) := by
  -- Body-only acknowledgement (trap 2): the instance bundle is part of this node's signature;
  -- the separation argument uses only the ℓ²-norm identity and the order-completeness of ℝ, so
  -- finite-dimensionality is not consumed directly.  (Note it must be acknowledged like THIS and
  -- not by re-`have`ing an `InnerProductSpace ℝ E`, which would duplicate an instance on the
  -- `NormedSpace ℝ E` path and break later `inferInstance` calls.)
  have _ : FiniteDimensional ℝ E := inferInstance
  -- the product objective and the per-factor objectives
  obtain ⟨f, hfdef⟩ : ∃ f : PiLp 2 (fun _ : Fin N => E) → ℝ,
      f = fun W : PiLp 2 (fun _ : Fin N => E) =>
        (∑ j, G j (ofLp W j)) - ‖Z - W‖ ^ 2 / (2 * ε) := ⟨_, rfl⟩
  obtain ⟨fj, hfjdef⟩ : ∃ fj : Fin N → E → ℝ, fj = fun j w =>
      G j w - ‖ofLp Z j - w‖ ^ 2 / (2 * ε) := ⟨_, rfl⟩
  have hL : SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
      = sSup (Set.range f) := by
    rw [hfdef]
    rfl
  have hR : ∀ j : Fin N, SupConvolution ε (G j) (ofLp Z j) = sSup (Set.range (fj j)) := by
    intro j
    rw [hfjdef]
    rfl
  -- THE KEY IDENTITY: the objective separates, because the ℓ²-norm does
  have hsep : ∀ W : PiLp 2 (fun _ : Fin N => E), f W = ∑ j, fj j (ofLp W j) := by
    intro W
    have hnorm : ‖Z - W‖ ^ 2 = ∑ j, ‖ofLp Z j - ofLp W j‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [real_inner_self_eq_norm_sq]
      simp
    rw [hfdef, hfjdef]
    simp only
    rw [hnorm, Finset.sum_div, ← Finset.sum_sub_distrib]
  -- every defining set is nonempty and bounded above
  have hbddj : ∀ j : Fin N, BddAbove (Set.range (fj j)) := by
    intro j
    refine ⟨C, fun y hy => ?_⟩
    obtain ⟨w, rfl⟩ := hy
    rw [hfjdef]
    have hq : (0:ℝ) ≤ ‖ofLp Z j - w‖ ^ 2 / (2 * ε) := by positivity
    simp only
    linarith [hGb j w]
  have hbdd : BddAbove (Set.range f) := by
    refine ⟨(N : ℝ) * C, fun y hy => ?_⟩
    obtain ⟨W, rfl⟩ := hy
    rw [hsep W]
    have h1 : ∀ j : Fin N, fj j (ofLp W j) ≤ C := by
      intro j
      rw [hfjdef]
      have hq : (0:ℝ) ≤ ‖ofLp Z j - ofLp W j‖ ^ 2 / (2 * ε) := by positivity
      simp only
      linarith [hGb j (ofLp W j)]
    calc ∑ j, fj j (ofLp W j) ≤ ∑ _j : Fin N, C := Finset.sum_le_sum (fun j _ => h1 j)
      _ = (N : ℝ) * C := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hL]
  refine le_antisymm ?_ ?_
  · -- the supremum of the sum is at most the sum of the suprema
    refine csSup_le ⟨f 0, ⟨0, rfl⟩⟩ (fun y hy => ?_)
    obtain ⟨W, rfl⟩ := hy
    rw [hsep W]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [hR j]
    exact le_csSup (hbddj j) ⟨ofLp W j, rfl⟩
  · -- and at least, by choosing each factor within θ/N of its supremum
    refine le_of_forall_pos_le_add (fun θ hθ => ?_)
    rcases Nat.eq_zero_or_pos N with hN0 | hN
    · subst hN0
      have hZ0 : Z = 0 := Subsingleton.elim _ _
      have hf0 : f 0 = 0 := by
        rw [hfdef, hZ0]
        simp
      have h1 : (0:ℝ) ≤ sSup (Set.range f) := by
        rw [← hf0]
        exact le_csSup hbdd ⟨0, rfl⟩
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
      linarith
    · have : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
      have hNpos : (0:ℝ) < (N : ℝ) := by
        have := hN
        positivity
      have hθN : (0:ℝ) < θ / (N : ℝ) := by positivity
      have hch : ∀ j : Fin N, ∃ w : E, sSup (Set.range (fj j)) - θ / (N : ℝ) < fj j w := by
        intro j
        have hlt : sSup (Set.range (fj j)) - θ / (N : ℝ) < sSup (Set.range (fj j)) := by
          linarith
        have hne : (Set.range (fj j)).Nonempty := ⟨fj j (ofLp Z j), ⟨ofLp Z j, rfl⟩⟩
        obtain ⟨y, hy, hlty⟩ := exists_lt_of_lt_csSup hne hlt
        obtain ⟨w, rfl⟩ := hy
        exact ⟨w, hlty⟩
      choose w hw using hch
      have h1 : ∑ j, (sSup (Set.range (fj j)) - θ / (N : ℝ)) < ∑ j, fj j (w j) :=
        Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun j _ => hw j)
      have h2 : ∑ j : Fin N, (sSup (Set.range (fj j)) - θ / (N : ℝ))
          = (∑ j, sSup (Set.range (fj j))) - θ := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
        field_simp
      rw [h2] at h1
      have h3 : ∑ j, fj j (w j) ≤ sSup (Set.range f) := by
        have h4 : f (toLp 2 w) = ∑ j, fj j (w j) := by
          rw [hsep (toLp 2 w)]
        rw [← h4]
        exact le_csSup hbdd ⟨toLp 2 w, rfl⟩
      have h5 : ∀ j : Fin N, SupConvolution ε (G j) (ofLp Z j)
          = sSup (Set.range (fj j)) := hR
      rw [Finset.sum_congr rfl (fun j _ => h5 j)]
      linarith
