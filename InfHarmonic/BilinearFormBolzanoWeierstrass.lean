import InfHarmonic.Preamble
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Bolzano-Weierstrass for tuples of continuous bilinear forms: the space of
`N`-tuples of continuous bilinear forms on a finite-dimensional space is itself
finite-dimensional, so a sequence of such tuples that is bounded uniformly in
norm has a subsequence converging in every coordinate.  Both of the limits taken
in the proof of the theorem of sums -- the one that shrinks the Jensen radius and
the one that removes the regularization `τ` -- are instances of this
statement. -/
theorem BilinearFormBolzanoWeierstrass (N : ℕ) (Lam : ℝ)
    (Xs : ℕ → Fin N → (E →L[ℝ] E →L[ℝ] ℝ))
    (hb : ∀ (k : ℕ) (j : Fin N), ‖Xs k j‖ ≤ Lam) :
    ∃ (X : Fin N → (E →L[ℝ] E →L[ℝ] ℝ)) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ j : Fin N, Filter.Tendsto (fun k => Xs (φ k) j) Filter.atTop (nhds (X j)) := by
  -- TWO INSTANCE NOTES, recorded here because they blocked an earlier burst.
  -- (1) On `E →L[ℝ] E →L[ℝ] ℝ` the `Norm` instance resolves as
  -- `ContinuousLinearMap.hasOpNorm` and the metric as
  -- `ContinuousLinearMap.toPseudoMetricSpace`.  These ARE `rfl`-equal to the ones a generic
  -- lemma uses -- `(SeminormedAddGroup.toNorm : Norm _) = ContinuousLinearMap.hasOpNorm` is
  -- `rfl` here -- but with an IMPLICIT argument the instance problem is stuck on a metavariable
  -- and `rw [dist_zero_right]` or `mem_closedBall_zero_iff.mpr h` both fail.  Naming the term,
  -- `dist_zero_right (Xs k j)`, closes the gap.  That is pm-0035 clause 1 in a new guise.
  -- (2) `FiniteDimensional` on this space must be taken from the `Module.Finite` instance; the
  -- named theorem `ContinuousLinearMap.finiteDimensional` is stated over a bare
  -- `TopologicalSpace`/`Module` tower and its `FiniteDimensional 𝕜 E` argument does NOT match
  -- the one coming from `InnerProductSpace ℝ E`.  And do NOT re-`have` an
  -- `InnerProductSpace ℝ E` into the local context for the unused-variable linter: a second copy
  -- creates a `NormedSpace ℝ E` diamond and `inferInstance` then fails on the line below.
  have hfd : FiniteDimensional ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance
  have hprop : ProperSpace (E →L[ℝ] E →L[ℝ] ℝ) :=
    FiniteDimensional.proper ℝ (E →L[ℝ] E →L[ℝ] ℝ)
  -- a finite product of closed balls is compact, and the sequence of tuples lives in it
  have hcpt : IsCompact
      (Set.univ.pi fun _ : Fin N => Metric.closedBall (0 : E →L[ℝ] E →L[ℝ] ℝ) Lam) :=
    isCompact_univ_pi (fun _ => isCompact_closedBall _ _)
  obtain ⟨X, _, φ, hφ, hconv⟩ := hcpt.tendsto_subseq (x := Xs) (fun k => by
    refine Set.mem_univ_pi.mpr (fun j => ?_)
    rw [Metric.mem_closedBall, dist_zero_right (Xs k j)]
    exact hb k j)
  -- convergence in the product topology is convergence in every coordinate
  exact ⟨X, φ, hφ, fun j => ((continuous_apply j).tendsto X).comp hconv⟩
