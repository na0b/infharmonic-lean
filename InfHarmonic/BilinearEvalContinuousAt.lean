module

public import InfHarmonic.Preamble

@[expose] public section
open Filter Topology

/-- Evaluating a varying symmetric-form-valued map on a varying direction is continuous
wherever both are.  Written for the shape `w ↦ B w [u w, u w]` that appears when a
second-order inequality, obtained along a sequence of approximating test functions, is
passed to the limit: both the second derivative and the direction move with the index. -/
theorem BilinearEvalContinuousAt {Z E : Type*} [TopologicalSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : Z → (E →L[ℝ] E →L[ℝ] ℝ)) (u : Z → E) (z : Z)
    (hB : ContinuousAt B z) (hu : ContinuousAt u z) :
    ContinuousAt (fun w => B w (u w) (u w)) z := by
  -- the first evaluation, `(C, x) ↦ C x` on `(E →L[ℝ] E →L[ℝ] ℝ) × E`
  have h1 : ContinuousAt (fun w => B w (u w)) z := by
    have he : ContinuousAt
        (fun q : (E →L[ℝ] E →L[ℝ] ℝ) × E => q.1 q.2) (B z, u z) :=
      (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := E →L[ℝ] ℝ)).continuous.continuousAt
    have h := Filter.Tendsto.comp he (hB.prodMk_nhds hu)
    exact h
  -- the second evaluation, `(C, x) ↦ C x` on `(E →L[ℝ] ℝ) × E`
  have he2 : ContinuousAt (fun q : (E →L[ℝ] ℝ) × E => q.1 q.2) (B z (u z), u z) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous.continuousAt
  have h := Filter.Tendsto.comp he2 (h1.prodMk_nhds hu)
  exact h
