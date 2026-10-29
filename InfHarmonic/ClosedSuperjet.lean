module

public import InfHarmonic.Superjet

@[expose] public section
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The closed superjet `J̄^{2,+} g (z)`: limits of superjets at points
approaching `z`, with the function values also converging. -/
def ClosedSuperjet (g : E → ℝ) (z : E) : Set (E × (E →L[ℝ] E →L[ℝ] ℝ)) :=
  {pX | ∃ (zs : ℕ → E) (ps : ℕ → E) (Xs : ℕ → (E →L[ℝ] E →L[ℝ] ℝ)),
      (∀ k, (ps k, Xs k) ∈ Superjet g (zs k)) ∧
      Tendsto zs atTop (𝓝 z) ∧ Tendsto (fun k => g (zs k)) atTop (𝓝 (g z)) ∧
      Tendsto ps atTop (𝓝 pX.1) ∧ Tendsto Xs atTop (𝓝 pX.2)}
