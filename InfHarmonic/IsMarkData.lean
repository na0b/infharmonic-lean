import InfHarmonic.IsFit
open Set WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The marks of the proof of Proposition 6.7, part 3: for each level
`j ≤ N` the stopping index `smark j` is the first index at which the walk
either stops or reaches the time level `2⁻ʲ`, and `(pj j, aj j)` is a fit for
`v` at that mark of radius `2⁻ʲ`, chosen measurably with respect to the stopped
σ-algebra and set to zero when the level is not reached. -/
def IsMarkData (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (N : ℕ)
    {Ω : Type*} {m0 : MeasurableSpace Ω} (𝒢 : Filtration ℕ m0)
    (z : ℕ → Ω → WithLp 2 (F × ℝ)) (τ : Ω → ℕ)
    (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (aj : ℕ → Ω → ℝ) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j ≤ N →
    IsStoppingTime 𝒢 (fun ω => (smark j ω : ℕ∞)) ∧
    (∀ ω, smark j ω ≤ τ ω) ∧
    (∀ ω, ∀ n < smark j ω, n < τ ω ∧ (ofLp (z n ω)).2 ≠ (1 / 2 : ℝ) ^ j) ∧
    (∀ ω, smark j ω = τ ω ∨ (ofLp (z (smark j ω) ω)).2 = (1 / 2 : ℝ) ^ j) ∧
    (∀ n, StronglyMeasurable[𝒢 n] (fun ω => if smark j ω ≤ n then pj j ω else 0)) ∧
    (∀ n, StronglyMeasurable[𝒢 n] (fun ω => if smark j ω ≤ n then aj j ω else 0)) ∧
    (∀ ω, (ofLp (z (smark j ω) ω)).2 = (1 / 2 : ℝ) ^ j →
      IsFit C₀ v (z (smark j ω) ω) ((1 / 2 : ℝ) ^ j) (pj j ω) (aj j ω)) ∧
    (∀ ω, (ofLp (z (smark j ω) ω)).2 ≠ (1 / 2 : ℝ) ^ j →
      pj j ω = 0 ∧ aj j ω = 0)
