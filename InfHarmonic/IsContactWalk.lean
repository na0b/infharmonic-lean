import InfHarmonic.IsStepPair
import InfHarmonic.JGap
open Set WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The stopped contact walk of the proof of Proposition 6.7, parts 1: fair
signs `ξ`, the state process `z` built from optimizing step pairs `(zp, zm)` of
size `ε`, the reference velocities `Q₀`, and the stopping index `τ` for the
first hit of the time level `2⁻ᴺ`, the time level `T`, or the horizontal
cutoff `R`. -/
def IsContactWalk (κ H : ℝ) (T : ℕ) (R : ℝ) (v : WithLp 2 (F × ℝ) → ℝ)
    (N : ℕ) (ε : ℝ) {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
    (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ) : Prop :=
  μ Set.univ = 1 ∧
  (∃ k : ℕ, ε = (1 / 2 : ℝ) ^ k) ∧ 0 < ε ∧ ε ≤ (1 / 2 : ℝ) ^ N / 4 ∧
  (∀ n ω, ξ n ω = 1 ∨ ξ n ω = -1) ∧
  (∀ n, StronglyMeasurable[𝒢 (n + 1)] (ξ n)) ∧
  (∀ n, μ[ξ n | 𝒢 n] =ᵐ[μ] 0) ∧
  (∀ n, StronglyMeasurable[𝒢 n] (z n)) ∧
  (∀ n, StronglyMeasurable[𝒢 n] (zp n)) ∧
  (∀ n, StronglyMeasurable[𝒢 n] (zm n)) ∧
  (∀ n, StronglyMeasurable[𝒢 n] (Q₀ n)) ∧
  (∀ ω, z 0 ω = toLp 2 ((0 : F), (1 : ℝ))) ∧
  (∀ n ω, n < τ ω → IsStepPair v κ ε (z n ω) (zp n ω) (zm n ω)) ∧
  (∀ n ω, z (n + 1) ω
      = if n < τ ω then (if ξ n ω = 1 then zp n ω else zm n ω) else z n ω) ∧
  (∀ n ω, HasGradientAt
      (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp (z n ω)).2)))
      (Q₀ n ω) (ofLp (z n ω)).1) ∧
  IsStoppingTime 𝒢 (fun ω => (τ ω : ℕ∞)) ∧
  Integrable (fun ω => (τ ω : ℝ)) μ ∧
  (∀ n ω, n < τ ω →
      (1 / 2 : ℝ) ^ N < (ofLp (z n ω)).2 ∧ (ofLp (z n ω)).2 < (T : ℝ) ∧
        ‖(ofLp (z n ω)).1‖ < R) ∧
  (∀ ω, (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N ∨ (ofLp (z (τ ω) ω)).2 = (T : ℝ) ∨
      R ≤ ‖(ofLp (z (τ ω) ω)).1‖) ∧
  (∀ n ω, n ≤ τ ω → ‖(ofLp (z n ω)).1‖ ≤ R + 1) ∧
  H - 1 ≤ JGap v κ ε (toLp 2 ((0 : F), (1 : ℝ)))
