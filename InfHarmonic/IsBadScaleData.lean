import InfHarmonic.NormalizedInfFamily
import InfHarmonic.IsCylinderFit
set_option linter.unusedVariables false
open Metric Set Filter Topology WithLp

/-- The selection data of Lemma 3.4: exponents, scales, normalized solutions,
centers, radii and bad parameters, with the enlarged parameter `32 λ i` good at
every nearby center and every comparable radius. -/
def IsBadScaleData (d : ℕ) (hd : 1 ≤ d) (γ s r lam : ℕ → ℝ)
    (U : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (z : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) : Prop :=
  (∀ i, 0 < γ i) ∧ Tendsto γ atTop (𝓝 0) ∧
  (∀ i, 0 < s i) ∧ Tendsto s atTop (𝓝 0) ∧
  (∀ i, 0 < lam i) ∧ Tendsto lam atTop (𝓝 0) ∧
  (∀ i, NormalizedInfFamily d (U i)) ∧
  (∀ i, z i ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)) ∧
  (∀ i, 0 < r i) ∧
  (∀ i, r i ≤ s i *
    infDist (z i) (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)))) ∧
  (∀ i, ¬ ∃ P, IsCylinderFit (U i) (z i) (r i) (lam i) P) ∧
  (∀ M : ℝ, 2 ≤ M → ∃ i₀ : ℕ, ∀ i ≥ i₀,
    ∀ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖w - z i‖ ≤ M * r i →
      ∀ ρ : ℝ, 0 < ρ → ρ ≤ M * r i →
        w ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
        ρ ≤ (1 / 8) *
          infDist w (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
        ∃ P, IsCylinderFit (U i) w ρ (32 * lam i) P)
