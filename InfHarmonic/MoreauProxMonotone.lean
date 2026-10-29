module

public import InfHarmonic.MoreauProxSubgradient

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The firm nonexpansiveness of the proximal map: the squared distance between
the minimizers plus the squared distance between the associated subgradients is
at most the squared distance between the base points. -/
theorem MoreauProxMonotone (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (y₁ y₂ x₁ x₂ : E)
    (h₁ : ∀ x : E, ψ x₁ + ‖x₁ - y₁‖ ^ 2 / 2 ≤ ψ x + ‖x - y₁‖ ^ 2 / 2)
    (h₂ : ∀ x : E, ψ x₂ + ‖x₂ - y₂‖ ^ 2 / 2 ≤ ψ x + ‖x - y₂‖ ^ 2 / 2) :
    ‖x₁ - x₂‖ ^ 2 + ‖(y₁ - x₁) - (y₂ - x₂)‖ ^ 2 ≤ ‖y₁ - y₂‖ ^ 2 := by
  -- Step 1: `y i - x i` is a subgradient of `ψ` at `x i`.
  have sub₁ := (MoreauProxSubgradient ψ hψ y₁ x₁).mp h₁
  have sub₂ := (MoreauProxSubgradient ψ hψ y₂ x₂).mp h₂
  have s₁ := sub₁ x₂
  have s₂ := sub₂ x₁
  -- Step 2: monotonicity of the subgradient pairs.
  have hflip : ∀ p : E, inner ℝ p (x₁ - x₂) = - inner ℝ p (x₂ - x₁) := by
    intro p
    rw [show x₁ - x₂ = -(x₂ - x₁) from by abel, inner_neg_right]
  have hI : inner ℝ (x₁ - x₂) ((y₁ - x₁) - (y₂ - x₂))
      = - (inner ℝ (y₁ - x₁) (x₂ - x₁) + inner ℝ (y₂ - x₂) (x₁ - x₂)) := by
    rw [inner_sub_right, real_inner_comm (y₁ - x₁) (x₁ - x₂),
      real_inner_comm (y₂ - x₂) (x₁ - x₂), hflip (y₁ - x₁)]
    ring
  have hmono : 0 ≤ inner ℝ (x₁ - x₂) ((y₁ - x₁) - (y₂ - x₂)) := by
    rw [hI]
    linarith
  -- Step 3: expand the square of `y₁ - y₂ = (x₁ - x₂) + ((y₁ - x₁) - (y₂ - x₂))`.
  have hexp : ‖y₁ - y₂‖ ^ 2
      = ‖x₁ - x₂‖ ^ 2 + 2 * inner ℝ (x₁ - x₂) ((y₁ - x₁) - (y₂ - x₂))
        + ‖(y₁ - x₁) - (y₂ - x₂)‖ ^ 2 := by
    rw [show y₁ - y₂ = (x₁ - x₂) + ((y₁ - x₁) - (y₂ - x₂)) from by abel,
      norm_add_sq_real]
  linarith
