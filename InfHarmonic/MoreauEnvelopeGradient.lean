module

public import InfHarmonic.IsMoreauProx
public import InfHarmonic.MoreauProxMonotone

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The Moreau envelope `ψ₁ y = ψ (u y) + ‖u y - y‖² / 2` is differentiable with
gradient `y - u y`, with a quadratic error bound; so `ψ₁` is `C^{1,1}`. -/
theorem MoreauEnvelopeGradient (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E)
    (hu : IsMoreauProx ψ u) (y y' : E) :
    |(ψ (u y') + ‖u y' - y'‖ ^ 2 / 2) - (ψ (u y) + ‖u y - y‖ ^ 2 / 2)
        - inner ℝ (y - u y) (y' - y)| ≤ 3 / 2 * ‖y' - y‖ ^ 2 := by
  -- Step 1: the defining inequality at base point `y'` with test point `u y`
  have h1 := hu y' (u y)
  have e1 : u y - y' = (u y - y) - (y' - y) := by abel
  rw [e1, norm_sub_sq_real (u y - y) (y' - y)] at h1
  -- Step 2: the same at base point `y` with test point `u y'` (so `k` becomes `-k`)
  have h2 := hu y (u y')
  have e2 : u y' - y = (u y' - y') + (y' - y) := by abel
  rw [e2, norm_add_sq_real (u y' - y') (y' - y)] at h2
  -- the two sign flips that line the inner products up with the goal's `y - u y`
  have hneg1 : inner ℝ (u y - y) (y' - y) = - inner ℝ (y - u y) (y' - y) := by
    rw [← neg_sub y (u y), inner_neg_left]
  have hneg2 : inner ℝ (u y' - y') (y' - y) = - inner ℝ (y' - u y') (y' - y) := by
    rw [← neg_sub y' (u y'), inner_neg_left]
  -- Step 3: firm nonexpansiveness bounds the gradient difference by ‖k‖
  have hmono := MoreauProxMonotone ψ hψ y' y (u y') (u y) (hu y') (hu y)
  have hdk : ‖(y' - u y') - (y - u y)‖ ≤ ‖y' - y‖ := by
    have hsq : ‖(y' - u y') - (y - u y)‖ ^ 2 ≤ ‖y' - y‖ ^ 2 := by
      nlinarith [sq_nonneg ‖u y' - u y‖, hmono]
    nlinarith [hsq, norm_nonneg ((y' - u y') - (y - u y)), norm_nonneg (y' - y)]
  have hprod : ‖(y' - u y') - (y - u y)‖ * ‖y' - y‖ ≤ ‖y' - y‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hdk (norm_nonneg (y' - y))]
  -- Cauchy-Schwarz in the LOWER direction
  have hcs : -(‖(y' - u y') - (y - u y)‖ * ‖y' - y‖)
      ≤ inner ℝ ((y' - u y') - (y - u y)) (y' - y) :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  have hexp : inner ℝ ((y' - u y') - (y - u y)) (y' - y)
      = inner ℝ (y' - u y') (y' - y) - inner ℝ (y - u y) (y' - y) :=
    inner_sub_left _ _ _
  -- the upper side has slack (1/2 against 3/2), so each branch is linear
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · linarith [h2, hneg2, hcs, hexp, hprod, sq_nonneg ‖y' - y‖]
  · linarith [h1, hneg1, sq_nonneg ‖y' - y‖]
