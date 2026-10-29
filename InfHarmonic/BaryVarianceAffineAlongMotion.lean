module

public import InfHarmonic.Preamble

@[expose] public section

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The variance penalty is affine along the straight common-time motion.  Move each
point of a weighted configuration with mean `x₀` at the velocity
`p + (y₀ i - x₀)/t₀`, and move time at unit speed.  Then every offset from the running
barycentre dilates by the single factor `1 + h/t₀`, so the penalty
`(∑ᵢ θᵢ |yᵢ - mean|²)/(2t)` becomes an affine function of the time increment `h`.  This
is the computation that makes the penalty invisible to the second derivative in the
common-time direction. -/
theorem BaryVarianceAffineAlongMotion (n : ℕ) (θ : Fin n → ℝ) (hθ1 : ∑ i, θ i = 1)
    (y₀ : Fin n → F) (x₀ : F) (hmean : ∑ i, θ i • y₀ i = x₀)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (p : F) (h : ℝ) (hth : 0 < t₀ + h) :
    (∑ i, θ i * ‖(y₀ i + h • (p + (t₀)⁻¹ • (y₀ i - x₀)))
          - ∑ j, θ j • (y₀ j + h • (p + (t₀)⁻¹ • (y₀ j - x₀)))‖ ^ 2)
        / (2 * (t₀ + h))
      = (∑ i, θ i * ‖y₀ i - x₀‖ ^ 2) / (2 * t₀)
        + (∑ i, θ i * ‖y₀ i - x₀‖ ^ 2) / (2 * t₀ ^ 2) * h := by
  have ht0 : t₀ ≠ 0 := ne_of_gt ht₀
  have hth' : t₀ + h ≠ 0 := ne_of_gt hth
  -- the weighted mean of the offsets from `x₀` vanishes
  have hoff0 : ∑ j, θ j • (y₀ j - x₀) = 0 := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hθ1, one_smul, sub_self]
  -- so the weighted mean of the velocities is exactly `p`
  have hq : ∑ j, θ j • (p + (t₀)⁻¹ • (y₀ j - x₀)) = p := by
    simp only [smul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, hθ1, one_smul]
    have : ∑ j, θ j • ((t₀)⁻¹ • (y₀ j - x₀)) = (t₀)⁻¹ • ∑ j, θ j • (y₀ j - x₀) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]
    rw [this, hoff0, smul_zero, add_zero]
  -- hence the running barycentre moves with velocity `p`
  have hmove : ∑ j, θ j • (y₀ j + h • (p + (t₀)⁻¹ • (y₀ j - x₀))) = x₀ + h • p := by
    have e1 : ∑ j, θ j • (y₀ j + h • (p + (t₀)⁻¹ • (y₀ j - x₀)))
        = (∑ j, θ j • y₀ j) + ∑ j, θ j • (h • (p + (t₀)⁻¹ • (y₀ j - x₀))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => smul_add _ _ _
    have e2 : ∑ j, θ j • (h • (p + (t₀)⁻¹ • (y₀ j - x₀)))
        = h • ∑ j, θ j • (p + (t₀)⁻¹ • (y₀ j - x₀)) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]
    rw [e1, e2, hq, hmean]
  -- every offset dilates by the same scalar factor `1 + h/t₀`
  have hdil : ∀ i, (y₀ i + h • (p + (t₀)⁻¹ • (y₀ i - x₀))) - (x₀ + h • p)
      = (1 + h * (t₀)⁻¹) • (y₀ i - x₀) := by
    intro i
    rw [smul_add, add_smul, one_smul, smul_smul]
    module
  -- so the variance scales by the square of that factor
  have hsum : (∑ i, θ i * ‖(y₀ i + h • (p + (t₀)⁻¹ • (y₀ i - x₀)))
        - ∑ j, θ j • (y₀ j + h • (p + (t₀)⁻¹ • (y₀ j - x₀)))‖ ^ 2)
      = (1 + h * (t₀)⁻¹) ^ 2 * ∑ i, θ i * ‖y₀ i - x₀‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hmove, hdil i, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  -- and `(1 + h/t₀)²/(2(t₀+h))` collapses to an affine function of `h`
  rw [hsum]
  field_simp
