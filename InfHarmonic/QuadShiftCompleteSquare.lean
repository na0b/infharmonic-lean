import InfHarmonic.Preamble

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Completing the square across a two-leg quadratic cost.  With `s = t + l`, the
combination of the three quadratic terms that appears when the forward envelope at time
`t` is compared with the free quadratic at time `s` collapses to a single square centred
at `(s/t)x`.  Both the centre and the coefficient `-t/(2ls)` are forced, and the
right-hand side depends on `x` only through that centre: this is what turns the
envelope's defining supremum into the partial supremum of a jointly concave function. -/
theorem QuadShiftCompleteSquare (t l : ℝ) (ht : 0 < t) (hl : 0 < l) (y x : F) :
    ‖y‖ ^ 2 / (2 * (t + l)) - ‖y - x‖ ^ 2 / (2 * l) - ‖x‖ ^ 2 / (2 * t)
      = -(t / (2 * l * (t + l))) * ‖y - ((t + l) / t) • x‖ ^ 2 := by
  have ht' : t ≠ 0 := ne_of_gt ht
  have hl' : l ≠ 0 := ne_of_gt hl
  have hs : (0:ℝ) < t + l := by linarith
  have hs' : t + l ≠ 0 := ne_of_gt hs
  -- expand both squares in terms of `‖y‖²`, `⟪y, x⟫` and `‖x‖²`
  have e1 : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ y x + ‖x‖ ^ 2 := norm_sub_sq_real y x
  have e2 : ‖y - ((t + l) / t) • x‖ ^ 2
      = ‖y‖ ^ 2 - 2 * ((t + l) / t) * inner ℝ y x + ((t + l) / t) ^ 2 * ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  -- and compare coefficients
  rw [e1, e2]
  field_simp
  ring
