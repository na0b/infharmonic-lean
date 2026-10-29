import InfHarmonic.Preamble
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The limiting operator `F[φ](z) = D²φ(z)[(∇_x φ(z), 1)]` on space-time
`WithLp 2 (F × ℝ)`. -/
noncomputable def LimitOp (φ : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  iteratedFDeriv ℝ 2 φ z (fun _ => toLp 2 ((ofLp (∇ φ z)).1, (1 : ℝ)))
