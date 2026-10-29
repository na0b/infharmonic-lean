module

public import InfHarmonic.LimitOp

@[expose] public section
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The rescaled operator `D²φ[(∇_x φ, 1 + λ φ_t)]` of (3.7). -/
noncomputable def RescaledOp (lam : ℝ) (φ : WithLp 2 (F × ℝ) → ℝ)
    (z : WithLp 2 (F × ℝ)) : ℝ :=
  iteratedFDeriv ℝ 2 φ z
    (fun _ => toLp 2 ((ofLp (∇ φ z)).1, 1 + lam * (ofLp (∇ φ z)).2))
