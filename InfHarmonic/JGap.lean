import InfHarmonic.QuadEnvP
import InfHarmonic.QuadEnvM
import InfHarmonic.ContactEnv

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The discrete propagation quantity
`J_ε = (P_ε W - M_ε v) / (2ε)` of (6.1), with `W` the contact envelope. -/
noncomputable def JGap (v : WithLp 2 (F × ℝ) → ℝ) (κ ε : ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  (QuadEnvP (ContactEnv v κ) ε z - QuadEnvM v ε z) / (2 * ε)
