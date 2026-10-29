import InfHarmonic.QuadEnvP
import InfHarmonic.QuadEnvM
import InfHarmonic.ContactEnv
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `(z⁺, z⁻)` is a pair of optimizing steps of size `ε` at `z`, as in
(6.3): the intermediate points at times `t ± ε` on the straight paths to a
maximizer for `P_{2ε} W (z)` and a minimizer for `M_{2ε} v (z)`. -/
def IsStepPair (v : WithLp 2 (F × ℝ) → ℝ) (κ ε : ℝ)
    (z zp zm : WithLp 2 (F × ℝ)) : Prop :=
  ∃ Yp Ym : F,
    QuadEnvP (ContactEnv v κ) (2 * ε) z
        = ContactEnv v κ (toLp 2 (Yp, (ofLp z).2 + 2 * ε))
            - ‖Yp - (ofLp z).1‖ ^ 2 / (2 * (2 * ε)) ∧
    QuadEnvM v (2 * ε) z
        = v (toLp 2 (Ym, (ofLp z).2 - 2 * ε))
            + ‖Ym - (ofLp z).1‖ ^ 2 / (2 * (2 * ε)) ∧
    zp = toLp 2 ((2 : ℝ)⁻¹ • ((ofLp z).1 + Yp), (ofLp z).2 + ε) ∧
    zm = toLp 2 ((2 : ℝ)⁻¹ • ((ofLp z).1 + Ym), (ofLp z).2 - ε)
