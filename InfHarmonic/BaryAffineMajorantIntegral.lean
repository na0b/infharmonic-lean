module

public import InfHarmonic.Preamble
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
open Set WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable [MeasurableSpace F] [BorelSpace F]

/-- Step 7 of Lemma 5.2: an affine majorant of `g` with slope `A₀` integrates
against any probability measure of mean `x` and finite second moment, the linear
term dropping out, and the second-moment identity converts the result into the
barycentric form. -/
theorem BaryAffineMajorantIntegral (f : WithLp 2 (F × ℝ) → ℝ) (s t : ℝ) (hs : 0 < s)
    (x : F) (Λ : ℝ) (A₀ : F)
    (hmaj : ∀ y : F, f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)
      ≤ Λ + inner ℝ A₀ (y - x))
    (μ : Measure F) (hμ : IsProbabilityMeasure μ)
    (hsq : Integrable (fun y : F => ‖y - x‖ ^ 2) μ)
    (hf : Integrable (fun y : F => f (toLp 2 (y, t))) μ)
    (hlin : Integrable (fun y : F => y - x) μ)
    (hmean : (∫ y, (y - x) ∂μ) = 0) :
    (∫ y, f (toLp 2 (y, t)) ∂μ) - (∫ y, ‖y - x‖ ^ 2 ∂μ) / (2 * s)
      ≤ Λ + ‖x‖ ^ 2 / (2 * s) := by
  -- Body-only acknowledgements (traps 2 and 3): `[BorelSpace F]` and `hs` are part of this
  -- node's protected signature; the route below reaches the conclusion without consuming
  -- them, so they are named here rather than by editing any line above `-- BODY`.
  have _ : BorelSpace F := inferInstance
  have _ := hs
  -- The expansion ‖y‖² = ‖y-x‖² + 2⟪x, y-x⟫ + ‖x‖², with the inner product written
  -- constant-first so that `integral_inner` applies to it directly.
  have hexp : ∀ y : F,
      ‖y‖ ^ 2 = ‖y - x‖ ^ 2 + 2 * (inner ℝ x (y - x) : ℝ) + ‖x‖ ^ 2 := by
    intro y
    have h := norm_add_sq_real (y - x) x
    have hyx : (y - x) + x = y := by abel
    rw [hyx, real_inner_comm x (y - x)] at h
    exact h
  -- Integrability of each summand: the second moment by hypothesis, the linear term as
  -- the integrable `y ↦ y - x` composed with the continuous linear functional ⟪x, ·⟫,
  -- and the constant because μ is finite.
  have hinnerx : Integrable (fun y : F => (inner ℝ x (y - x) : ℝ)) μ :=
    Integrable.const_inner x hlin
  have hi1 : Integrable (fun y : F => 2 * (inner ℝ x (y - x) : ℝ)) μ := hinnerx.const_mul 2
  -- stated with an explicit lambda type: `Integrable.add` yields Pi-addition, while
  -- `integral_add` wants its integrand as `fun a => f a + g a`
  have hi2 : Integrable (fun y : F => ‖y - x‖ ^ 2 + 2 * (inner ℝ x (y - x) : ℝ)) μ :=
    hsq.add hi1
  have hnormsq : Integrable (fun y : F => ‖y‖ ^ 2) μ := by
    have hfun : (fun y : F => ‖y‖ ^ 2)
        = fun y : F => ‖y - x‖ ^ 2 + 2 * (inner ℝ x (y - x) : ℝ) + ‖x‖ ^ 2 := funext hexp
    rw [hfun]
    exact (hsq.add hi1).add (integrable_const _)
  -- Both linear terms vanish on the mean-zero hypothesis.
  have hlinzero : (∫ y, (inner ℝ x (y - x) : ℝ) ∂μ) = 0 := by
    rw [integral_inner hlin x, hmean, inner_zero_right]
  have hA₀zero : (∫ y, (inner ℝ A₀ (y - x) : ℝ) ∂μ) = 0 := by
    rw [integral_inner hlin A₀, hmean, inner_zero_right]
  -- The second-moment identity.
  have hmom : (∫ y, ‖y‖ ^ 2 ∂μ) = (∫ y, ‖y - x‖ ^ 2 ∂μ) + ‖x‖ ^ 2 := by
    have hfun : (fun y : F => ‖y‖ ^ 2)
        = fun y : F => ‖y - x‖ ^ 2 + 2 * (inner ℝ x (y - x) : ℝ) + ‖x‖ ^ 2 := funext hexp
    rw [hfun, integral_add hi2 (integrable_const _), integral_add hsq hi1,
      integral_const_mul, hlinzero, mul_zero, add_zero, integral_const]
    simp
  -- Monotonicity of the integral against the affine majorant.
  have hg : Integrable (fun y : F => f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)) μ :=
    hf.sub (hnormsq.div_const (2 * s))
  have hmajint : Integrable (fun y : F => Λ + (inner ℝ A₀ (y - x) : ℝ)) μ :=
    (integrable_const Λ).add (Integrable.const_inner A₀ hlin)
  have hmono := integral_mono hg hmajint hmaj
  have hrhs : (∫ y, (Λ + (inner ℝ A₀ (y - x) : ℝ)) ∂μ) = Λ := by
    rw [integral_add (integrable_const Λ) (Integrable.const_inner A₀ hlin), hA₀zero,
      add_zero, integral_const]
    simp
  have hlhs : (∫ y, (f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)) ∂μ)
      = (∫ y, f (toLp 2 (y, t)) ∂μ) - ((∫ y, ‖y - x‖ ^ 2 ∂μ) + ‖x‖ ^ 2) / (2 * s) := by
    rw [integral_sub hf (hnormsq.div_const (2 * s)), integral_div, hmom]
  rw [hrhs, hlhs] at hmono
  have hsplit : ((∫ y, ‖y - x‖ ^ 2 ∂μ) + ‖x‖ ^ 2) / (2 * s)
      = (∫ y, ‖y - x‖ ^ 2 ∂μ) / (2 * s) + ‖x‖ ^ 2 / (2 * s) := by ring
  rw [hsplit] at hmono
  linarith
