module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Definitions used in the statements of the main results

This file is kept textually identical to the definitions section of `Challenge.lean`
(same Mathlib imports, same declarations in the same order), so that both elaborate to the
same terms, including the names of auxiliary proofs, as Comparator requires.
-/

@[expose] public section

open Metric Set

section Euclidean

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The (unnormalized) infinity Laplacian of `φ` at `z`:
`Δ_∞ φ(z) = D²φ(z)[∇φ(z), ∇φ(z)] = Σᵢⱼ ∂ᵢφ ∂ⱼφ ∂ᵢⱼφ`, written as the second iterated
Fréchet derivative of `φ` at `z` evaluated on the pair `(∇φ(z), ∇φ(z))`. It is only
applied to test functions that are `C²` at `z`. -/
noncomputable def InfLap (φ : E → ℝ) (z : E) : ℝ :=
  iteratedFDeriv ℝ 2 φ z (fun _ => ∇ φ z)

end Euclidean

section Viscosity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- `u` is a viscosity subsolution of `Δ_∞ u = 0` on `Ω`: `Ω` is open, `u` is continuous
on `Ω`, and whenever `φ` is `C²` at `z ∈ Ω` and `u - φ` has a local maximum (relative to
`Ω`) at `z` — i.e. `φ` touches `u` from above — then `Δ_∞ φ(z) ≥ 0`. -/
def IsInfSubsolutionOn (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn u Ω ∧
    ∀ z ∈ Ω, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMaxOn (fun x => u x - φ x) Ω z → 0 ≤ InfLap φ z

/-- `u` is a viscosity supersolution of `Δ_∞ u = 0` on `Ω`: `Ω` is open, `u` is continuous
on `Ω`, and whenever `φ` is `C²` at `z ∈ Ω` and `u - φ` has a local minimum (relative to
`Ω`) at `z` — i.e. `φ` touches `u` from below — then `Δ_∞ φ(z) ≤ 0`. -/
def IsInfSupersolutionOn (Ω : Set E) (u : E → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn u Ω ∧
    ∀ z ∈ Ω, ∀ φ : E → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMinOn (fun x => u x - φ x) Ω z → InfLap φ z ≤ 0

/-- `u` is infinity-harmonic on the open set `Ω`: a continuous viscosity solution of
`Δ_∞ u = 0`, i.e. both a viscosity subsolution and a viscosity supersolution. This is the
standard notion of the paper's §1.1 (all `C²` tests, including those with `∇φ(z) = 0`). -/
def IsInfHarmonicOn (Ω : Set E) (u : E → ℝ) : Prop :=
  IsInfSubsolutionOn Ω u ∧ IsInfSupersolutionOn Ω u

/-- The oscillation `osc_S u = sup_S u - inf_S u` (Mathlib's conditionally complete
`sSup`/`sInf`; the main theorem assumes `u` bounded on `S`, so these are the true
supremum and infimum). -/
noncomputable def OscOn (u : E → ℝ) (S : Set E) : ℝ :=
  sSup (u '' S) - sInf (u '' S)

variable {V : Type*} [NormedAddCommGroup V]

/-- The set of `α`-Hölder difference quotients `‖g x - g y‖ / ‖x - y‖^α` of a vector field
`g` over pairs of distinct points `x, y ∈ S`. -/
def HolderQuotSet (g : E → V) (α : ℝ) (S : Set E) : Set ℝ :=
  {q | ∃ x ∈ S, ∃ y ∈ S, x ≠ y ∧ q = ‖g x - g y‖ / dist x y ^ α}

/-- The Hölder seminorm `[g]_{C^{0,α}(S)} = sup_{x ≠ y ∈ S} ‖g x - g y‖ / ‖x - y‖^α`. It is
used only together with a proof that `HolderQuotSet g α S` is bounded above, so it is the
true supremum. -/
noncomputable def HolderSeminormOn (g : E → V) (α : ℝ) (S : Set E) : ℝ :=
  sSup (HolderQuotSet g α S)

end Viscosity

section SpaceTime

open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The limiting operator of the paper's equation (3.1) on space-time `F × ℝ` (with the
Euclidean `L²` product norm): for `z = (x, t)`,
`F[φ](z) = D²φ(z)[(∇ₓφ(z), 1), (∇ₓφ(z), 1)]`, where `∇ₓφ(z)` is the spatial component of the
space-time gradient. -/
noncomputable def LimitOp (φ : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)) : ℝ :=
  iteratedFDeriv ℝ 2 φ z (fun _ => toLp 2 ((ofLp (∇ φ z)).1, (1 : ℝ)))

end SpaceTime

section Limit

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- `v` is a viscosity subsolution of `F[v] = 0` on the open set `Ω ⊆ F × ℝ`: every `C²`
test touching `v` from above at `z ∈ Ω` has `F[φ](z) ≥ 0`. -/
def IsLimitSubOn (Ω : Set (WithLp 2 (F × ℝ))) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn v Ω ∧
    ∀ z ∈ Ω, ∀ φ : WithLp 2 (F × ℝ) → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMaxOn (fun w => v w - φ w) Ω z → 0 ≤ LimitOp φ z

/-- `v` is a viscosity supersolution of `F[v] = 0` on the open set `Ω ⊆ F × ℝ`: every `C²`
test touching `v` from below at `z ∈ Ω` has `F[φ](z) ≤ 0`. -/
def IsLimitSuperOn (Ω : Set (WithLp 2 (F × ℝ))) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsOpen Ω ∧ ContinuousOn v Ω ∧
    ∀ z ∈ Ω, ∀ φ : WithLp 2 (F × ℝ) → ℝ, ContDiffAt ℝ 2 φ z →
      IsLocalMinOn (fun w => v w - φ w) Ω z → LimitOp φ z ≤ 0

/-- `v` is a continuous viscosity solution of the limiting equation
`F[v] = D²v[(∇ₓv, 1)] = 0` (paper, (3.1)) on the open set `Ω`. -/
def IsLimitSolutionOn (Ω : Set (WithLp 2 (F × ℝ))) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsLimitSubOn Ω v ∧ IsLimitSuperOn Ω v

open WithLp in
/-- `(p, a)` is a *fit* for `v` at `z = (x, t)` of radius `R` with constant `C₀` (paper,
(3.2)): for all `(h, ℓ)` in the sheared box `|ℓ| ≤ R`, `‖h - ℓ p‖ ≤ R`,
`|v(x + h, t + ℓ) - v(x, t) - ⟨p, h⟩ - (a - ‖p‖²/2) ℓ| ≤ C₀ R`. -/
def IsFit (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)) (R : ℝ)
    (p : F) (a : ℝ) : Prop :=
  ∀ (h : F) (l : ℝ), |l| ≤ R → ‖h - l • p‖ ≤ R →
    |v (z + toLp 2 (h, l)) - v z - inner ℝ p h - (a - ‖p‖ ^ 2 / 2) * l| ≤ C₀ * R

/-- The hypotheses of the paper's Liouville Theorem 3.1 on `v : F × ℝ → ℝ`: `v` is a
continuous viscosity solution of `F[v] = 0` on all of space-time, and at every point `z`
and every radius `R > 0` it admits a fit `(p, a)` with the same constant `C₀`. -/
def IsFitClass (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  IsLimitSolutionOn Set.univ v ∧
    ∀ (z : WithLp 2 (F × ℝ)) (R : ℝ), 0 < R → ∃ (p : F) (a : ℝ), IsFit C₀ v z R p a

open WithLp in
/-- `v` is affine on space-time: `v (x, t) = ⟨q, x⟩ + b t + c` for some `q ∈ F`, `b, c ∈ ℝ`. -/
def IsSpaceTimeAffine (v : WithLp 2 (F × ℝ) → ℝ) : Prop :=
  ∃ (q : F) (b c : ℝ), ∀ z : WithLp 2 (F × ℝ),
    v z = inner ℝ q (ofLp z).1 + b * (ofLp z).2 + c

end Limit
