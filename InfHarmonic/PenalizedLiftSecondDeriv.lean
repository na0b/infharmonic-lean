module

public import InfHarmonic.SecondFDerivCompLinear

@[expose] public section
open Set Metric Filter Topology

/-- The second derivative of a penalised lift, in a direction the penalty cannot see.
Let `L : P →L[ℝ] Q` and `M : P →L[ℝ] R` be continuous linear maps, let `g : Q → ℝ` be
`C²` near `L W`, and set `Ψ := g ∘ L + lam * ‖M ·‖²/2`.  If `ζ` lies in the kernel of
`M` then the quadratic penalty contributes nothing to `D²Ψ(W)[ζ, ζ]`, which is
therefore the second derivative of `g` transported through `L`.  This is the step that
lets a penalty term be added to localise a maximum without disturbing the second-order
information in the directions that matter. -/
theorem PenalizedLiftSecondDeriv {P Q R : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q]
    [NormedAddCommGroup R] [InnerProductSpace ℝ R]
    (L : P →L[ℝ] Q) (M : P →L[ℝ] R) (g : Q → ℝ) (lam : ℝ) (W ζ : P)
    (hg : ContDiffAt ℝ 2 g (L W)) (hMζ : M ζ = 0) :
    fderiv ℝ (fderiv ℝ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2))) W ζ ζ
      = fderiv ℝ (fderiv ℝ g) (L W) (L ζ) (L ζ) := by
  -- NOTE (worker, cycle 121).  This statement is deliberately abstract in `P`, `Q`, `R`
  -- even though its only consumer uses the concrete `PiLp`/`WithLp` product spaces, and
  -- that is not stylistic.  `DifferentiableAt`/`fderiv` are stated over
  -- `[AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]`, so at a concrete `WithLp p α`
  -- instance search resolves those arguments directly to `WithLp.instAddCommGroup` and
  -- `PiLp.topologicalSpace`, whereas the normed-section lemmas (`fderiv_add`,
  -- `fderiv_fun_add`, `HasFDerivAt.add`, `HasFDerivAt.const_smul`, and `nhds` on a
  -- product with a `→L` factor) carry `NormedAddCommGroup.toAddCommGroup` and
  -- `PseudoMetricSpace.toUniformSpace.toTopologicalSpace`.  The two paths are not
  -- interchangeable for unification, and neither `rw` nor `exact` bridges them: every
  -- attempt to run this split at the concrete type failed on the `+`.  With the
  -- instances as theorem parameters the whole difficulty disappears, and applying the
  -- result at the concrete types is then unproblematic.  If a similar `fderiv`
  -- manipulation is ever needed on a `WithLp` space, hoist it to an abstract node
  -- instead of fighting the instances in place.
  have hq : ContDiff ℝ 2 (fun u : R => ‖u‖ ^ 2 / 2) := (contDiff_norm_sq ℝ).div_const _
  have hχC2 : ContDiffAt ℝ 2 (fun U : P => ‖M U‖ ^ 2 / 2) W :=
    (hq.comp (M.contDiff (n := 2))).contDiffAt
  have hgLC2 : ContDiffAt ℝ 2 (fun U : P => g (L U)) W :=
    ContDiffAt.comp W hg (L.contDiff (n := 2)).contDiffAt
  -- the two first derivatives are themselves differentiable at `W`
  have hA : HasFDerivAt (fderiv ℝ (fun U : P => g (L U)))
      (fderiv ℝ (fderiv ℝ (fun U : P => g (L U))) W) W :=
    ((hgLC2.fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num)).hasFDerivAt
  have hB : HasFDerivAt (fderiv ℝ (fun U : P => ‖M U‖ ^ 2 / 2))
      (fderiv ℝ (fderiv ℝ (fun U : P => ‖M U‖ ^ 2 / 2)) W) W :=
    ((hχC2.fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num)).hasFDerivAt
  -- near `W` the first derivative splits additively
  have hev : fderiv ℝ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2))
      =ᶠ[𝓝 W] fun U => fderiv ℝ (fun V : P => g (L V)) U
        + lam • fderiv ℝ (fun V : P => ‖M V‖ ^ 2 / 2) U := by
    filter_upwards [hgLC2.eventually (by norm_num)] with U hU
    have h1 : DifferentiableAt ℝ (fun V : P => g (L V)) U := hU.differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (fun V : P => ‖M V‖ ^ 2 / 2) U :=
      ((hq.comp (M.contDiff (n := 2))).differentiable (by norm_num)) U
    have h3 : HasFDerivAt (fun V => g (L V) + lam * (‖M V‖ ^ 2 / 2))
        (fderiv ℝ (fun V : P => g (L V)) U
          + lam • fderiv ℝ (fun V : P => ‖M V‖ ^ 2 / 2) U) U :=
      h1.hasFDerivAt.add (h2.hasFDerivAt.const_mul lam)
    exact h3.fderiv
  -- differentiate once more
  have hsd : HasFDerivAt (fderiv ℝ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2)))
      (fderiv ℝ (fderiv ℝ (fun U : P => g (L U))) W
        + lam • fderiv ℝ (fderiv ℝ (fun U : P => ‖M U‖ ^ 2 / 2)) W) W :=
    (hA.add (hB.const_smul lam)).congr_of_eventuallyEq hev
  rw [hsd.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  -- the penalty term dies: its second derivative is evaluated at `M ζ = 0`
  have hχ0 : fderiv ℝ (fderiv ℝ (fun U : P => ‖M U‖ ^ 2 / 2)) W ζ ζ = 0 := by
    rw [SecondFDerivCompLinear M (fun u : R => ‖u‖ ^ 2 / 2) W hq.contDiffAt ζ ζ, hMζ]
    simp
  rw [hχ0, SecondFDerivCompLinear L g W hg ζ ζ]
  ring
