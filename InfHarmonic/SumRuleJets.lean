import InfHarmonic.ClosedSuperjetClosed
import InfHarmonic.BilinearFormBolzanoWeierstrass
import InfHarmonic.SumRuleFixedTauJets
open Set MeasureTheory Metric
open scoped Gradient
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The theorem of sums (paper Lemma 2.4, Crandall-Ishii-Lions Theorem 3.2):
at a local maximum of `∑ g j - Ψ` the partial derivatives of `Ψ` are realized by
closed superjets of the `g j` whose Hessians satisfy
`diag (X 1, …, X N) ≤ A + η A²` with `A = D²Ψ`. -/
theorem SumRuleJets (N : ℕ) (O : Fin N → Set E) (hO : ∀ j, IsOpen (O j))
    (g : Fin N → E → ℝ) (hg : ∀ j, ContinuousOn (g j) (O j))
    (Ψ : PiLp 2 (fun _ : Fin N => E) → ℝ) (Z : PiLp 2 (fun _ : Fin N => E))
    (hZ : ∀ j, ofLp Z j ∈ O j) (hΨ : ContDiffAt ℝ 2 Ψ Z)
    (hmax : IsLocalMax (fun Y : PiLp 2 (fun _ : Fin N => E) =>
      (∑ j, g j (ofLp Y j)) - Ψ Y) Z)
    (η : ℝ) (hη : 0 < η) :
    ∃ X : Fin N → (E →L[ℝ] E →L[ℝ] ℝ),
      (∀ j, ∀ a b : E, X j a b = X j b a) ∧
      (∀ j, ((ofLp (∇ Ψ Z) j), X j) ∈ ClosedSuperjet (g j) (ofLp Z j)) ∧
      (∀ ξ : PiLp 2 (fun _ : Fin N => E),
        (∑ j, X j (ofLp ξ j) (ofLp ξ j))
          ≤ (fderiv ℝ (fderiv ℝ Ψ) Z) ξ ξ
            + η * ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ξ‖ ^ 2) := by
  -- PART V(3), THE LIMIT τ ↓ 0, IS WHAT THIS NODE KEEPS.  Parts I-V(2) are the imported
  -- helpers: `SumRuleFixedTauJets` delivers ONE constant `Lam` and then, for every
  -- τ ∈ (0,1], a family of symmetric forms that already sit in the closed superjets of the
  -- `g j` at the right base points, are bounded by `Lam`, and obey the matrix inequality for
  -- the PERTURBED form `D²Ψ + τ id`.  The τ-free bound is exactly what makes the family
  -- precompact, so a subsequence converges; the limit inherits the superjet memberships
  -- because the closed superjet is a closed set (`ClosedSuperjetClosed`, Part I(D)), and the
  -- τ-terms drop out of the matrix inequality in the limit.
  --
  -- A LEAN NOTE THAT COST A ROUND AND IS WORTH KEEPING.  On `(PiLp 2 fun _ => E) →L[ℝ] ℝ`
  -- the `Norm` instance resolves to `ContinuousLinearMap.hasOpNorm`, while a generic norm
  -- lemma applied with an implicit argument resolves its own instance through
  -- `SeminormedAddGroup.toNorm`; the two do not unify while the argument is still a
  -- metavariable.  Every generic norm lemma below is therefore given its argument
  -- EXPLICITLY (`norm_add_le (A ζ) _`, `Continuous.norm (f := …)`), which is enough.
  have _ : FiniteDimensional ℝ E := inferInstance
  have _ : BorelSpace E := inferInstance
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · -- N = 0: the product space is trivial, the family of forms is empty, both claims are vacuous
    subst hN0
    refine ⟨fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun j => Fin.elim0 j, fun ξ => ?_⟩
    have hξ : ξ = 0 := Subsingleton.elim _ _
    subst hξ
    simp
  -- PART V(1)-(2): the uniform constant, then the family at τ = 1/(k+1).
  obtain ⟨Lam, hLam0, hfam⟩ :=
    SumRuleFixedTauJets N hN O hO g hg Ψ Z hZ hΨ hmax η hη
  choose Xf hsym hnorm hjet hform using fun k : ℕ =>
    hfam (1 / ((k : ℝ) + 1)) (by positivity)
      (by
        rw [div_le_one (by positivity)]
        have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
  -- THE τ-FREE BOUND MAKES THE FAMILY PRECOMPACT (Bolzano-Weierstrass for bilinear forms).
  obtain ⟨X, φ, hφ, hconvj⟩ := BilinearFormBolzanoWeierstrass N Lam Xf hnorm
  -- pointwise convergence of the extracted subsequence
  have hev : ∀ (j : Fin N) (a b : E),
      Filter.Tendsto (fun k => Xf (φ k) j a b) Filter.atTop (nhds (X j a b)) := by
    intro j a b
    have hc : Continuous fun T : E →L[ℝ] E →L[ℝ] ℝ => T a b :=
      ((ContinuousLinearMap.apply ℝ ℝ b).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)).continuous
    exact (hc.tendsto (X j)).comp (hconvj j)
  refine ⟨X, ?_, ?_, ?_⟩
  · -- the limit of symmetric forms is symmetric
    intro j a b
    have h1 := hev j a b
    have h2 := hev j b a
    have heq : (fun k => Xf (φ k) j a b) = fun k => Xf (φ k) j b a := by
      funext k
      exact hsym (φ k) j a b
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  · -- the closed superjet absorbs the limit (Part I(D))
    intro j
    refine (ClosedSuperjetClosed (g j) (ofLp Z j)).mem_of_tendsto
      (b := Filter.atTop) (f := fun k => ((ofLp (∇ Ψ Z) j), Xf (φ k) j)) ?_
      (Filter.Eventually.of_forall (fun k => hjet (φ k) j))
    exact Filter.Tendsto.prodMk_nhds tendsto_const_nhds (hconvj j)
  · -- the τ-terms drop out of the matrix inequality
    intro ζ
    have hlhs : Filter.Tendsto (fun k => ∑ j, Xf (φ k) j (ofLp ζ j) (ofLp ζ j))
        Filter.atTop (nhds (∑ j, X j (ofLp ζ j) (ofLp ζ j))) :=
      tendsto_finsetSum _ (fun j _ => hev j (ofLp ζ j) (ofLp ζ j))
    have hτ0 : Filter.Tendsto (fun k : ℕ => 1 / ((φ k : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hc1 : Continuous fun t : ℝ =>
        (fderiv ℝ (fderiv ℝ Ψ) Z) ζ + t • innerSL ℝ ζ :=
      continuous_const.add (continuous_id.smul (continuous_const (y := innerSL ℝ ζ)))
    have hc2 : Continuous fun t : ℝ => ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ + t • innerSL ℝ ζ‖ :=
      Continuous.norm (f := fun t : ℝ => (fderiv ℝ (fderiv ℝ Ψ) Z) ζ + t • innerSL ℝ ζ) hc1
    have hcf : Continuous fun t : ℝ =>
        ((fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ + t * ‖ζ‖ ^ 2)
          + η * ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ + t • innerSL ℝ ζ‖ ^ 2 :=
      (continuous_const.add (continuous_id.mul continuous_const)).add
        (continuous_const.mul (hc2.pow 2))
    have hrhs := (hcf.tendsto 0).comp hτ0
    have h0 : ((fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ + (0:ℝ) * ‖ζ‖ ^ 2)
          + η * ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ + (0:ℝ) • innerSL ℝ ζ‖ ^ 2
        = (fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ + η * ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖ ^ 2 := by
      simp
    rw [h0] at hrhs
    exact le_of_tendsto_of_tendsto' hlhs hrhs (fun k => hform (φ k) ζ)
