import InfHarmonic.ContactEnv
import InfHarmonic.IsFitClass
import InfHarmonic.IsCenteredAt
import InfHarmonic.HasJensenBound
import InfHarmonic.BaryEnvDuality
import InfHarmonic.BaryEnvSandwich
import InfHarmonic.UniformSubquadratic
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The contact envelope is continuous and subquadratic on positive times.  For a member
of the fit class satisfying the horizontal Jensen bound, the barycentric sandwich pins the
contact envelope `W = C_t v - κ²t/2` between `v - κ²t/2` and `v` at every positive time,
which transfers the subquadratic spatial growth of `v` to `W` on compact subintervals of
`(0, ∞)`; continuity comes from continuity of the barycentric envelope in its parameter
and its point jointly.  These are exactly the two hypotheses the quadratic-envelope
attainment lemma asks of its integrand. -/
theorem ContactEnvPositiveTimeRegularity (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ) :
    ContinuousOn (ContactEnv v κ)
        ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.Ioi (0:ℝ))
      ∧ SubquadraticGrowth (Set.Ioi (0:ℝ)) (ContactEnv v κ)
      ∧ ∀ σ : ℝ, 0 < σ → ConcaveOn ℝ (Set.univ : Set F)
          (fun y : F => ContactEnv v κ (toLp 2 (y, σ)) - ‖y‖ ^ 2 / (2 * σ)) := by
  classical
  -- `BaryEnvDuality` is stated for a Borel-measurable `F`, because one of its clauses
  -- speaks about probability measures.  This node's statement carries no measurable
  -- structure and needs none: give `F` its Borel σ-algebra locally.  The clause used
  -- below mentions no measure, so the choice is immaterial.
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  -- `v` is continuous and subquadratic on all of space-time
  have hvcont : ContinuousOn v Set.univ := hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc ε hε
    obtain ⟨M, hM, hMb⟩ := UniformSubquadratic C₀ hC₀ (toLp 2 ((0:F), (1:ℝ)))
      (Or.inr rfl) J hJc ε hε
    exact ⟨M, hM, fun z hz hzJ => hMb v hv hcent z hz hzJ⟩
  have hvcont' : ContinuousOn v ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) :=
    hvcont
  -- the barycentric sandwich at the running time
  have hsand := BaryEnvSandwich (Set.univ : Set ℝ) v κ hκ hvcont' hJ hvgrow
  have hfs : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧ ContactEnv v κ z ≤ v z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsand (ofLp z).2 z hz (Set.mem_univ _)
    rw [ContactEnv]
    constructor <;> linarith
  obtain ⟨_, _, hconv, hconc0, _⟩ :=
    BaryEnvDuality (Set.univ : Set ℝ) isOpen_univ v hvcont' hvgrow
  refine ⟨?_, ?_, ?_⟩
  · -- continuity, from joint continuity of the barycentric envelope
    intro z₀ hz₀
    refine ContinuousAt.continuousWithinAt ?_
    have hz₀' : 0 < (ofLp z₀).2 := hz₀
    have h1 : ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => BaryEnv v p.1 p.2)
        ((ofLp z₀).2, z₀) := hconv _ hz₀' z₀ (Set.mem_univ _)
    have h2 : Continuous (fun z : WithLp 2 (F × ℝ) => ((ofLp z).2, z)) :=
      ((continuous_snd.comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous).prodMk continuous_id)
    have h3 : ContinuousAt (fun z : WithLp 2 (F × ℝ) => BaryEnv v (ofLp z).2 z) z₀ := by
      have h := Filter.Tendsto.comp h1 (h2.continuousAt (x := z₀))
      exact h
    have h4 : ContinuousAt (fun z : WithLp 2 (F × ℝ) => κ ^ 2 * (ofLp z).2 / 2) z₀ := by
      refine ContinuousAt.div_const (continuousAt_const.mul ?_) 2
      exact (continuous_snd.comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous).continuousAt
    have h5 : ContinuousAt (ContactEnv v κ) z₀ := by
      have : ContactEnv v κ
          = fun z : WithLp 2 (F × ℝ) => BaryEnv v (ofLp z).2 z - κ ^ 2 * (ofLp z).2 / 2 := by
        funext z; rw [ContactEnv]
      rw [this]
      exact h3.sub h4
    exact h5
  · -- subquadratic growth, transferred through the sandwich
    intro J hJI hJc ε hε
    rcases Set.eq_empty_or_nonempty J with hJe | hJne
    · refine ⟨1, one_pos, fun z _ hzJ => ?_⟩
      rw [hJe] at hzJ
      simp at hzJ
    obtain ⟨τm, hτmJ, hτmle⟩ := hJc.exists_isGreatest hJne
    have hτm0 : 0 < τm := hJI hτmJ
    obtain ⟨M, hM, hMb⟩ := hvgrow J (Set.subset_univ _) hJc (ε / 2) (by positivity)
    obtain ⟨A, hAd⟩ : ∃ A : ℝ, A = κ ^ 2 * τm / ε := ⟨_, rfl⟩
    have hA0 : 0 ≤ A := by rw [hAd]; positivity
    obtain ⟨M', hM'd⟩ : ∃ r : ℝ, r = max M (Real.sqrt A + 1) := ⟨_, rfl⟩
    have hM'0 : 0 < M' := by rw [hM'd]; exact lt_max_of_lt_left hM
    have hMM' : M ≤ M' := by rw [hM'd]; exact le_max_left _ _
    have hM'sq : A ≤ M' ^ 2 := by
      have h1 : Real.sqrt A + 1 ≤ M' := by rw [hM'd]; exact le_max_right _ _
      have h2 : (0:ℝ) ≤ Real.sqrt A + 1 := by positivity
      nlinarith [Real.sq_sqrt hA0, Real.sqrt_nonneg A, mul_le_mul h1 h1 h2 hM'0.le]
    refine ⟨M', hM'0, fun z hz hzJ => ?_⟩
    have hzM : M ≤ ‖(ofLp z).1‖ := le_trans hMM' hz
    have hvb := hMb z hzM hzJ
    have hτ : (ofLp z).2 ≤ τm := hτmle hzJ
    have hzt : 0 < (ofLp z).2 := hJI hzJ
    obtain ⟨hl, hu⟩ := hfs z hzt
    -- `|f| ≤ |v| + κ²τ/2`, and the extra term is absorbed by enlarging the radius
    have hcorr : κ ^ 2 * (ofLp z).2 / 2 ≤ ε / 2 * M' ^ 2 := by
      have h1 : κ ^ 2 * (ofLp z).2 / 2 ≤ κ ^ 2 * τm / 2 := by
        have : (0:ℝ) ≤ κ ^ 2 := sq_nonneg κ
        nlinarith [hτ]
      have hεne : ε ≠ 0 := ne_of_gt hε
      have h2 : κ ^ 2 * τm / 2 = ε / 2 * A := by
        rw [hAd]; field_simp
      nlinarith [hM'sq, hε, h2.le]
    have habs := abs_le.mp hvb
    have hM'le : ε / 2 * M' ^ 2 ≤ ε / 2 * ‖(ofLp z).1‖ ^ 2 := by
      have h1 : M' ^ 2 ≤ ‖(ofLp z).1‖ ^ 2 := by nlinarith [hz, hM'0]
      nlinarith [hε, h1]
    rw [abs_le]
    constructor <;> nlinarith [habs.1, habs.2, hl, hu, hcorr, hM'le]
  · -- concavity after the quadratic correction, from the barycentric concavity
    intro σ hσ
    have h := hconc0 σ σ hσ (Set.mem_univ _)
    refine ⟨convex_univ, fun y₀ _ y₁ _ α β hα hβ hαβ => ?_⟩
    have h1 := h.2 (Set.mem_univ y₀) (Set.mem_univ y₁) hα hβ hαβ
    have hce : ∀ y : F, ContactEnv v κ (toLp 2 (y, σ)) - ‖y‖ ^ 2 / (2 * σ)
        = (BaryEnv v σ (toLp 2 (y, σ)) - ‖y‖ ^ 2 / (2 * σ)) - κ ^ 2 * σ / 2 := by
      intro y; rw [ContactEnv]; ring
    show α • (ContactEnv v κ (toLp 2 (y₀, σ)) - ‖y₀‖ ^ 2 / (2 * σ))
        + β • (ContactEnv v κ (toLp 2 (y₁, σ)) - ‖y₁‖ ^ 2 / (2 * σ))
      ≤ ContactEnv v κ (toLp 2 (α • y₀ + β • y₁, σ))
          - ‖α • y₀ + β • y₁‖ ^ 2 / (2 * σ)
    rw [hce y₀, hce y₁, hce (α • y₀ + β • y₁)]
    have hc : α * (κ ^ 2 * σ / 2) + β * (κ ^ 2 * σ / 2) = κ ^ 2 * σ / 2 := by
      rw [← add_mul, hαβ, one_mul]
    simp only [smul_eq_mul] at h1 ⊢
    linarith [h1, hc]
