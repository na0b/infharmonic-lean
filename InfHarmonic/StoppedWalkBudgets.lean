module

public import InfHarmonic.IsContactWalk
public import InfHarmonic.IsMarkData
public import InfHarmonic.ContactWalkExists
public import InfHarmonic.ContactWalkBudgets
public import InfHarmonic.ContactWalkMarkData

@[expose] public section
-- The four standing hypotheses `hWsub`, `hsand`, `hconc` and `hgap` belong to the
-- approved statement of this node but are not consumed by the assembly below, so the
-- unused-variable linter is switched off for this declaration.
set_option linter.unusedVariables false
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 6.7, part 1: for the pair supplied by the extremal envelope
contact there is a constant `C_*`, independent of `N`, `R` and `T`, such that
for every box a stopped contact walk exists and satisfies the stopped
expectation bound (6.18) at every stopping time below `τ` and the error budget
(6.19) with `B₀ = C_* L(B)⁴`, `B = R + T + 2`. -/
theorem StoppedWalkBudgets (C₀ κ H : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 < κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ))
    (hWsub : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} (ContactEnv v κ))
    (hsand : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧ ContactEnv v κ z ≤ v z)
    (hW0 : ContactEnv v κ (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hv0 : v (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hconc : ∀ t : ℝ, 0 < t → ConcaveOn ℝ (Set.univ : Set F)
      (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t)))
    (hgap : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z = v z →
      (BaryEnv v (ofLp z).2 z - v z) / (ofLp z).2 = κ ^ 2 / 2)
    (hham : EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal))
    (hslope : Tendsto (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 H)) :
    ∃ Cstar : ℝ, 0 < Cstar ∧
      ∀ T : ℕ, 2 ≤ T → ∀ R : ℝ, 2 ≤ R → ∀ N : ℕ, 1 ≤ N →
        ∃ (ε : ℝ) (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω)
          (𝒢 : Filtration ℕ m0) (ξ : ℕ → Ω → ℝ)
          (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ),
          IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ ∧
          (∀ σ : Ω → ℕ, IsStoppingTime 𝒢 (fun ω => (σ ω : ℕ∞)) → (∀ ω, σ ω ≤ τ ω) →
            Integrable (fun ω => JGap v κ ε (z (σ ω) ω)) μ ∧
            JGap v κ ε (toLp 2 ((0 : F), (1 : ℝ)))
              ≤ ∫ ω, JGap v κ ε (z (σ ω) ω) ∂μ) ∧
          Integrable (fun ω => ∑ n ∈ Finset.range (τ ω),
            (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) μ ∧
          ∫ ω, (∑ n ∈ Finset.range (τ ω),
            (‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
              + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2)) ∂μ
            ≤ Cstar * (1 + Real.log (R + (T : ℝ) + 2)) ^ 4 ∧
          ∃ (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (aj : ℕ → Ω → ℝ),
            IsMarkData C₀ v N 𝒢 z τ smark pj aj := by
  obtain ⟨Cstar, hCstar0, hbudget⟩ :=
    ContactWalkBudgets C₀ κ H hC₀ hκ v hv hcent hJ hWcont hWgrow
  refine ⟨Cstar, hCstar0, ?_⟩
  intro T hT R hR N hN
  obtain ⟨ε, Ω, m0, μ, 𝒢, ξ, z, zp, zm, Q₀, τ, hcw, hcount⟩ :=
    ContactWalkExists C₀ κ H hC₀ hκ v hv hcent hJ hWcont hWgrow hW0 hv0 hham hslope T hT R hR N hN
  have hb := hbudget T hT R hR N hN ε Ω m0 μ 𝒢 ξ z zp zm Q₀ τ hcw
  exact ⟨ε, Ω, m0, μ, 𝒢, ξ, z, zp, zm, Q₀, τ, hcw, hb.1, hb.2.1, hb.2.2,
    ContactWalkMarkData C₀ κ H v hv T R N ε Ω m0 μ 𝒢 ξ z zp zm Q₀ τ hcw hcount⟩
