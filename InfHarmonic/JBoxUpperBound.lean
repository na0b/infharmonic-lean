module

public import InfHarmonic.JUpperBound
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.EnvHamiltonianSolution
public import InfHarmonic.UniformSubquadratic

@[expose] public section
open Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 7 of Proposition 6.8: on a compact set of space-time the propagation
quantity `J_ε` is bounded above by one constant, uniformly over all lengths
`0 < ε ≤ 1` and all states of positive time in the set. -/
theorem JBoxUpperBound (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (B : Set (WithLp 2 (F × ℝ))) (hB : IsCompact B) :
    ∃ U : ℝ, ∀ z ∈ B, 0 < (ofLp z).2 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      JGap v κ ε z ≤ U := by
  have hcont : ContinuousOn v ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hv.1.1.2.1
  have hgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc ε hε
    obtain ⟨M, hM, hbd⟩ :=
      UniformSubquadratic C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc ε hε
    exact ⟨M, hM, fun z hz1 hz2 => hbd v hv hcent z hz1 hz2⟩
  obtain ⟨-, -, hcP, hcM, -, -⟩ := QuadEnvAttained (F := F) Set.univ isOpen_univ v hcont hgrow
  have hPc : Continuous fun z : WithLp 2 (F × ℝ) => QuadEnvP v 1 z := by
    rw [continuous_iff_continuousAt]
    intro z₀
    exact (hcP 1 one_pos z₀ (Set.mem_univ _) (Set.mem_univ _)).comp
      (by fun_prop : ContinuousAt (fun z : WithLp 2 (F × ℝ) => ((1 : ℝ), z)) z₀)
  have hMc : Continuous fun z : WithLp 2 (F × ℝ) => QuadEnvM v 1 z := by
    rw [continuous_iff_continuousAt]
    intro z₀
    exact (hcM 1 one_pos z₀ (Set.mem_univ _) (Set.mem_univ _)).comp
      (by fun_prop : ContinuousAt (fun z : WithLp 2 (F × ℝ) => ((1 : ℝ), z)) z₀)
  set Φ : WithLp 2 (F × ℝ) → ℝ :=
    fun z => (EnvSlopeP v 1 z + EnvSlopeM v 1 z) / 2 with hΦ
  have hΦc : Continuous Φ := by
    have hrw : Φ = fun z => (QuadEnvP v 1 z - QuadEnvM v 1 z) / 2 := by
      funext z
      simp only [hΦ, EnvSlopeP, EnvSlopeM, div_one]
      ring
    rw [hrw]
    fun_prop
  obtain ⟨hmono, -, -, -⟩ :=
    EnvHamiltonianSolution (F := F) Set.univ isOpen_univ v hcont hgrow hv.1
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · exact ⟨0, fun z hz => absurd hz (by simp [hBe])⟩
  obtain ⟨zm, hzm, hmax⟩ := hB.exists_isMaxOn hBne hΦc.continuousOn
  refine ⟨Φ zm, fun z hz hzt ε hε hε1 => ?_⟩
  have h1 := JUpperBound C₀ κ hC₀ hκ v hv hcent hJ ε z hε hzt
  have h2 := hmono z ε 1 hε hε1 (fun σ _ => Set.mem_univ _)
  have h3 : Φ z ≤ Φ zm := hmax hz
  have h4 : (EnvSlopeP v ε z + EnvSlopeM v ε z) / 2 ≤ Φ z := by
    simp only [hΦ]
    linarith [h2.1, h2.2]
  linarith
