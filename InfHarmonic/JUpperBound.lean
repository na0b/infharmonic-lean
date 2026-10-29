import InfHarmonic.JGap
import InfHarmonic.EnvSlopeP
import InfHarmonic.EnvSlopeM
import InfHarmonic.IsFitClass
import InfHarmonic.IsCenteredAt
import InfHarmonic.HasJensenBound
import InfHarmonic.BaryEnvSandwich
import InfHarmonic.UniformSubquadratic
import InfHarmonic.BaryEnvDuality
import InfHarmonic.QuadEnvAttained
import InfHarmonic.EnvelopeCompetitorBounds
import InfHarmonic.ContactEnv
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (6.3): the propagation quantity is at most the average of the two
envelope slopes of `v`. -/
theorem JUpperBound (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ) :
    ∀ (ε : ℝ) (z : WithLp 2 (F × ℝ)), 0 < ε → 0 < (ofLp z).2 →
      JGap v κ ε z ≤ (EnvSlopeP v ε z + EnvSlopeM v ε z) / 2 := by
  classical
  -- ===== Step 0: the two regularity facts for `v` on all of space-time =====
  have hIuniv : ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvcont : ContinuousOn v
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hv.1.1.2.1
  have hgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc δ hδ
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc δ hδ
    exact ⟨M, hM0, fun ζ hζ hζJ => hMb v hv hcent ζ hζ hζJ⟩
  -- ===== Step 1: `W ≤ v` at every positive time =====
  have hWle : ∀ (y : F) (σ : ℝ), 0 < σ →
      ContactEnv v κ (toLp 2 (y, σ)) ≤ v (toLp 2 (y, σ)) := by
    intro y σ hσ
    have hs := (BaryEnvSandwich (Set.univ : Set ℝ) v κ hκ hvcont hJ hgrow σ
      (toLp 2 (y, σ)) hσ (Set.mem_univ _)).2
    have he : ContactEnv v κ (toLp 2 (y, σ))
        = BaryEnv v σ (toLp 2 (y, σ)) - κ ^ 2 * σ / 2 := by
      rw [ContactEnv]
    rw [he]
    linarith
  -- ===== Step 2: the forward envelope is monotone in the function =====
  intro ε z hε hzt
  have hεne : ε ≠ 0 := ne_of_gt hε
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have hte : (0 : ℝ) < (ofLp z).2 + ε := by linarith
  -- the competitor set of `W`, and the licence for `v`'s own competitors.  Attainment
  -- of the supremum for `v` is NOT what bounds `A_v`: it is an equality with one
  -- element, which under the preamble's `sup` convention does not dominate the others.
  -- Part (1) of EnvelopeCompetitorBounds states the domination itself.
  have hdom := ((EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont hgrow).1 ε z hε
    (Set.mem_univ _) (Set.mem_univ _)).1
  have hQW : QuadEnvP (ContactEnv v κ) ε z
      = sSup {w : ℝ | ∃ y : F, w = ContactEnv v κ (toLp 2 (y, (ofLp z).2 + ε))
          - ‖y - (ofLp z).1‖ ^ 2 / (2 * ε)} := by
    rw [QuadEnvP, if_neg hεne]
  have hub : ∀ w ∈ {w : ℝ | ∃ y : F, w = ContactEnv v κ (toLp 2 (y, (ofLp z).2 + ε))
      - ‖y - (ofLp z).1‖ ^ 2 / (2 * ε)}, w ≤ QuadEnvP v ε z := by
    rintro w ⟨y, rfl⟩
    have h1 := hWle y ((ofLp z).2 + ε) hte
    have h2 := hdom y
    linarith
  have hne : ({w : ℝ | ∃ y : F, w = ContactEnv v κ (toLp 2 (y, (ofLp z).2 + ε))
      - ‖y - (ofLp z).1‖ ^ 2 / (2 * ε)}).Nonempty := ⟨_, ⟨(ofLp z).1, rfl⟩⟩
  have hstep2 : QuadEnvP (ContactEnv v κ) ε z ≤ QuadEnvP v ε z := by
    rw [hQW]
    exact csSup_le hne hub
  -- ===== Step 3: insert `v z` and split.  The backward envelope appears unchanged on
  -- both sides and cancels, so no statement about `M_ε v` is needed here. =====
  have hkey : ((QuadEnvP v ε z - v z) / ε + (v z - QuadEnvM v ε z) / ε) / 2
      = (QuadEnvP v ε z - QuadEnvM v ε z) / (2 * ε) := by
    field_simp
    ring
  rw [JGap, EnvSlopeP, EnvSlopeM, hkey, div_le_div_iff₀ h2ε h2ε]
  exact mul_le_mul_of_nonneg_right (by linarith) h2ε.le
