module

public import InfHarmonic.JGap
public import InfHarmonic.IsFitClass
public import InfHarmonic.IsCenteredAt
public import InfHarmonic.HasJensenBound
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.BaryEnvSandwich
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.BaryEnvDuality
public import InfHarmonic.ContactEnv
public import InfHarmonic.ContactEnvPositiveTimeRegularity

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (6.2) and its consequence: the exact decomposition of
`2 ε J_ε` and the uniform convergence `2 ε J_ε → W - v` on compact subsets
of positive time. -/
theorem ContactGapLimit (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ) :
    (∀ (ε : ℝ) (z : WithLp 2 (F × ℝ)), 0 < ε →
        2 * ε * JGap v κ ε z
          = (ContactEnv v κ z - v z)
            + (QuadEnvP (ContactEnv v κ) ε z - ContactEnv v κ z)
            + (v z - QuadEnvM v ε z)) ∧
    (∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K → (∀ z ∈ K, 0 < (ofLp z).2) →
        ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ z ∈ K,
          |2 * ε * JGap v κ ε z - (ContactEnv v κ z - v z)| ≤ δ) := by
  classical
  -- the `I = ℝ` boilerplate for `v`
  have hIuniv : ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvcont : ContinuousOn v
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc η hη
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc η hη
    exact ⟨M, hM0, fun ζ hζ hζJ => hMb v hv hcent ζ hζ hζJ⟩
  -- the two admissibility facts for `W = ContactEnv v κ` on positive time: continuity on
  -- the positive-time slab and subquadratic spatial growth there.  Both are conjuncts of
  -- ContactEnvPositiveTimeRegularity, under exactly this node's own hypotheses, so
  -- neither the composition through `z ↦ ((ofLp z).2, z)` nor the enlargement of the
  -- growth radius that absorbs the additive `κ²t/2` has to be redone here.
  obtain ⟨hWcont, hWgrow, -⟩ :=
    ContactEnvPositiveTimeRegularity C₀ κ hC₀ hκ v hv hcent hJ
  -- the uniform zero-length convergence, for `v` on `ℝ` and for `W` on `(0, ∞)`
  obtain ⟨-, -, -, -, hcollv, -⟩ :=
    QuadEnvAttained (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow
  obtain ⟨-, -, -, -, hcollW, -⟩ :=
    QuadEnvAttained (Set.Ioi (0 : ℝ)) isOpen_Ioi (ContactEnv v κ) hWcont hWgrow
  refine ⟨?_, ?_⟩
  · -- (1): pure algebra.  `2ε J_ε = P_ε W - M_ε v` by JGap, and on the right side the
    -- terms `W z` and `v z` cancel in pairs; no envelope fact is used, and by the
    -- junk-value convention nothing needs licensing because only realness is involved.
    intro ε z hε
    have hεne : ε ≠ 0 := ne_of_gt hε
    rw [JGap]
    field_simp
    ring
  · -- (2): the identity reduces the claim to the two zero-length estimates
    intro K hKc hKt δ hδ
    obtain ⟨δ₁, hδ₁, hb1⟩ := hcollv K hKc (fun z _ => Set.mem_univ _) (δ / 2) (by linarith)
    obtain ⟨δ₂, hδ₂, hb2⟩ := hcollW K hKc (fun z hz => hKt z hz) (δ / 2) (by linarith)
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
    intro ε hε hεlt z hz
    have hεne : ε ≠ 0 := ne_of_gt hε
    have h1 := (hb1 ε hε (lt_of_lt_of_le hεlt (min_le_left _ _)) z hz).2
    have h2 := (hb2 ε hε (lt_of_lt_of_le hεlt (min_le_right _ _)) z hz).1
    have hid : 2 * ε * JGap v κ ε z - (ContactEnv v κ z - v z)
        = (QuadEnvP (ContactEnv v κ) ε z - ContactEnv v κ z) + (v z - QuadEnvM v ε z) := by
      rw [JGap]
      field_simp
      ring
    rw [hid]
    have ha1 : |v z - QuadEnvM v ε z| ≤ δ / 2 := by
      rw [abs_sub_comm]
      exact h1
    calc |(QuadEnvP (ContactEnv v κ) ε z - ContactEnv v κ z) + (v z - QuadEnvM v ε z)|
        ≤ |QuadEnvP (ContactEnv v κ) ε z - ContactEnv v κ z| + |v z - QuadEnvM v ε z| :=
          abs_add_le _ _
      _ ≤ δ := by linarith
