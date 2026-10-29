module

public import InfHarmonic.Preamble

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The resolvent package used by the theorem of sums: for a self-adjoint `B` and
`ε > 0` with `ε ‖B‖ ≤ 1/2` the operator `Aeps = B (id - ε B)⁻¹` exists, is
self-adjoint, satisfies the two resolvent identities, makes `ε⁻¹ id + Aeps`
positive definite, has norm at most `2 ‖B‖`, and dominates `B` only up to the
quadratic correction `η ‖B ζ‖²` whenever `2 ε ≤ η`. -/
theorem SumRuleResolvent (B : E →L[ℝ] E)
    (hB : ∀ ξ ζ : E, inner ℝ (B ξ) ζ = inner ℝ ξ (B ζ))
    (ε : ℝ) (hε : 0 < ε) (hεB : ε * ‖B‖ ≤ 1 / 2) :
    ∃ Aeps : E →L[ℝ] E,
      (∀ ξ ζ : E, inner ℝ (Aeps ξ) ζ = inner ℝ ξ (Aeps ζ)) ∧
      (∀ ξ : E, Aeps ξ = B (ξ + ε • Aeps ξ)) ∧
      (∀ ξ : E, (ξ + ε • Aeps ξ) - ε • B (ξ + ε • Aeps ξ) = ξ) ∧
      (∀ ξ : E, ξ ≠ 0 → 0 < (inner ℝ ξ ξ : ℝ) / ε + inner ℝ (Aeps ξ) ξ) ∧
      ‖Aeps‖ ≤ 2 * ‖B‖ ∧
      (∀ η : ℝ, 2 * ε ≤ η → ∀ ζ : E,
        (inner ℝ (Aeps ζ) ζ : ℝ) ≤ inner ℝ (B ζ) ζ + η * ‖B ζ‖ ^ 2) := by
  -- THE LEAN ROUTE IS SHORTER THAN THE .tex's AND NEEDS NEITHER THE NEUMANN SERIES NOR THE
  -- SPECTRAL THEOREM.  Recorded here because it is reusable.
  -- (a) Invertibility: `S = id - ε B` satisfies ⟪S ξ, ξ⟫ ≥ ‖ξ‖²/2 (from ε‖B‖ ≤ 1/2), so it is
  --     injective, hence bijective in finite dimensions, and `ContinuousLinearEquiv.ofBijective`
  --     hands back a CONTINUOUS two-sided inverse `T`.  No series is summed.
  -- (b) ‖T‖ ≤ 2 comes from the same lower bound: ‖ξ‖²/2 ≤ ⟪Sξ,ξ⟫ ≤ ‖Sξ‖‖ξ‖ gives
  --     ‖ξ‖ ≤ 2‖Sξ‖, and at ξ = T ζ that is ‖T ζ‖ ≤ 2‖ζ‖.
  -- (c) (R6) NEEDS NO EIGENBASIS.  From `T ξ = ξ + ε B (T ξ)` and `B T = T B` one gets the
  --     operator identity  A_ε = B + ε B T B, hence, with w = B ζ,
  --         ⟪A_ε ζ, ζ⟫ = ⟪B ζ, ζ⟫ + ε ⟪T w, w⟫,
  --     and ⟪T w, w⟫ ≤ ‖T w‖‖w‖ ≤ 2‖w‖² by (b).  So ε⟪T w,w⟫ ≤ 2ε‖w‖² ≤ η‖w‖² whenever
  --     2ε ≤ η -- the whole eigenvalue computation of the .tex collapses to Cauchy-Schwarz.
  have _ : FiniteDimensional ℝ E := inferInstance
  have hBn : (0:ℝ) ≤ ‖B‖ := norm_nonneg B
  -- (1) S = id - ε B, with its lower bound
  obtain ⟨S, hSdef⟩ : ∃ S : E →L[ℝ] E, S = ContinuousLinearMap.id ℝ E - ε • B := ⟨_, rfl⟩
  have hSapp : ∀ ξ : E, S ξ = ξ - ε • B ξ := by
    intro ξ
    rw [hSdef]
    simp
  have hSsa : ∀ ξ ζ : E, (inner ℝ (S ξ) ζ : ℝ) = inner ℝ ξ (S ζ) := by
    intro ξ ζ
    rw [hSapp, hSapp, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hB ξ ζ]
  have hBcs : ∀ ξ : E, (inner ℝ (B ξ) ξ : ℝ) ≤ ‖B‖ * ‖ξ‖ ^ 2 := by
    intro ξ
    have h1 := real_inner_le_norm (B ξ) ξ
    have h2 := B.le_opNorm ξ
    nlinarith [norm_nonneg ξ, norm_nonneg (B ξ)]
  have hSlow : ∀ ξ : E, ‖ξ‖ ^ 2 / 2 ≤ (inner ℝ (S ξ) ξ : ℝ) := by
    intro ξ
    rw [hSapp, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    nlinarith [mul_le_mul_of_nonneg_left (hBcs ξ) hε.le,
      mul_le_mul_of_nonneg_right hεB (show (0:ℝ) ≤ ‖ξ‖ ^ 2 by positivity)]
  -- (2) S is bijective, so it has a continuous two-sided inverse
  have hker : LinearMap.ker (S : E →ₗ[ℝ] E) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro ξ hξ
    have h1 := hSlow ξ
    rw [show S ξ = 0 from hξ, inner_zero_left] at h1
    have h2 : ‖ξ‖ = 0 := by nlinarith [norm_nonneg ξ]
    exact norm_eq_zero.mp h2
  have hrange : LinearMap.range (S : E →ₗ[ℝ] E) = ⊤ :=
    LinearMap.ker_eq_bot_iff_range_eq_top.mp hker
  obtain ⟨T, hTS, hST⟩ : ∃ T : E →L[ℝ] E, (∀ ξ : E, T (S ξ) = ξ) ∧ (∀ ξ : E, S (T ξ) = ξ) :=
    ⟨(ContinuousLinearEquiv.ofBijective S hker hrange).symm.toContinuousLinearMap,
      fun ξ => ContinuousLinearEquiv.ofBijective_symm_apply_apply S hker hrange ξ,
      fun ξ => ContinuousLinearEquiv.ofBijective_apply_symm_apply S hker hrange ξ⟩
  -- (3) T is self-adjoint, bounded by 2, and commutes with B
  have hTsa : ∀ ξ ζ : E, (inner ℝ (T ξ) ζ : ℝ) = inner ℝ ξ (T ζ) := by
    intro ξ ζ
    calc (inner ℝ (T ξ) ζ : ℝ) = inner ℝ (T ξ) (S (T ζ)) := by rw [hST ζ]
      _ = inner ℝ (S (T ξ)) (T ζ) := (hSsa (T ξ) (T ζ)).symm
      _ = inner ℝ ξ (T ζ) := by rw [hST ξ]
  have hTb : ∀ ζ : E, ‖T ζ‖ ≤ 2 * ‖ζ‖ := by
    intro ζ
    have h1 := hSlow (T ζ)
    rw [hST ζ] at h1
    have h2 := real_inner_le_norm (T ζ) ζ
    have h3 : (inner ℝ ζ (T ζ) : ℝ) = inner ℝ (T ζ) ζ := real_inner_comm (T ζ) ζ
    nlinarith [norm_nonneg (T ζ), norm_nonneg ζ, h1, h2, h3]
  have hTnorm : ‖T‖ ≤ 2 :=
    ContinuousLinearMap.opNorm_le_bound _ (by norm_num) hTb
  have hBS : ∀ ξ : E, B (S ξ) = S (B ξ) := by
    intro ξ
    rw [hSapp, hSapp, map_sub, map_smul]
  have hBT : ∀ ξ : E, B (T ξ) = T (B ξ) := by
    intro ξ
    calc B (T ξ) = T (S (B (T ξ))) := (hTS (B (T ξ))).symm
      _ = T (B (S (T ξ))) := by rw [hBS (T ξ)]
      _ = T (B ξ) := by rw [hST ξ]
  -- (4) the resolvent expansion T ξ = ξ + ε • B (T ξ)
  have hTexp : ∀ ξ : E, T ξ = ξ + ε • B (T ξ) := by
    intro ξ
    have h1 : T ξ - ε • B (T ξ) = ξ := by
      rw [← hSapp (T ξ)]
      exact hST ξ
    exact sub_eq_iff_eq_add.mp h1
  -- (5) the witness
  refine ⟨B.comp T, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (R1) self-adjointness of B T, using B T = T B
    intro ξ ζ
    show (inner ℝ (B (T ξ)) ζ : ℝ) = inner ℝ ξ (B (T ζ))
    calc (inner ℝ (B (T ξ)) ζ : ℝ) = inner ℝ (T ξ) (B ζ) := hB (T ξ) ζ
      _ = inner ℝ ξ (T (B ζ)) := hTsa ξ (B ζ)
      _ = inner ℝ ξ (B (T ζ)) := by rw [hBT ζ]
  · -- (R2)
    intro ξ
    show B (T ξ) = B (ξ + ε • B (T ξ))
    rw [← hTexp ξ]
  · -- (R3)
    intro ξ
    show (ξ + ε • B (T ξ)) - ε • B (ξ + ε • B (T ξ)) = ξ
    rw [← hTexp ξ]
    have h1 : T ξ - ε • B (T ξ) = S (T ξ) := (hSapp (T ξ)).symm
    rw [h1, hST ξ]
  · -- (R4) positivity of ε⁻¹ id + A_ε, which is ε⁻¹ T
    intro ξ hξ
    show 0 < (inner ℝ ξ ξ : ℝ) / ε + inner ℝ (B (T ξ)) ξ
    have hTne : T ξ ≠ 0 := by
      intro h0
      have h1 := hST ξ
      rw [h0, map_zero] at h1
      exact hξ h1.symm
    have h2 := hSlow (T ξ)
    rw [hST ξ] at h2
    have h3 : (0:ℝ) < ‖T ξ‖ ^ 2 / 2 := by
      have hpos := norm_pos_iff.mpr hTne
      positivity
    have hcomm : (inner ℝ ξ (T ξ) : ℝ) = inner ℝ (T ξ) ξ := real_inner_comm (T ξ) ξ
    have h5 : (0:ℝ) < (inner ℝ (T ξ) ξ : ℝ) := by
      rw [← hcomm]
      linarith
    have h4 : (inner ℝ (T ξ) ξ : ℝ) = inner ℝ ξ ξ + ε * inner ℝ (B (T ξ)) ξ := by
      conv_lhs => rw [hTexp ξ]
      rw [inner_add_left, real_inner_smul_left]
    rw [h4] at h5
    have h6 := div_pos h5 hε
    rw [show ((inner ℝ ξ ξ : ℝ) + ε * inner ℝ (B (T ξ)) ξ) / ε
        = (inner ℝ ξ ξ : ℝ) / ε + inner ℝ (B (T ξ)) ξ from by field_simp] at h6
    exact h6
  · -- (R5)
    calc ‖B.comp T‖ ≤ ‖B‖ * ‖T‖ := ContinuousLinearMap.opNorm_comp_le B T
      _ ≤ ‖B‖ * 2 := mul_le_mul_of_nonneg_left hTnorm hBn
      _ = 2 * ‖B‖ := by ring
  · -- (R6) the comparison, by Cauchy-Schwarz on T at the vector B ζ
    intro η hη ζ
    show (inner ℝ (B (T ζ)) ζ : ℝ) ≤ inner ℝ (B ζ) ζ + η * ‖B ζ‖ ^ 2
    have hid : (inner ℝ (B (T ζ)) ζ : ℝ)
        = inner ℝ (B ζ) ζ + ε * inner ℝ (T (B ζ)) (B ζ) := by
      calc (inner ℝ (B (T ζ)) ζ : ℝ) = inner ℝ (T ζ) (B ζ) := hB (T ζ) ζ
        _ = inner ℝ (ζ + ε • B (T ζ)) (B ζ) := by rw [← hTexp ζ]
        _ = inner ℝ ζ (B ζ) + ε * inner ℝ (B (T ζ)) (B ζ) := by
            rw [inner_add_left, real_inner_smul_left]
        _ = inner ℝ (B ζ) ζ + ε * inner ℝ (T (B ζ)) (B ζ) := by
            rw [real_inner_comm ζ (B ζ), hBT ζ]
    have hcs : (inner ℝ (T (B ζ)) (B ζ) : ℝ) ≤ 2 * ‖B ζ‖ ^ 2 := by
      have h1 := real_inner_le_norm (T (B ζ)) (B ζ)
      have h2 := hTb (B ζ)
      nlinarith [norm_nonneg (B ζ), norm_nonneg (T (B ζ))]
    rw [hid]
    nlinarith [hcs, hε, hη, sq_nonneg ‖B ζ‖]
