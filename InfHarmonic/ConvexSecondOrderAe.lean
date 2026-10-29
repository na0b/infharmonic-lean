import InfHarmonic.MoreauProxExists
import InfHarmonic.MoreauProxMonotone
import InfHarmonic.MoreauEnvelopeGradient
import InfHarmonic.MoreauProxImageFullMeasure
import InfHarmonic.ProxEnvelopeExpansionAt
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Alexandrov's theorem: a real convex function on `E` admits a second-order
Taylor expansion at almost every point, with a nonnegative Hessian form. -/
theorem ConvexSecondOrderAe (μ : Measure E) [μ.IsAddHaarMeasure] (ψ : E → ℝ)
    (hψ : ConvexOn ℝ Set.univ ψ) :
    ∀ᵐ x ∂μ, ∃ (q : E) (A : E →L[ℝ] E →L[ℝ] ℝ),
      (∀ h k : E, A h k = A k h) ∧ (∀ h : E, 0 ≤ A h h) ∧
      ∀ δ > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
        |ψ (x + h) - ψ x - inner ℝ q h - A h h / 2| ≤ δ * ‖h‖ ^ 2 := by
  -- The proximal map, and Step 3: almost every point lies above an invertible derivative.
  obtain ⟨u, hu⟩ := MoreauProxExists ψ hψ
  obtain ⟨hnull, hdense⟩ := MoreauProxImageFullMeasure μ ψ hψ u hu
  rw [MeasureTheory.ae_iff]
  refine measure_mono_null (fun x hx => ?_) hnull
  intro hxG
  obtain ⟨y, ⟨P, hP, hdet⟩, hxy⟩ := hxG
  -- `det P ≠ 0` gives `P` a two-sided continuous linear inverse.
  have hker : LinearMap.ker (P : E →ₗ[ℝ] E) = ⊥ :=
    (LinearMap.isUnit_iff_ker_eq_bot _).mp
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
  have hsurj : LinearMap.range (P : E →ₗ[ℝ] E) = ⊤ :=
    LinearMap.ker_eq_bot_iff_range_eq_top.mp hker
  obtain ⟨Pinv, hinv, hinv'⟩ : ∃ Pinv : E →L[ℝ] E,
      (∀ z : E, Pinv (P z) = z) ∧ (∀ z : E, P (Pinv z) = z) :=
    ⟨(ContinuousLinearEquiv.ofBijective P hker hsurj).symm.toContinuousLinearMap,
      fun z => ContinuousLinearEquiv.ofBijective_symm_apply_apply P hker hsurj z,
      fun z => ContinuousLinearEquiv.ofBijective_apply_symm_apply P hker hsurj z⟩
  -- Step 5: the expansion at `u y`.
  have hexp := ProxEnvelopeExpansionAt ψ hψ u hu hdense y P Pinv hP hinv hinv' hdet
  -- `y - u y` is a subgradient at `u y`, so the remainder `g` is nonnegative.
  have hsub : ∀ k : E, ψ (u y) + inner ℝ (y - u y) k ≤ ψ (u y + k) := by
    intro k
    have h := (MoreauProxSubgradient ψ hψ y (u y)).mp (hu y) (u y + k)
    simpa using h
  -- The symmetrized continuous bilinear form attached to `A₀ = (I - P) ∘ P⁻¹`.
  obtain ⟨B, hB⟩ : ∃ B : E →L[ℝ] E →L[ℝ] ℝ, ∀ a b : E, B a b = inner ℝ a b :=
    ⟨(InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap, fun a b => rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : E →L[ℝ] E →L[ℝ] ℝ,
      M = B.comp ((ContinuousLinearMap.id ℝ E - P).comp Pinv) := ⟨_, rfl⟩
  have hMval : ∀ a b : E,
      M a b = inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv a)) b := by
    intro a b; rw [hM]; exact hB _ _
  have hAhh : ∀ h : E, ((2⁻¹ : ℝ) • (M + M.flip)) h h
      = inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv h)) h := by
    intro h
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    rw [hMval h h]
    ring
  refine hx ⟨y - u y, (2⁻¹ : ℝ) • (M + M.flip), ?_, ?_, ?_⟩
  · -- symmetry, by construction
    intro h k
    simp only [smul_apply, add_apply,
      ContinuousLinearMap.flip_apply, smul_eq_mul]
    ring
  · -- Step 6: nonnegativity, from `g ≥ 0` and the expansion
    intro h
    rw [hAhh h]
    rcases eq_or_ne h 0 with rfl | hne
    · simp
    · by_contra hneg
      rw [not_le] at hneg
      have hn : 0 < ‖h‖ := norm_pos_iff.mpr hne
      -- a positive δ small enough that δ‖h‖² eats only a quarter of the (negative) form
      obtain ⟨d, hd0, hd⟩ : ∃ d : ℝ, 0 < d ∧
          d * ‖h‖ ^ 2
            ≤ -(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv h)) h : ℝ) / 4 := by
        refine ⟨-(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv h)) h : ℝ)
          / (4 * ‖h‖ ^ 2), div_pos (by linarith) (by positivity), ?_⟩
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        ring_nf
        nlinarith [sq_nonneg ‖h‖]
      obtain ⟨ρ, hρ, hball⟩ := hexp d hd0
      obtain ⟨t, ht0, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖h‖ < ρ :=
        ⟨ρ / (2 * ‖h‖), by positivity, by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith⟩
      have hsm : ‖t • h‖ < ρ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]; exact htρ
      have hform : (inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv (t • h))) (t • h) : ℝ)
          = t ^ 2 * inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv h)) h := by
        rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_right]
        ring
      have hg := hsub (t • h)
      have hb := hball (t • h) hsm
      rw [hform, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at hb
      have habs := (abs_le.mp hb).2
      have k1 : t ^ 2 * (d * ‖h‖ ^ 2)
          ≤ t ^ 2 * (-(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv h)) h : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg t)
      have k2 : 0 < t ^ 2 * -(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv h)) h : ℝ) :=
        mul_pos (pow_pos ht0 2) (by linarith)
      linarith
  · -- the expansion itself
    intro δ hδ
    obtain ⟨ρ, hρ, hball⟩ := hexp δ hδ
    refine ⟨ρ, hρ, fun h hh => ?_⟩
    rw [hAhh h, ← hxy]
    exact hball h hh
