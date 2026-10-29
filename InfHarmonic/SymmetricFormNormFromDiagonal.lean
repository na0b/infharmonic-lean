import InfHarmonic.Preamble
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- For a symmetric continuous bilinear form, a bound on the diagonal gives the same
bound on the operator norm: if `|S a a| ≤ C ‖a‖²` for every `a`, then `‖S‖ ≤ C`. -/
theorem SymmetricFormNormFromDiagonal (S : E →L[ℝ] E →L[ℝ] ℝ) (Cc : ℝ) (hCc : 0 ≤ Cc)
    (hSsym : ∀ a b : E, S a b = S b a) (hSdiag : ∀ a : E, |S a a| ≤ Cc * ‖a‖ ^ 2) :
    ‖S‖ ≤ Cc := by
  refine S.opNorm_le_bound₂ hCc (fun a b => ?_)
  -- the parallelogram law, from the two expansions of `‖u ± v‖²`
  have hpar : ∀ u v : E, ‖u + v‖ ^ 2 + ‖u - v‖ ^ 2 = 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    intro u v
    have e1 := norm_add_sq_real u v
    have e2 := norm_sub_sq_real u v
    linarith
  -- polarization: the symmetric bound in the form `C (‖u‖² + ‖v‖²)/2`
  have hhalf : ∀ u v : E, |S u v| ≤ Cc * (‖u‖ ^ 2 + ‖v‖ ^ 2) / 2 := by
    intro u v
    have hpol : S u v = (S (u + v) (u + v) - S (u - v) (u - v)) / 4 := by
      simp only [map_add, map_sub, add_apply, sub_apply]
      rw [hSsym v u]
      ring
    have h1 := abs_le.mp (hSdiag (u + v))
    have h2 := abs_le.mp (hSdiag (u - v))
    -- the parallelogram law must be multiplied through by `Cc` by hand: `linarith` cannot
    -- scale a hypothesis by the variable `Cc`
    have h4 : Cc * ‖u + v‖ ^ 2 + Cc * ‖u - v‖ ^ 2 = Cc * (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
      rw [← mul_add, hpar u v]
    rw [hpol, abs_le]
    constructor <;> linarith
  -- the degenerate arguments
  rcases eq_or_ne a 0 with ha0 | ha0
  · simp [ha0]
  rcases eq_or_ne b 0 with hb0 | hb0
  · simp [hb0]
  -- the scaling `(a, b) ↦ (t a, t⁻¹ b)` with `t² = ‖b‖/‖a‖` turns the arithmetic mean
  -- `(‖u‖² + ‖v‖²)/2` into the geometric mean `‖a‖ ‖b‖`
  have hap : 0 < ‖a‖ := norm_pos_iff.mpr ha0
  have hbp : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  obtain ⟨t, ht0, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ^ 2 = ‖b‖ / ‖a‖ :=
    ⟨Real.sqrt (‖b‖ / ‖a‖), Real.sqrt_pos.mpr (by positivity),
      Real.sq_sqrt (by positivity)⟩
  have hti : (t⁻¹) ^ 2 = ‖a‖ / ‖b‖ := by
    rw [inv_pow, ht2]
    field_simp
  have hsc : S (t • a) (t⁻¹ • b) = S a b := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    field_simp
  have h1 := hhalf (t • a) (t⁻¹ • b)
  rw [hsc, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ht0, abs_of_pos (inv_pos.mpr ht0)] at h1
  have hcalc : Cc * ((t * ‖a‖) ^ 2 + (t⁻¹ * ‖b‖) ^ 2) / 2 = Cc * ‖a‖ * ‖b‖ := by
    rw [mul_pow, mul_pow, ht2, hti]
    field_simp
    ring
  rw [Real.norm_eq_abs]
  linarith [h1, hcalc]
