import InfHarmonic.Preamble
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 5(a) of Alexandrov's theorem, the quantitative comparison: if `P` is
bounded below by `c` and `k` is within `δ₁‖h‖` of `P h`, then `h` is controlled by
`k` and the quadratic form `⟪(I - P) h, P h⟫` is within `O(δ₁)‖k‖²` of the form
`⟪(I - P) (P⁻¹ k), k⟫` written in the `k` variable. -/
theorem ProxQuadraticFormComparison (P Pinv : E →L[ℝ] E) (hinv : ∀ z : E, Pinv (P z) = z)
    (c : ℝ) (hc : 0 < c) (hlow : ∀ z : E, c * ‖z‖ ≤ ‖P z‖)
    (δ₁ : ℝ) (hδ₁ : 0 < δ₁) (hδ₁c : δ₁ ≤ c / 2)
    (h k : E) (hk : ‖k - P h‖ ≤ δ₁ * ‖h‖) :
    ‖h‖ ≤ 2 / c * ‖k‖ ∧
      |inner ℝ ((ContinuousLinearMap.id ℝ E - P) h) (P h)
          - inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) k|
        ≤ (4 * ‖ContinuousLinearMap.id ℝ E - P‖ * ‖Pinv‖ * ‖P‖ / c ^ 2
            + 2 * ‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ / c) * δ₁ * ‖k‖ ^ 2 := by
  have _ : FiniteDimensional ℝ E := inferInstance
  -- the lower bound forces `h` to be controlled by `k`
  have htri : ‖P h‖ ≤ ‖k‖ + ‖k - P h‖ := by
    calc ‖P h‖ = ‖k + (P h - k)‖ := by rw [show k + (P h - k) = P h by abel]
      _ ≤ ‖k‖ + ‖P h - k‖ := norm_add_le _ _
      _ = ‖k‖ + ‖k - P h‖ := by rw [norm_sub_rev]
  have hc2 : c * ‖h‖ ≤ 2 * ‖k‖ := by
    nlinarith [hlow h, hk, htri, mul_le_mul_of_nonneg_right hδ₁c (norm_nonneg h)]
  have hgoal1 : ‖h‖ ≤ 2 / c * ‖k‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]; linarith
  -- two scaled consequences, kept multiplied through by `c` to avoid division
  have h2 : c * ‖k - P h‖ ≤ 2 * δ₁ * ‖k‖ := by
    nlinarith [mul_le_mul_of_nonneg_left hk hc.le,
      mul_le_mul_of_nonneg_left hc2 hδ₁.le]
  have he : h - Pinv k = Pinv (P h - k) := by rw [map_sub, hinv h]
  have hb : ‖h - Pinv k‖ ≤ ‖Pinv‖ * ‖k - P h‖ := by
    calc ‖h - Pinv k‖ = ‖Pinv (P h - k)‖ := by rw [he]
      _ ≤ ‖Pinv‖ * ‖P h - k‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖Pinv‖ * ‖k - P h‖ := by rw [norm_sub_rev]
  have h3 : c * ‖h - Pinv k‖ ≤ ‖Pinv‖ * (2 * δ₁ * ‖k‖) := by
    nlinarith [mul_le_mul_of_nonneg_left hb hc.le,
      mul_le_mul_of_nonneg_left h2 (norm_nonneg Pinv)]
  -- the algebraic identity splitting the difference of the two forms
  have hid : (inner ℝ ((ContinuousLinearMap.id ℝ E - P) h) (P h) : ℝ)
        - inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) k
      = inner ℝ ((ContinuousLinearMap.id ℝ E - P) (h - Pinv k)) (P h)
        + inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) (P h - k) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  -- Cauchy-Schwarz on each term
  have hT1 : |(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (h - Pinv k)) (P h) : ℝ)|
      ≤ (‖ContinuousLinearMap.id ℝ E - P‖ * ‖h - Pinv k‖) * (‖P‖ * ‖h‖) := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    exact mul_le_mul (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
      (norm_nonneg _) (by positivity)
  have hT2 : |(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) (P h - k) : ℝ)|
      ≤ (‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ * ‖k‖) * ‖k - P h‖ := by
    refine le_trans (abs_real_inner_le_norm _ _) ?_
    have hA : ‖(ContinuousLinearMap.id ℝ E - P) (Pinv k)‖
        ≤ ‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ * ‖k‖ :=
      ContinuousLinearMap.le_opNorm ((ContinuousLinearMap.id ℝ E - P).comp Pinv) k
    have hPk : ‖P h - k‖ = ‖k - P h‖ := norm_sub_rev _ _
    rw [hPk]
    exact mul_le_mul_of_nonneg_right hA (norm_nonneg _)
  -- assemble: split the conjunction, then clear each denominator separately
  have hcsq : (0:ℝ) < c ^ 2 := by positivity
  refine ⟨hgoal1, ?_⟩
  have hprod : (c * ‖h - Pinv k‖) * (c * ‖h‖)
      ≤ (‖Pinv‖ * (2 * δ₁ * ‖k‖)) * (2 * ‖k‖) :=
    mul_le_mul h3 hc2 (by positivity) (by positivity)
  have e1 : c ^ 2 * |(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (h - Pinv k)) (P h) : ℝ)|
      ≤ 4 * ‖ContinuousLinearMap.id ℝ E - P‖ * ‖Pinv‖ * ‖P‖ * δ₁ * ‖k‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hT1 hcsq.le,
      mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (norm_nonneg (ContinuousLinearMap.id ℝ E - P)) (norm_nonneg P))]
  have e2 : c * |(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) (P h - k) : ℝ)|
      ≤ 2 * ‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ * δ₁ * ‖k‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hT2 hc.le,
      mul_le_mul_of_nonneg_left h2 (mul_nonneg (norm_nonneg
        ((ContinuousLinearMap.id ℝ E - P).comp Pinv)) (norm_nonneg k)),
      norm_nonneg k, norm_nonneg (k - P h), hc.le,
      norm_nonneg ((ContinuousLinearMap.id ℝ E - P).comp Pinv)]
  -- divide each back through its own denominator
  have f1 : |(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (h - Pinv k)) (P h) : ℝ)|
      ≤ 4 * ‖ContinuousLinearMap.id ℝ E - P‖ * ‖Pinv‖ * ‖P‖ / c ^ 2 * δ₁ * ‖k‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hcsq]
    linarith
  have f2 : |(inner ℝ ((ContinuousLinearMap.id ℝ E - P) (Pinv k)) (P h - k) : ℝ)|
      ≤ 2 * ‖(ContinuousLinearMap.id ℝ E - P).comp Pinv‖ / c * δ₁ * ‖k‖ ^ 2 := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hc]
    linarith
  rw [hid]
  refine le_trans (abs_add_le _ _) ?_
  nlinarith [f1, f2]
