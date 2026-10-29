import InfHarmonic.Preamble
open Set Filter Topology WithLp MeasureTheory

/-- The Cauchy-Schwarz inequality for the integral of a product of square roots:
for nonnegative integrable `f` and `g` the product `sqrt f * sqrt g` is
integrable and its integral is at most `sqrt (∫ f) * sqrt (∫ g)`. The proof
runs through the pointwise bound `sqrt a * sqrt b ≤ (l * a + b / l) / 2`, valid
for every `l > 0`, and optimizes in `l`. -/
theorem IntegralSqrtProductCauchySchwarz {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f g : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) (hg0 : ∀ ω, 0 ≤ g ω)
    (hfi : Integrable f μ) (hgi : Integrable g μ) :
    Integrable (fun ω => Real.sqrt (f ω) * Real.sqrt (g ω)) μ ∧
      ∫ ω, Real.sqrt (f ω) * Real.sqrt (g ω) ∂μ
        ≤ Real.sqrt (∫ ω, f ω ∂μ) * Real.sqrt (∫ ω, g ω ∂μ) := by
  have hpt : ∀ (l : ℝ), 0 < l → ∀ ω,
      Real.sqrt (f ω) * Real.sqrt (g ω) ≤ (l * f ω + g ω / l) / 2 := by
    intro l hl ω
    have ha : (0:ℝ) ≤ Real.sqrt (f ω) := Real.sqrt_nonneg _
    have hb : (0:ℝ) ≤ Real.sqrt (g ω) := Real.sqrt_nonneg _
    have ha2 : Real.sqrt (f ω) ^ 2 = f ω := Real.sq_sqrt (hf0 ω)
    have hb2 : Real.sqrt (g ω) ^ 2 = g ω := Real.sq_sqrt (hg0 ω)
    have hkey : (0:ℝ) ≤ (l * Real.sqrt (f ω) - Real.sqrt (g ω)) ^ 2 := sq_nonneg _
    have h2 : 2 * l * (Real.sqrt (f ω) * Real.sqrt (g ω)) ≤ l ^ 2 * f ω + g ω := by
      have h2' : 2 * l * (Real.sqrt (f ω) * Real.sqrt (g ω))
          ≤ l ^ 2 * Real.sqrt (f ω) ^ 2 + Real.sqrt (g ω) ^ 2 := by
        nlinarith only [hkey]
      rwa [ha2, hb2] at h2'
    have h4 : g ω / l * l = g ω := div_mul_cancel₀ _ (ne_of_gt hl)
    nlinarith only [h2, h4, hl]
  have hprodint : Integrable (fun ω => Real.sqrt (f ω) * Real.sqrt (g ω)) μ := by
    refine Integrable.mono' (g := fun ω => (1 * f ω + g ω / 1) / 2)
      (((hfi.const_mul 1).add (hgi.div_const 1)).div_const 2)
      ((Real.continuous_sqrt.comp_aestronglyMeasurable hfi.aestronglyMeasurable).mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable hgi.aestronglyMeasurable))
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hpt 1 one_pos ω
  refine ⟨hprodint, ?_⟩
  obtain ⟨A, hAd⟩ : ∃ t : ℝ, t = ∫ ω, f ω ∂μ := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ t : ℝ, t = ∫ ω, g ω ∂μ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAd]; exact integral_nonneg hf0
  have hB0 : 0 ≤ B := by rw [hBd]; exact integral_nonneg hg0
  have hmain : ∀ l : ℝ, 0 < l →
      ∫ ω, Real.sqrt (f ω) * Real.sqrt (g ω) ∂μ ≤ (l * A + B / l) / 2 := by
    intro l hl
    have h1 : ∫ ω, Real.sqrt (f ω) * Real.sqrt (g ω) ∂μ
        ≤ ∫ ω, ((l * f ω + g ω / l) / 2) ∂μ :=
      integral_mono hprodint (((hfi.const_mul l).add (hgi.div_const l)).div_const 2)
        (fun ω => hpt l hl ω)
    rw [integral_div, integral_add (hfi.const_mul l) (hgi.div_const l), integral_const_mul,
      integral_div, ← hAd, ← hBd] at h1
    exact h1
  rcases eq_or_lt_of_le hA0 with hA | hA
  · rw [← hAd, ← hBd, ← hA, Real.sqrt_zero, zero_mul]
    refine le_of_forall_pos_le_add (fun δ hδ => ?_)
    obtain ⟨l, hl0, hl⟩ : ∃ l : ℝ, 0 < l ∧ B / l / 2 ≤ δ := by
      refine ⟨(B + 1) / δ, by positivity, ?_⟩
      have he : B / ((B + 1) / δ) / 2 = B * δ / ((B + 1) * 2) := by
        field_simp
      rw [he, div_le_iff₀ (by positivity : (0:ℝ) < (B + 1) * 2)]
      nlinarith only [hB0, hδ]
    have h3 := hmain l hl0
    rw [← hA] at h3
    simp only [mul_zero, zero_add] at h3
    linarith only [h3, hl]
  · rcases eq_or_lt_of_le hB0 with hB | hB
    · rw [← hAd, ← hBd, ← hB, Real.sqrt_zero, mul_zero]
      refine le_of_forall_pos_le_add (fun δ hδ => ?_)
      obtain ⟨l, hl0, hl⟩ : ∃ l : ℝ, 0 < l ∧ l * A / 2 ≤ δ := by
        refine ⟨δ / (A + 1), by positivity, ?_⟩
        have he : δ / (A + 1) * A / 2 = δ * A / ((A + 1) * 2) := by
          field_simp
        rw [he, div_le_iff₀ (by positivity : (0:ℝ) < (A + 1) * 2)]
        nlinarith only [hA, hδ]
      have h3 := hmain l hl0
      rw [← hB] at h3
      simp only [zero_div, add_zero] at h3
      linarith only [h3, hl]
    · have hsA : 0 < Real.sqrt A := Real.sqrt_pos.mpr hA
      have hsB : 0 < Real.sqrt B := Real.sqrt_pos.mpr hB
      have h3 := hmain (Real.sqrt B / Real.sqrt A) (by positivity)
      have e1 : Real.sqrt B / Real.sqrt A * A = Real.sqrt A * Real.sqrt B := by
        have hAA : Real.sqrt A * Real.sqrt A = A := Real.mul_self_sqrt hA0
        field_simp
        nlinarith only [hAA]
      have e2 : B / (Real.sqrt B / Real.sqrt A) = Real.sqrt A * Real.sqrt B := by
        have hBB : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hB0
        field_simp
        nlinarith only [hBB]
      rw [e1, e2] at h3
      rw [← hAd, ← hBd]
      linarith only [h3]
