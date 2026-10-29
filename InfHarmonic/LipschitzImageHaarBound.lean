import InfHarmonic.Preamble
open Set MeasureTheory Metric Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- A map that is `K`-Lipschitz on `A` increases the additive Haar measure of `A` by at
most the factor `K ^ dim E`. -/
theorem LipschitzImageHaarBound (μ : Measure E) [μ.IsAddHaarMeasure]
    (K : NNReal) (A : Set E) (f : E → E) (hf : LipschitzOnWith K f A) :
    μ (f '' A) ≤ (K : ENNReal) ^ (finrank ℝ E) * μ A := by
  -- the `dim E`-dimensional Hausdorff measure is itself an additive Haar measure, so by
  -- uniqueness of Haar measure `μ` is a scalar multiple of it
  obtain ⟨c, hsm⟩ : ∃ c : NNReal, μ = c • (μH[finrank ℝ E] : Measure E) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul μ _⟩
  have key : ∀ s : Set E, μ s = (c : ENNReal) * (μH[finrank ℝ E] : Measure E) s := by
    intro s; rw [hsm, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  -- the bound for the Hausdorff measure, at the dimension `dim E`
  have himg : (μH[finrank ℝ E] : Measure E) (f '' A)
      ≤ (K : ENNReal) ^ (finrank ℝ E) * (μH[finrank ℝ E] : Measure E) A := by
    have h := hf.hausdorffMeasure_image_le (d := ((finrank ℝ E : ℕ) : ℝ)) (by positivity)
    rwa [ENNReal.rpow_natCast] at h
  -- rescale by the same factor on both sides
  calc μ (f '' A) = (c : ENNReal) * (μH[finrank ℝ E] : Measure E) (f '' A) := key _
    _ ≤ (c : ENNReal) * ((K : ENNReal) ^ (finrank ℝ E) * (μH[finrank ℝ E] : Measure E) A) := by
        gcongr
    _ = (K : ENNReal) ^ (finrank ℝ E) * ((c : ENNReal) * (μH[finrank ℝ E] : Measure E) A) := by
        ring
    _ = (K : ENNReal) ^ (finrank ℝ E) * μ A := by rw [key A]
