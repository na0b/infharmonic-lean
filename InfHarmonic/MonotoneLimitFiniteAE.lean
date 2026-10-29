import InfHarmonic.Preamble
-- The project's standing variable block is not used by this statement, which is
-- about an abstract measure space, so the unused-section-variable linter is
-- switched off here.
set_option linter.unusedSectionVars false
open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A nondecreasing sequence of nonnegative integrable functions whose integrals
stay below a fixed bound is almost everywhere bounded above: the pointwise
increasing limit is finite almost everywhere. -/
theorem MonotoneLimitFiniteAE {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (g : ℕ → X → ℝ) (M : ℝ)
    (hmeas : ∀ i, Measurable (g i))
    (hnn : ∀ i, ∀ x, 0 ≤ g i x)
    (hmono : ∀ i, ∀ x, g i x ≤ g (i + 1) x)
    (hint : ∀ i, Integrable (g i) μ)
    (hbd : ∀ i, ∫ x, g i x ∂μ ≤ M) :
    ∀ᵐ x ∂μ, BddAbove (Set.range fun i => g i x) := by
  set f : ℕ → X → ℝ≥0∞ := fun i x => ENNReal.ofReal (g i x) with hf
  have hfmeas : ∀ i, Measurable (f i) := fun i => (hmeas i).ennreal_ofReal
  have hfmono : Monotone f := by
    intro a b hab x
    simp only [hf]
    refine ENNReal.ofReal_le_ofReal ?_
    induction b, hab using Nat.le_induction with
    | base => exact le_refl _
    | succ n hn ih => exact le_trans ih (hmono n x)
  have hfi : ∀ i, ∫⁻ x, f i x ∂μ ≤ ENNReal.ofReal M := by
    intro i
    rw [hf]
    rw [← ofReal_integral_eq_lintegral_ofReal (hint i)
      (Filter.Eventually.of_forall (hnn i))]
    exact ENNReal.ofReal_le_ofReal (hbd i)
  have hsup : ∫⁻ x, (⨆ i, f i x) ∂μ ≠ ∞ := by
    rw [lintegral_iSup hfmeas hfmono]
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (iSup_le hfi)
  have hmble : Measurable fun x => ⨆ i, f i x := Measurable.iSup hfmeas
  filter_upwards [ae_lt_top hmble hsup] with x hx
  refine ⟨(⨆ i, f i x).toReal, ?_⟩
  rintro y ⟨i, rfl⟩
  have h1 : f i x ≤ ⨆ i, f i x := le_iSup (fun i => f i x) i
  have h2 := ENNReal.toReal_le_toReal (by simp [hf]) hx.ne |>.mpr h1
  calc g i x = (ENNReal.ofReal (g i x)).toReal := by
        rw [ENNReal.toReal_ofReal (hnn i x)]
    _ ≤ (⨆ i, f i x).toReal := h2
