import InfHarmonic.IsInfHarmonicOn
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Infinity-harmonicity restricts to an open subset: a local extremum of `u - φ`
relative to the smaller open set is automatically a local extremum relative to
the larger one, because the smaller set is a neighbourhood of the contact point.
This is what licenses passing from the unit ball to a smaller concentric ball. -/
theorem InfHarmonicMono (Ω Ω' : Set E) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω) (u : E → ℝ)
    (hu : IsInfHarmonicOn Ω u) :
    IsInfHarmonicOn Ω' u := by
  obtain ⟨⟨-, huc, hsubsol⟩, ⟨-, -, hsupsol⟩⟩ := hu
  -- the neighbourhood filter of a point of the smaller OPEN set does not see the
  -- restriction, so an eventual inequality there holds eventually on the larger set
  have key : ∀ (f : E → ℝ) (z : E), z ∈ Ω' →
      (∀ᶠ x in nhdsWithin z Ω', f x ≤ f z) → (∀ᶠ x in nhdsWithin z Ω, f x ≤ f z) := by
    intro f z hz h
    rw [nhdsWithin_eq_nhds.mpr (hΩ'.mem_nhds hz)] at h
    exact h.filter_mono nhdsWithin_le_nhds
  have key' : ∀ (f : E → ℝ) (z : E), z ∈ Ω' →
      (∀ᶠ x in nhdsWithin z Ω', f z ≤ f x) → (∀ᶠ x in nhdsWithin z Ω, f z ≤ f x) := by
    intro f z hz h
    rw [nhdsWithin_eq_nhds.mpr (hΩ'.mem_nhds hz)] at h
    exact h.filter_mono nhdsWithin_le_nhds
  refine ⟨⟨hΩ', huc.mono hsub, ?_⟩, ⟨hΩ', huc.mono hsub, ?_⟩⟩
  · intro z hz φ hφ hmax
    exact hsubsol z (hsub hz) φ hφ (key (fun x => u x - φ x) z hz hmax)
  · intro z hz φ hφ hmin
    exact hsupsol z (hsub hz) φ hφ (key' (fun x => u x - φ x) z hz hmin)
