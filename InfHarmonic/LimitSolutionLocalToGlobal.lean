module

public import InfHarmonic.IsLimitSolutionOn

@[expose] public section
open Set Filter Topology

/-- Being a limit solution is a LOCAL property: if an open set is covered by
subsets on each of which `v` is a limit solution, and `v` is continuous on the
whole set, then `v` is a limit solution there.  The mechanism is that a local
extremum relative to the big set restricts to one relative to any subset
containing the point, because the neighbourhood filter within a subset is
finer. -/
theorem LimitSolutionLocalToGlobal {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*} (Ω : Set (WithLp 2 (F × ℝ))) (O : ι → Set (WithLp 2 (F × ℝ)))
    (v : WithLp 2 (F × ℝ) → ℝ)
    (hΩ : IsOpen Ω)
    (hsub : ∀ k, O k ⊆ Ω)
    (hcover : ∀ z ∈ Ω, ∃ k, z ∈ O k)
    (hcont : ContinuousOn v Ω)
    (hloc : ∀ k, IsLimitSolutionOn (O k) v) :
    IsLimitSolutionOn Ω v := by
  constructor
  · refine ⟨hΩ, hcont, ?_⟩
    intro z hz φ hφ hmax
    obtain ⟨k, hk⟩ := hcover z hz
    exact (hloc k).1.2.2 z hk φ hφ (hmax.filter_mono (nhdsWithin_mono z (hsub k)))
  · refine ⟨hΩ, hcont, ?_⟩
    intro z hz φ hφ hmin
    obtain ⟨k, hk⟩ := hcover z hz
    exact (hloc k).2.2.2 z hk φ hφ (hmin.filter_mono (nhdsWithin_mono z (hsub k)))
