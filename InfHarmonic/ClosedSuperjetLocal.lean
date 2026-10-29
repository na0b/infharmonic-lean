module

public import InfHarmonic.ClosedSuperjet

@[expose] public section
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Part I(A) of the theorem of sums: the closed superjet at `0` sees only the
germ of the function near `0`, so two functions agreeing on a ball about `0` have
the same closed superjet there. -/
theorem ClosedSuperjetLocal (f₁ f₂ : E → ℝ) (b : ℝ) (hb : 0 < b)
    (hagree : ∀ w : E, ‖w‖ < b → f₁ w = f₂ w) :
    ClosedSuperjet f₁ 0 = ClosedSuperjet f₂ 0 := by
  -- Body-only acknowledgement (trap 2): the instance bundle is part of this node's protected
  -- signature; the route below uses finite-dimensionality only through `ClosedSuperjet` itself.
  have _ : FiniteDimensional ℝ E := inferInstance
  -- One inclusion suffices: the hypothesis is symmetric in `f₁` and `f₂`, so the auxiliary
  -- claim below is applied twice, the second time with the two functions exchanged.
  have hb4 : (0:ℝ) < b / 4 := by positivity
  have key : ∀ g₁ g₂ : E → ℝ, (∀ w : E, ‖w‖ < b → g₁ w = g₂ w) →
      ClosedSuperjet g₁ 0 ⊆ ClosedSuperjet g₂ 0 := by
    intro g₁ g₂ hag
    rintro ⟨p, X⟩ ⟨zs, ps, Xs, hjet, hz, hg, hp, hX⟩
    -- an index `k₀` beyond which the base points satisfy ‖z k‖ < b / 4
    obtain ⟨k₀, hk₀⟩ := (Metric.tendsto_atTop.mp hz) (b / 4) hb4
    have hzsmall : ∀ m : ℕ, ‖zs (m + k₀)‖ < b / 4 := by
      intro m
      have h := hk₀ (m + k₀) (by omega)
      rwa [dist_zero_right (zs (m + k₀))] at h
    -- re-indexing by `m ↦ m + k₀` changes none of the limits
    have hshift : Filter.Tendsto (fun m : ℕ => m + k₀) Filter.atTop Filter.atTop :=
      Filter.tendsto_add_atTop_nat k₀
    refine ⟨fun m => zs (m + k₀), fun m => ps (m + k₀), fun m => Xs (m + k₀), ?_, ?_, ?_, ?_, ?_⟩
    · -- each re-indexed jet is a superjet of `g₂` as well
      intro m
      obtain ⟨hsym, hineq⟩ := hjet (m + k₀)
      refine ⟨hsym, ?_⟩
      intro ε hε
      obtain ⟨δ, hδ, hball⟩ := hineq ε hε
      -- shrinking δ to min δ (b/4) only weakens the condition, and forces both
      -- ‖z k‖ < b and ‖z k + h‖ ≤ ‖z k‖ + ‖h‖ < b/2 < b
      refine ⟨min δ (b / 4), lt_min hδ hb4, fun h hh => ?_⟩
      have hhδ : ‖h‖ < δ := lt_of_lt_of_le hh (min_le_left _ _)
      have hhb : ‖h‖ < b / 4 := lt_of_lt_of_le hh (min_le_right _ _)
      have hzm := hzsmall m
      have h1 : ‖zs (m + k₀) + h‖ < b := by
        have htri := norm_add_le (zs (m + k₀)) h
        linarith
      have h2 : ‖zs (m + k₀)‖ < b := by linarith
      rw [← hag _ h1, ← hag _ h2]
      exact hball h hhδ
    · exact hz.comp hshift
    · -- the function values still converge to the right limit
      have h0 : g₂ (0 : E) = g₁ (0 : E) := by
        refine (hag 0 ?_).symm
        rw [norm_zero]
        exact hb
      rw [h0]
      have heq : (fun m : ℕ => g₂ (zs (m + k₀))) = fun m : ℕ => g₁ (zs (m + k₀)) := by
        funext m
        refine (hag _ ?_).symm
        have := hzsmall m
        linarith
      rw [heq]
      exact hg.comp hshift
    · exact hp.comp hshift
    · exact hX.comp hshift
  exact Set.Subset.antisymm (key f₁ f₂ hagree)
    (key f₂ f₁ (fun w hw => (hagree w hw).symm))
