module

public import InfHarmonic.SupConvolution
public import InfHarmonic.SemiconvexOn

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Under a linear growth bound the sup-convolution is finite, dominates `φ`,
and is `(1/ε)`-semiconvex. -/
theorem SupConvolutionSemiconvex (ε C : ℝ) (hε : 0 < ε) (φ : E → ℝ)
    (hφ : ∀ w : E, φ w ≤ C + ‖w‖) :
    (∀ z : E, BddAbove (Set.range (fun w : E => φ w - ‖z - w‖ ^ 2 / (2 * ε)))) ∧
    (∀ z : E, φ z ≤ SupConvolution ε φ z) ∧
    SemiconvexOn (1 / ε) Set.univ (SupConvolution ε φ) := by
  -- Ledger item 6: the node statement and proof never use finite-dimensionality, and
  -- neither cited signature carries it (`SupConvolution` sheds it, `SemiconvexOn` too),
  -- so the automatically included section variable would be flagged unused.
  have _unused_fd : FiniteDimensional ℝ E := inferInstance
  have h2e : (0:ℝ) < 2 * ε := by linarith
  -- (1) boundedness above, with the explicit bound C + ‖z‖ + ε/2
  have hbdd : ∀ z : E, BddAbove (Set.range (fun w : E => φ w - ‖z - w‖ ^ 2 / (2 * ε))) := by
    intro z
    refine ⟨C + ‖z‖ + ε / 2, ?_⟩
    rintro v ⟨w, rfl⟩
    have htri : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := by
      have hrw : ‖w‖ = ‖z - (z - w)‖ := by rw [sub_sub_cancel]
      rw [hrw]; exact norm_sub_le z (z - w)
    have hD : ‖z - w‖ - ε / 2 ≤ ‖z - w‖ ^ 2 / (2 * ε) := by
      rw [le_div_iff₀ h2e]
      nlinarith [sq_nonneg (‖z - w‖ - ε)]
    have := hφ w

    linarith
  -- the pointwise upper bound of the supremum
  have hmem : ∀ (z w : E), φ w - ‖z - w‖ ^ 2 / (2 * ε) ≤ SupConvolution ε φ z := by
    intro z w
    have := le_csSup (hbdd z) (Set.mem_range_self (f := fun w : E => φ w - ‖z - w‖ ^ 2 / (2 * ε)) w)
    simpa [SupConvolution] using this
  -- (2) domination
  have hdom : ∀ z : E, φ z ≤ SupConvolution ε φ z := by
    intro z
    have := hmem z z
    simpa using this
  refine ⟨hbdd, hdom, ?_⟩
  -- (3) semiconvexity
  rw [SemiconvexOn]
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have key : SupConvolution ε φ (a • x + b • y) + ‖a • x + b • y‖ ^ 2 / (2 * ε)
      ≤ a * (SupConvolution ε φ x + ‖x‖ ^ 2 / (2 * ε))
        + b * (SupConvolution ε φ y + ‖y‖ ^ 2 / (2 * ε)) := by
    have hle : SupConvolution ε φ (a • x + b • y)
        ≤ a * (SupConvolution ε φ x + ‖x‖ ^ 2 / (2 * ε))
          + b * (SupConvolution ε φ y + ‖y‖ ^ 2 / (2 * ε))
          - ‖a • x + b • y‖ ^ 2 / (2 * ε) := by
      rw [SupConvolution]
      refine csSup_le (Set.range_nonempty _) ?_
      rintro v ⟨w, rfl⟩
      have hx := hmem x w
      have hy := hmem y w
      have hinner : (inner ℝ (a • x + b • y) w : ℝ)
          = a * inner ℝ x w + b * inner ℝ y w := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have hb' : b = 1 - a := by linarith
      subst hb'
      have hid : φ w - ‖a • x + (1 - a) • y - w‖ ^ 2 / (2 * ε)
            + ‖a • x + (1 - a) • y‖ ^ 2 / (2 * ε)
          = a * (φ w - ‖x - w‖ ^ 2 / (2 * ε) + ‖x‖ ^ 2 / (2 * ε))
            + (1 - a) * (φ w - ‖y - w‖ ^ 2 / (2 * ε) + ‖y‖ ^ 2 / (2 * ε)) := by
        rw [norm_sub_sq_real (a • x + (1 - a) • y) w, norm_sub_sq_real x w,
          norm_sub_sq_real y w, hinner]
        field_simp
        ring
      have h1 := mul_le_mul_of_nonneg_left hx ha
      have h2 := mul_le_mul_of_nonneg_left hy hb

      linarith [hid, h1, h2]
    linarith
  simp only [smul_eq_mul]
  have hexp : ∀ z : E, (1 / ε) * ‖z‖ ^ 2 / 2 = ‖z‖ ^ 2 / (2 * ε) := by
    intro z; field_simp
  simp only [hexp]
  linarith [key]
