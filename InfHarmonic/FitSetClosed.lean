module

public import InfHarmonic.IsFit

@[expose] public section
-- `FiniteDimensional ℝ F` is carried by the project's standing variable block but is not
-- needed for this statement, so the unused-section-variable linter is switched off here.
set_option linter.unusedSectionVars false
open Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The fits of a fixed radius form a closed set: for a continuous `v`, a
constant `C₀` and a radius `r > 0`, the set of triples `(z, p, a)` for which
`(p, a)` is a fit for `v` at `z` of radius `r` is closed. -/
theorem FitSetClosed (C₀ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ) (hv : Continuous v)
    (r : ℝ) (hr : 0 < r) :
    IsClosed {q : WithLp 2 (F × ℝ) × F × ℝ | IsFit C₀ v q.1 r q.2.1 q.2.2} := by
  classical
  set S : ℝ → F → Set (WithLp 2 (F × ℝ) × F × ℝ) := fun θ ζ =>
    {q | |v (q.1 + toLp 2 ((r * θ) • q.2.1 + r • ζ, r * θ)) - v q.1
        - inner ℝ q.2.1 ((r * θ) • q.2.1 + r • ζ)
        - (q.2.2 - ‖q.2.1‖ ^ 2 / 2) * (r * θ)| ≤ C₀ * r} with hS
  have hSclosed : ∀ (θ : ℝ) (ζ : F), IsClosed (S θ ζ) := by
    intro θ ζ
    have hcont : Continuous (fun q : WithLp 2 (F × ℝ) × F × ℝ =>
        |v (q.1 + toLp 2 ((r * θ) • q.2.1 + r • ζ, r * θ)) - v q.1
          - inner ℝ q.2.1 ((r * θ) • q.2.1 + r • ζ)
          - (q.2.2 - ‖q.2.1‖ ^ 2 / 2) * (r * θ)|) := by
      fun_prop
    rw [hS]
    exact isClosed_le hcont continuous_const
  have heq : {q : WithLp 2 (F × ℝ) × F × ℝ | IsFit C₀ v q.1 r q.2.1 q.2.2}
      = ⋂ (θ : ℝ) (_ : |θ| ≤ 1) (ζ : F) (_ : ‖ζ‖ ≤ 1), S θ ζ := by
    ext q
    constructor
    · intro hq
      refine Set.mem_iInter.2 (fun θ => Set.mem_iInter.2 (fun hθ =>
        Set.mem_iInter.2 (fun ζ => Set.mem_iInter.2 (fun hζ => ?_))))
      rw [hS]
      refine hq ((r * θ) • q.2.1 + r • ζ) (r * θ) ?_ ?_
      · rw [abs_mul, abs_of_pos hr]
        calc r * |θ| ≤ r * 1 := by
              exact mul_le_mul_of_nonneg_left hθ hr.le
          _ = r := by ring
      · have h1 : (r * θ) • q.2.1 + r • ζ - (r * θ) • q.2.1 = r • ζ := by
          abel
        rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
        calc r * ‖ζ‖ ≤ r * 1 := by
              exact mul_le_mul_of_nonneg_left hζ hr.le
          _ = r := by ring
    · intro hq h l hl hhl
      have hθ : |l / r| ≤ 1 := by
        rw [abs_div, abs_of_pos hr, div_le_one hr]
        exact hl
      have hζ : ‖r⁻¹ • (h - l • q.2.1)‖ ≤ 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < r⁻¹)]
        calc r⁻¹ * ‖h - l • q.2.1‖ ≤ r⁻¹ * r :=
              mul_le_mul_of_nonneg_left hhl (by positivity)
          _ = 1 := by field_simp
      have h2 := Set.mem_iInter.1 (Set.mem_iInter.1 (Set.mem_iInter.1
        (Set.mem_iInter.1 hq (l / r)) hθ) (r⁻¹ • (h - l • q.2.1))) hζ
      simp only [hS, Set.mem_ofPred_eq] at h2
      have hl' : r * (l / r) = l := by
        field_simp
      have hh' : (r * (l / r)) • q.2.1 + r • (r⁻¹ • (h - l • q.2.1)) = h := by
        rw [hl', smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
        abel
      rw [hh', hl'] at h2
      exact h2
  rw [heq]
  exact isClosed_iInter (fun θ => isClosed_iInter (fun _ => isClosed_iInter
    (fun ζ => isClosed_iInter (fun _ => hSclosed θ ζ))))
