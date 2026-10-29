import InfHarmonic.NormalizedInfFamily
import InfHarmonic.LinearLift
import InfHarmonic.InfHarmonicMono
open Metric Set WithLp

/-- Step 0 of the family-flatness argument: every member of the normalized lifted
family is infinity-harmonic on the unit ball of space-time.  The lift is
infinity-harmonic on the slab `{z : ‖z_x‖ < 1}`, and the unit ball of space-time
sits inside that slab because the first coordinate is shorter than the vector. -/
theorem NormalizedFamilyInfHarmonic (d : ℕ)
    (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hU : NormalizedInfFamily d U) :
    IsInfHarmonicOn (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1) U := by
  obtain ⟨u, hinf, -, -, -, -, hUeq⟩ := hU
  -- the first coordinate is no longer than the vector
  have hfst : ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖(ofLp z).1‖ ≤ ‖z‖ := by
    intro z
    show ‖z.fst‖ ≤ ‖z‖
    have h := WithLp.prod_norm_sq_eq_of_L2 z
    nlinarith [norm_nonneg z.fst, norm_nonneg z, sq_nonneg ‖z.snd‖]
  -- the lift is infinity-harmonic on the slab
  have hlift := LinearLift (E := EuclideanSpace ℝ (Fin d)) (ball 0 1) u hinf
  -- the unit ball of space-time lies in the slab
  have hsub : ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1
      ⊆ (fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp z).1) ⁻¹' ball 0 1 := by
    intro z hz
    rw [mem_ball, dist_eq_norm, sub_zero] at hz
    rw [Set.mem_preimage, mem_ball, dist_eq_norm, sub_zero]
    exact lt_of_le_of_lt (hfst z) hz
  -- restrict, then rewrite the lift as `U`
  have hres := InfHarmonicMono
    ((fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp z).1) ⁻¹' ball 0 1)
    (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1) isOpen_ball hsub
    (fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => u (ofLp z).1 + (ofLp z).2) hlift
  have heq : (fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => u (ofLp z).1 + (ofLp z).2)
      = U := by
    funext z; rw [hUeq z]
  rw [heq] at hres
  exact hres
