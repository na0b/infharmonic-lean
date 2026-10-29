import InfHarmonic.Preamble
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-- The concave radial profile `f r = r - r √r / 8 = r - r^{3/2}/8` of the
three-point estimate, together with its `C²` regularity away from the origin, its
first two derivatives, and the elementary bounds it is used through on `(0, 3/2]`:
it is squeezed between `ν r` and `r` with `ν = 1 - √(3/2)/8 > 0`, its derivative
lies in `(0, 1]`, and its second
derivative `-3/(32 √r)` blows up to `-∞` as `r ↓ 0`.  That last blow-up is the
source of the dominant negative second variation. -/
theorem ConcaveRadialProfile :
    0 < 1 - Real.sqrt (3 / 2) / 8 ∧
    (∀ r : ℝ, 0 < r → ContDiffAt ℝ 2 (fun s : ℝ => s - s * Real.sqrt s / 8) r) ∧
    (∀ r : ℝ, 0 < r →
      HasDerivAt (fun s : ℝ => s - s * Real.sqrt s / 8) (1 - 3 * Real.sqrt r / 16) r) ∧
    (∀ r : ℝ, 0 < r →
      HasDerivAt (fun s : ℝ => 1 - 3 * Real.sqrt s / 16) (-(3 / (32 * Real.sqrt r))) r) ∧
    (∀ r : ℝ, 0 < r → r ≤ 3 / 2 →
      (1 - Real.sqrt (3 / 2) / 8) * r ≤ r - r * Real.sqrt r / 8 ∧
      r - r * Real.sqrt r / 8 ≤ r ∧
      0 < 1 - 3 * Real.sqrt r / 16 ∧
      1 - 3 * Real.sqrt r / 16 ≤ 1) := by
  -- `√(3/2) < 2`, which is what makes `ν` positive and `f'` positive on `(0, 3/2]`
  have h32 : Real.sqrt (3 / 2) < 2 := by
    have h : Real.sqrt (3 / 2) < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  refine ⟨by linarith, ?_, ?_, ?_, ?_⟩
  · -- `f` is `C²` on `(0, ∞)`, the square root being smooth away from the origin
    intro r hr
    exact contDiffAt_id.sub ((contDiffAt_id.mul (Real.contDiffAt_sqrt hr.ne')).div_const 8)
  · -- `f'(r) = 1 - 3√r/16`
    intro r hr
    have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt r)) r := Real.hasDerivAt_sqrt hr.ne'
    have hid : HasDerivAt (fun s : ℝ => s) 1 r := hasDerivAt_id r
    have hm : HasDerivAt (fun s : ℝ => s * Real.sqrt s)
        (1 * Real.sqrt r + r * (1 / (2 * Real.sqrt r))) r := hid.mul hs
    have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hsr : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
    have h2 : 1 * Real.sqrt r + r * (1 / (2 * Real.sqrt r)) = 3 / 2 * Real.sqrt r := by
      field_simp
      nlinarith [hsr]
    rw [h2] at hm
    have h3 := hid.sub (hm.div_const 8)
    have h4 : (1 : ℝ) - 3 / 2 * Real.sqrt r / 8 = 1 - 3 * Real.sqrt r / 16 := by ring
    rw [h4] at h3
    exact h3
  · -- `f''(r) = -3/(32√r)`
    intro r hr
    have hs : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt r)) r := Real.hasDerivAt_sqrt hr.ne'
    have h3 := ((hs.const_mul (3 : ℝ)).div_const 16).const_sub (1 : ℝ)
    have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have h4 : -(3 * (1 / (2 * Real.sqrt r)) / 16) = -(3 / (32 * Real.sqrt r)) := by
      field_simp
      ring
    rw [h4] at h3
    exact h3
  · -- the elementary bounds on `(0, 3/2]`
    intro r hr hr32
    have hsq : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
    have hmono : Real.sqrt r ≤ Real.sqrt (3 / 2) := Real.sqrt_le_sqrt hr32
    refine ⟨?_, ?_, ?_, ?_⟩
    · nlinarith [hmono, hr]
    · nlinarith [hsq, hr]
    · nlinarith [hmono, h32]
    · nlinarith [hsq]
