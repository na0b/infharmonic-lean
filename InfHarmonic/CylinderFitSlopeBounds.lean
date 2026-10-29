import InfHarmonic.NormalizedInfFamily
import InfHarmonic.IsCylinderFit
open Metric Set WithLp

/-- Equation (3.3)'s slope bounds: every cylinder fit for a member of the
normalized family has slope of norm at most `L + √λ` and time component within
`√λ` of one. -/
theorem CylinderFitSlopeBounds (d : ℕ) (hd : 1 ≤ d) (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hU : NormalizedInfFamily d U) (L : ℝ)
    (z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (r lam : ℝ)
    (hr : 0 < r) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hLip : ∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖h‖ ≤ r →
      |U (z + h) - U z| ≤ L * ‖h‖)
    (P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (hfit : IsCylinderFit U z r lam P) :
    ‖P‖ ≤ L + Real.sqrt lam ∧
    |inner ℝ P (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) - 1| ≤ Real.sqrt lam := by
  -- `hd` is carried by the statement because the paper fixes `d ≥ 1`; the argument below
  -- is uniform in the dimension, so it is recorded here rather than used.
  have _unused_hd := hd
  obtain ⟨hP0, hfit2⟩ := hfit
  have hPpos : (0:ℝ) < ‖P‖ := norm_pos_iff.mpr hP0
  have hNnorm : ‖(‖P‖⁻¹ • P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ = 1 :=
    norm_smul_inv_norm hP0
  have hsqpos : (0:ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt hlam.le
  have hsqle1 : Real.sqrt lam ≤ 1 := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hlam1
  have hρpos : (0:ℝ) < Real.sqrt lam * r := mul_pos hsqpos hr
  have hρr : Real.sqrt lam * r ≤ r := by nlinarith
  -- the orthogonal-projection bound for a unit axis (the cylinder-layer block)
  have hproj : ∀ m h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      ‖m‖ = 1 → ‖h - (inner ℝ m h : ℝ) • m‖ ≤ ‖h‖ := by
    intro m h hm
    have hs : ‖h - (inner ℝ m h : ℝ) • m‖ ^ 2 ≤ ‖h‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hm, mul_one,
        real_inner_comm h m]
      nlinarith [sq_abs (inner ℝ h m : ℝ), sq_nonneg (inner ℝ h m : ℝ)]
    have h' := Real.sqrt_le_sqrt hs
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'
  -- Step 1: the cylinder contains the closed ball of radius `√λ r` about `z`.
  have hball : ∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖h‖ ≤ Real.sqrt lam * r →
      |U (z + h) - U z - (inner ℝ P h : ℝ)| ≤ lam * r := by
    intro h hh
    have hmem : z + h ∈ FitCylinder z r lam P := by
      refine ⟨?_, ?_⟩
      · rw [add_sub_cancel_left]
        calc |(inner ℝ (‖P‖⁻¹ • P) h : ℝ)|
            ≤ ‖(‖P‖⁻¹ • P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ * ‖h‖ :=
              abs_real_inner_le_norm _ _
          _ = ‖h‖ := by rw [hNnorm, one_mul]
          _ ≤ r := le_trans hh hρr
      · rw [add_sub_cancel_left]
        exact le_trans (hproj _ h hNnorm) hh
    have hv := hfit2 (z + h) hmem
    rwa [add_sub_cancel_left] at hv
  -- Step 2: the norm bound.
  have hnorm : ‖P‖ ≤ L + Real.sqrt lam := by
    have hwn : ‖((Real.sqrt lam * r) • (‖P‖⁻¹ • P) :
        WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ = Real.sqrt lam * r := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, hNnorm, mul_one]
    have hinner : (inner ℝ P ((Real.sqrt lam * r) • (‖P‖⁻¹ • P)) : ℝ)
        = (Real.sqrt lam * r) * ‖P‖ := by
      rw [real_inner_smul_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hb := hball _ (le_of_eq hwn)
    have hL := hLip _ (le_trans (le_of_eq hwn) hρr)
    rw [hinner] at hb
    rw [hwn] at hL
    rw [abs_le] at hb hL
    have hkey : (Real.sqrt lam * r) * ‖P‖
        ≤ (Real.sqrt lam * r) * (L + Real.sqrt lam) := by
      nlinarith [hb.1, hb.2, hL.1, hL.2, hsq]
    exact le_of_mul_le_mul_left hkey hρpos
  -- Step 3: the exact increment in the direction `e_b`.
  obtain ⟨u, -, -, -, -, -, hUrep⟩ := hU
  have hebnorm : ‖(toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) :
      WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ = 1 := by
    rw [WithLp.prod_norm_eq_of_L2]; simp
  have htime : ‖((Real.sqrt lam * r) • (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) :
      WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ = Real.sqrt lam * r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hρpos, hebnorm, mul_one]
  have hincr : U (z + (Real.sqrt lam * r) •
      (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)))) - U z = Real.sqrt lam * r := by
    rw [hUrep, hUrep]
    simp
  have hb2 := hball _ (le_of_eq htime)
  rw [hincr, real_inner_smul_right] at hb2
  have htb : |(inner ℝ P (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) : ℝ) - 1|
      ≤ Real.sqrt lam := by
    have he : Real.sqrt lam * r
          - Real.sqrt lam * r * (inner ℝ P (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) : ℝ)
        = (Real.sqrt lam * r)
          * (1 - (inner ℝ P (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) : ℝ)) := by ring
    rw [he, abs_mul, abs_of_pos hρpos] at hb2
    rw [abs_sub_comm]
    have h2 : (Real.sqrt lam * r)
          * |1 - (inner ℝ P (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) : ℝ)|
        ≤ (Real.sqrt lam * r) * Real.sqrt lam := by
      nlinarith [hb2, hsq]
    exact le_of_mul_le_mul_left h2 hρpos
  exact ⟨hnorm, htb⟩
