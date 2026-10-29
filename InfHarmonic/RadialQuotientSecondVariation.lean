module

public import InfHarmonic.Preamble

@[expose] public section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The second variation of the quadratic penalty `|h|²/r²` along a straight
motion in which the numerator vector moves with velocity `k` and the denominator
moves affinely with velocity `s`.  The motion is differentiable near the base
point and its derivative is again differentiable there, with
`2|k|²/r² - 8 s ⟪h,k⟫/r³ + 6 s²|h|²/r⁴` at the base point. -/
theorem RadialQuotientSecondVariation (h k : E) (r s : ℝ) (hr : 0 < r) :
    ∃ G : ℝ → ℝ,
      (∀ᶠ τ : ℝ in nhds (0:ℝ),
        HasDerivAt (fun t : ℝ => ‖h + t • k‖ ^ 2 / (r + t * s) ^ 2) (G τ) τ) ∧
      HasDerivAt G
        (2 * ‖k‖ ^ 2 / r ^ 2 - 8 * s * (inner ℝ h k) / r ^ 3
          + 6 * s ^ 2 * ‖h‖ ^ 2 / r ^ 4) 0 := by
  set a : ℝ := inner ℝ h k with ha
  set b : ℝ := ‖k‖ ^ 2 with hb
  set p : ℝ := ‖h‖ ^ 2 with hp
  have hr0 : r ≠ 0 := hr.ne'
  -- the numerator is the explicit quadratic `p + 2 t a + t² b` in the parameter
  have hN : ∀ t : ℝ, ‖h + t • k‖ ^ 2 = p + 2 * t * a + t ^ 2 * b := by
    intro t
    rw [hp, ha, hb, norm_add_sq_real, real_inner_smul_right, norm_smul]
    simp [mul_pow, sq_abs]
    ring
  have hfun : (fun t : ℝ => ‖h + t • k‖ ^ 2 / (r + t * s) ^ 2)
      = fun t : ℝ => (p + 2 * t * a + t ^ 2 * b) / (r + t * s) ^ 2 := by
    funext t; rw [hN t]
  -- the affine denominator and the quadratic numerator, differentiated
  have hlin : ∀ t : ℝ, HasDerivAt (fun u : ℝ => r + u * s) s t := by
    intro t
    have h := ((hasDerivAt_id t).mul_const s).const_add r
    rw [one_mul] at h
    exact h
  have hnum : ∀ t : ℝ, HasDerivAt (fun u : ℝ => p + 2 * u * a + u ^ 2 * b)
      (2 * a + 2 * t * b) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => p + 2 * u * a) (2 * a) t := by
      have h := (((hasDerivAt_id t).const_mul (2:ℝ)).mul_const a).const_add p
      exact h.congr_deriv (by ring)
    have h2 : HasDerivAt (fun u : ℝ => u ^ 2 * b) (2 * t * b) t := by
      have h : HasDerivAt (fun u : ℝ => u ^ 2 * b) ((2:ℝ) * t ^ (2-1) * b) t :=
        (hasDerivAt_pow 2 t).mul_const b
      exact h.congr_deriv (by norm_num)
    exact (h1.add h2).congr_deriv (by ring)
  rw [hfun]
  refine ⟨fun t => (2 * a + 2 * t * b) / (r + t * s) ^ 2
      - (p + 2 * t * a + t ^ 2 * b) * (2 * s) / (r + t * s) ^ 3, ?_, ?_⟩
  · -- the first derivative, at every parameter where the denominator survives
    have hcont : ContinuousAt (fun t : ℝ => r + t * s) 0 := by fun_prop
    have hne : ∀ᶠ t : ℝ in nhds (0:ℝ), r + t * s ≠ 0 := by
      have h0 : (fun t : ℝ => r + t * s) 0 ≠ 0 := by
        simp only []
        intro hc; rw [zero_mul, add_zero] at hc; exact hr0 hc
      exact hcont.eventually_ne h0
    filter_upwards [hne] with t ht
    have hden : HasDerivAt (fun u : ℝ => (r + u * s) ^ 2)
        ((2:ℝ) * (r + t * s) ^ (2-1) * s) t := (hlin t).pow 2
    have hd0 : (r + t * s) ^ 2 ≠ 0 := pow_ne_zero 2 ht
    have hq := (hnum t).div hden hd0
    exact hq.congr_deriv (by field_simp; ring)
  · -- the second derivative at the base point, by the quotient rule twice
    have h1 : HasDerivAt (fun t : ℝ => (2 * a + 2 * t * b) / (r + t * s) ^ 2)
        (2 * b / r ^ 2 - 4 * a * s / r ^ 3) 0 := by
      have hn : HasDerivAt (fun u : ℝ => 2 * a + 2 * u * b) (2 * b) 0 := by
        have h := (((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).mul_const b).const_add (2 * a)
        exact h.congr_deriv (by ring)
      have hd : HasDerivAt (fun u : ℝ => (r + u * s) ^ 2)
          ((2:ℝ) * (r + 0 * s) ^ (2-1) * s) 0 := (hlin 0).pow 2
      have hd0 : (r + (0:ℝ) * s) ^ 2 ≠ 0 := by
        rw [zero_mul, add_zero]; exact pow_ne_zero 2 hr0
      have hq := hn.div hd hd0
      exact hq.congr_deriv (by rw [zero_mul, add_zero] at *; field_simp; ring)
    have h2 : HasDerivAt
        (fun t : ℝ => (p + 2 * t * a + t ^ 2 * b) * (2 * s) / (r + t * s) ^ 3)
        (4 * a * s / r ^ 3 - 6 * p * s ^ 2 / r ^ 4) 0 := by
      have hn : HasDerivAt (fun u : ℝ => (p + 2 * u * a + u ^ 2 * b) * (2 * s))
          ((2 * a + 2 * 0 * b) * (2 * s)) 0 := (hnum 0).mul_const (2 * s)
      have hd : HasDerivAt (fun u : ℝ => (r + u * s) ^ 3)
          ((3:ℝ) * (r + 0 * s) ^ (3-1) * s) 0 := (hlin 0).pow 3
      have hd0 : (r + (0:ℝ) * s) ^ 3 ≠ 0 := by
        rw [zero_mul, add_zero]; exact pow_ne_zero 3 hr0
      have hq := hn.div hd hd0
      exact hq.congr_deriv (by rw [zero_mul, add_zero] at *; field_simp; ring)
    exact (h1.sub h2).congr_deriv (by field_simp; ring)
