import InfHarmonic.Preamble

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The second variation of the localizing product `B(c) f(r)` along a straight motion in
which the center moves with velocity `u` and the radius moves affinely with velocity `s`.
The motion is differentiable near the base point, its derivative is again differentiable
there, and the second derivative is the Leibniz sum
`D²B(c)[u] f(r) + 2 DB(c)[u] f'(r) s + B(c) f''(r) s²`.  The third summand is the one that
carries the blow-up of `f''` in the three-point estimate; the first two are bounded. -/
theorem ProfileProductSecondVariation (B : E → ℝ) (f f' : ℝ → ℝ) (c u : E) (r s fc : ℝ)
    (hB : ContDiff ℝ 2 B)
    (hf : ∀ᶠ ρ : ℝ in nhds r, HasDerivAt f (f' ρ) ρ)
    (hf2 : HasDerivAt f' fc r) :
    ∃ G : ℝ → ℝ,
      (∀ᶠ τ : ℝ in nhds (0:ℝ),
        HasDerivAt (fun t : ℝ => B (c + t • u) * f (r + t * s)) (G τ) τ) ∧
      HasDerivAt G
        (fderiv ℝ (fderiv ℝ B) c u u * f r
          + 2 * (fderiv ℝ B c u) * (f' r * s)
          + B c * (fc * s ^ 2)) 0 := by
  -- the two straight motions
  have hline : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => c + t • u) u τ := by
    intro τ
    have h1 : HasDerivAt (fun t : ℝ => t • u) u τ := by
      have h := (hasDerivAt_id τ).smul_const u
      rw [one_smul] at h
      exact h
    exact h1.const_add c
  have hlinr : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => r + t * s) s τ := by
    intro τ
    have h := ((hasDerivAt_id τ).mul_const s).const_add r
    rw [one_mul] at h
    exact h
  -- the B-factor and its derivative along the motion
  have hβ1 : ∀ τ : ℝ, HasDerivAt (fun t : ℝ => B (c + t • u))
      (fderiv ℝ B (c + τ • u) u) τ := by
    intro τ
    have hd : HasFDerivAt B (fderiv ℝ B (c + τ • u)) (c + τ • u) :=
      (hB.differentiable (by norm_num) (c + τ • u)).hasFDerivAt
    exact hd.comp_hasDerivAt τ (hline τ)
  -- the second derivative of the B-factor at the base point
  have hβ2 : HasDerivAt (fun τ : ℝ => fderiv ℝ B (c + τ • u) u)
      (fderiv ℝ (fderiv ℝ B) c u u) 0 := by
    have hd2 : DifferentiableAt ℝ (fderiv ℝ B) c :=
      ((hB.contDiffAt (x := c)).fderiv_right (m := 1) le_rfl).differentiableAt (by norm_num)
    have hd2' : HasFDerivAt (fderiv ℝ B) (fderiv ℝ (fderiv ℝ B) c) (c + (0:ℝ) • u) := by
      rw [zero_smul, add_zero]; exact hd2.hasFDerivAt
    exact (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt 0
      (hd2'.comp_hasDerivAt 0 (hline 0))
  -- the f-factor along the motion
  have hc2 : Continuous (fun τ : ℝ => r + τ * s) := by fun_prop
  have htend : Filter.Tendsto (fun τ : ℝ => r + τ * s) (nhds (0:ℝ)) (nhds r) := by
    have h := hc2.tendsto 0
    rw [zero_mul, add_zero] at h
    exact h
  have hγ1 : ∀ᶠ τ : ℝ in nhds (0:ℝ),
      HasDerivAt (fun t : ℝ => f (r + t * s)) (f' (r + τ * s) * s) τ := by
    filter_upwards [htend.eventually hf] with τ hτ
    exact hτ.comp τ (hlinr τ)
  have hγ2 : HasDerivAt (fun τ : ℝ => f' (r + τ * s) * s) (fc * s * s) 0 := by
    have hf2' : HasDerivAt f' fc (r + (0:ℝ) * s) := by
      rw [zero_mul, add_zero]; exact hf2
    exact (HasDerivAt.comp 0 hf2' (hlinr 0)).mul_const s
  have hγ1_0 : HasDerivAt (fun t : ℝ => f (r + t * s)) (f' r * s) 0 := by
    have h := hγ1.self_of_nhds
    rw [zero_mul, add_zero] at h
    exact h
  have hβ1_0 : HasDerivAt (fun t : ℝ => B (c + t • u)) (fderiv ℝ B c u) 0 := by
    have h := hβ1 0
    rw [zero_smul, add_zero] at h
    exact h
  refine ⟨fun τ => fderiv ℝ B (c + τ • u) u * f (r + τ * s)
      + B (c + τ • u) * (f' (r + τ * s) * s), ?_, ?_⟩
  · filter_upwards [hγ1] with τ hτ
    exact (hβ1 τ).mul hτ
  · refine ((hβ2.mul hγ1_0).add (hβ1_0.mul hγ2)).congr_deriv ?_
    simp only [zero_smul, add_zero, zero_mul]
    ring
