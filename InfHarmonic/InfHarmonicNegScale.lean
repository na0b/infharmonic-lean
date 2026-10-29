module

public import InfHarmonic.IsInfHarmonicOn

@[expose] public section
open Set
open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Negative scaling preserves infinity-harmonicity, exchanging the roles of the
two viscosity inequalities: for `t < 0` the function `t * u` is infinity-harmonic
on `Ω` whenever `u` is.  This is what licenses replacing a family by its
negatives, and what makes `-2 u` a subsolution. -/
theorem InfHarmonicNegScale (Ω : Set E) (u : E → ℝ) (hu : IsInfHarmonicOn Ω u)
    (t : ℝ) (ht : t < 0) :
    IsInfHarmonicOn Ω (fun y : E => t * u y) := by
  obtain ⟨⟨hΩ, hcu, hsub⟩, ⟨-, -, hsup⟩⟩ := hu
  have htne : t ≠ 0 := ne_of_lt ht
  have hcont : ContinuousOn (fun y : E => t * u y) Ω := continuousOn_const.mul hcu
  -- the scaling identity `Δ_∞ (s φ) = s³ Δ_∞ φ`
  have hscale : ∀ (s : ℝ) (ψ : E → ℝ) (z : E), ContDiffAt ℝ 2 ψ z →
      InfLap (fun y => s * ψ y) z = s ^ 3 * InfLap ψ z := by
    intro s ψ z hψ
    have hd : DifferentiableAt ℝ ψ z := hψ.differentiableAt (by norm_num)
    have hgrad : ∇ (fun y => s * ψ y) z = s • ∇ ψ z := by
      have h : HasGradientAt (fun y => s * ψ y) (s • ∇ ψ z) z := by
        rw [hasGradientAt_iff_hasFDerivAt]
        simpa using hd.hasFDerivAt.const_mul s
      exact h.gradient
    have hsecond : iteratedFDeriv ℝ 2 (fun y => s * ψ y) z
        = s • iteratedFDeriv ℝ 2 ψ z := by
      have e : (fun y : E => s * ψ y) = fun y : E => s • ψ y := by
        funext y; simp
      rw [e, iteratedFDeriv_const_smul_apply' hψ]
    have happ : iteratedFDeriv ℝ 2 ψ z (fun _ => s • ∇ ψ z)
        = s ^ 2 * iteratedFDeriv ℝ 2 ψ z (fun _ => ∇ ψ z) := by
      simpa using (iteratedFDeriv ℝ 2 ψ z).map_smul_univ
        (fun _ : Fin 2 => s) (fun _ : Fin 2 => ∇ ψ z)
    simp only [InfLap, hgrad, hsecond, smul_apply, happ, smul_eq_mul]
    ring
  have hCD : ∀ (ψ : E → ℝ) (z : E), ContDiffAt ℝ 2 ψ z →
      ContDiffAt ℝ 2 (fun y => t⁻¹ * ψ y) z := fun ψ z hψ => contDiffAt_const.mul hψ
  have htinv : t⁻¹ < 0 := inv_lt_zero.mpr ht
  have hsq : 0 < t⁻¹ * t⁻¹ := mul_pos_of_neg_of_neg htinv htinv
  have htinv3 : t⁻¹ ^ 3 < 0 := by
    have h := mul_neg_of_neg_of_pos htinv hsq
    calc t⁻¹ ^ 3 = t⁻¹ * (t⁻¹ * t⁻¹) := by ring
      _ < 0 := h
  refine ⟨⟨hΩ, hcont, ?_⟩, ⟨hΩ, hcont, ?_⟩⟩
  · -- an upper test for `t u` becomes a lower test for `u` after division by `t < 0`
    intro z hz ψ hψ hmax
    have hmin' : IsLocalMinOn (fun x => u x - t⁻¹ * ψ x) Ω z := by
      refine Filter.Eventually.mono hmax fun x hx => ?_
      have h1 : t⁻¹ * (t * u z - ψ z) ≤ t⁻¹ * (t * u x - ψ x) :=
        mul_le_mul_of_nonpos_left hx htinv.le
      have e : ∀ w : E, t⁻¹ * (t * u w - ψ w) = u w - t⁻¹ * ψ w := by
        intro w; field_simp
      rw [e x, e z] at h1
      exact h1
    have h := hsup z hz (fun y => t⁻¹ * ψ y) (hCD ψ z hψ) hmin'
    rw [hscale t⁻¹ ψ z hψ] at h
    nlinarith [h, htinv3]
  · -- a lower test for `t u` becomes an upper test for `u`
    intro z hz ψ hψ hmin
    have hmax' : IsLocalMaxOn (fun x => u x - t⁻¹ * ψ x) Ω z := by
      refine Filter.Eventually.mono hmin fun x hx => ?_
      have h1 : t⁻¹ * (t * u x - ψ x) ≤ t⁻¹ * (t * u z - ψ z) :=
        mul_le_mul_of_nonpos_left hx htinv.le
      have e : ∀ w : E, t⁻¹ * (t * u w - ψ w) = u w - t⁻¹ * ψ w := by
        intro w; field_simp
      rw [e x, e z] at h1
      exact h1
    have h := hsub z hz (fun y => t⁻¹ * ψ y) (hCD ψ z hψ) hmax'
    rw [hscale t⁻¹ ψ z hψ] at h
    nlinarith [h, htinv3]
