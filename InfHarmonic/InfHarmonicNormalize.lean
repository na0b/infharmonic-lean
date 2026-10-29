import InfHarmonic.IsInfHarmonicOn
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Positive scaling and additive constants preserve infinity-harmonicity:
`(u - c)/M` is infinity-harmonic on `Ω` for `M > 0`. -/
theorem InfHarmonicNormalize (Ω : Set E) (u : E → ℝ) (hu : IsInfHarmonicOn Ω u)
    (c M : ℝ) (hM : 0 < M) :
    IsInfHarmonicOn Ω (fun y : E => (u y - c) / M) := by
  obtain ⟨⟨hΩ, hcu, hsub⟩, ⟨-, -, hsup⟩⟩ := hu
  have hM0 : M ≠ 0 := ne_of_gt hM
  have hM3 : (0 : ℝ) < M ^ 3 := pow_pos hM 3
  -- Step 0: the normalization is continuous on `Ω`.
  have hcont : ContinuousOn (fun y : E => (u y - c) / M) Ω :=
    (hcu.sub continuousOn_const).div_const M
  -- Step 1: the test transfer `ψ ↦ φ = M ψ + c` stays a `C²` test.
  have hCD : ∀ (ψ : E → ℝ) (z : E), ContDiffAt ℝ 2 ψ z →
      ContDiffAt ℝ 2 (fun y => M * ψ y + c) z := fun ψ z hψ =>
    (contDiffAt_const.mul hψ).add contDiffAt_const
  -- Step 2: `∇φ = M ∇ψ` and `D²φ = M D²ψ`, hence `Δ_∞ φ = M³ Δ_∞ ψ`.
  have hscale : ∀ (ψ : E → ℝ) (z : E), ContDiffAt ℝ 2 ψ z →
      InfLap (fun y => M * ψ y + c) z = M ^ 3 * InfLap ψ z := by
    intro ψ z hψ
    have hd : DifferentiableAt ℝ ψ z := hψ.differentiableAt (by norm_num)
    have hgrad : gradient (fun y => M * ψ y + c) z = M • gradient ψ z := by
      have h : HasGradientAt (fun y => M * ψ y + c) (M • gradient ψ z) z := by
        rw [hasGradientAt_iff_hasFDerivAt]
        simpa using (hd.hasFDerivAt.const_mul M).add_const c
      exact h.gradient
    have hsecond : iteratedFDeriv ℝ 2 (fun y => M * ψ y + c) z
        = M • iteratedFDeriv ℝ 2 ψ z := by
      have e : (fun y : E => M * ψ y + c) = (fun y : E => M • ψ y) + (fun _ : E => c) := by
        funext y; simp
      have h1 : ContDiffAt ℝ 2 (fun y : E => M • ψ y) z := hψ.const_smul M
      rw [e, iteratedFDeriv_add_apply h1 contDiffAt_const,
        iteratedFDeriv_const_smul_apply' hψ, iteratedFDeriv_const_of_ne (by norm_num) c]
      simp
    have happ : iteratedFDeriv ℝ 2 ψ z (fun _ => M • gradient ψ z)
        = M ^ 2 * iteratedFDeriv ℝ 2 ψ z (fun _ => gradient ψ z) := by
      simpa using (iteratedFDeriv ℝ 2 ψ z).map_smul_univ
        (fun _ : Fin 2 => M) (fun _ : Fin 2 => gradient ψ z)
    simp only [InfLap, hgrad, hsecond, smul_apply, happ, smul_eq_mul]
    ring
  refine ⟨⟨hΩ, hcont, ?_⟩, ⟨hΩ, hcont, ?_⟩⟩
  · -- Upper tests: `(u - c)/M - ψ` peaks at `z` iff `u - (Mψ + c)` does.
    intro z hz ψ hψ hmax
    have hmax' : IsLocalMaxOn (fun x => u x - (M * ψ x + c)) Ω z := by
      refine Filter.Eventually.mono hmax fun x hx => ?_
      have h1 : M * ((u x - c) / M - ψ x) ≤ M * ((u z - c) / M - ψ z) :=
        mul_le_mul_of_nonneg_left hx hM.le
      have e : ∀ w : E, M * ((u w - c) / M - ψ w) = u w - (M * ψ w + c) := by
        intro w; field_simp; ring
      rw [e x, e z] at h1
      exact h1
    have h := hsub z hz (fun y => M * ψ y + c) (hCD ψ z hψ) hmax'
    rw [hscale ψ z hψ] at h
    refine le_of_mul_le_mul_left ?_ hM3
    simpa using h
  · -- Lower tests: the mirror computation with minima.
    intro z hz ψ hψ hmin
    have hmin' : IsLocalMinOn (fun x => u x - (M * ψ x + c)) Ω z := by
      refine Filter.Eventually.mono hmin fun x hx => ?_
      have h1 : M * ((u z - c) / M - ψ z) ≤ M * ((u x - c) / M - ψ x) :=
        mul_le_mul_of_nonneg_left hx hM.le
      have e : ∀ w : E, M * ((u w - c) / M - ψ w) = u w - (M * ψ w + c) := by
        intro w; field_simp; ring
      rw [e x, e z] at h1
      exact h1
    have h := hsup z hz (fun y => M * ψ y + c) (hCD ψ z hψ) hmin'
    rw [hscale ψ z hψ] at h
    refine le_of_mul_le_mul_left ?_ hM3
    simpa using h
