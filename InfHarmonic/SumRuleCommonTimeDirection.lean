module

public import InfHarmonic.SumRuleJets
public import InfHarmonic.LimitSubClosedSuperjet
public import InfHarmonic.ClosedSuperjetScale

@[expose] public section
open Set Metric
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The sum rule, applied to a weighted family of copies of one subsolution and then
evaluated in the common-time direction: at a local maximum of `∑ θ i • v - Ψ` on the
product, the Hessian of `Ψ` is nonnegative on the direction whose `i`-th block is
`(θ i⁻¹ ∇_i Ψ, 1)`.  This is the step where the theorem of sums meets the viscosity
inequality; the regularization parameter `η` of the sum rule is sent to `0` here, which
is legitimate because neither the Hessian nor the direction depends on it. -/
theorem SumRuleCommonTimeDirection (N : ℕ) (Ω : Set (WithLp 2 (F × ℝ)))
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsLimitSubOn Ω v)
    (θ : Fin N → ℝ) (hθ : ∀ i, 0 < θ i)
    (Ψ : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) → ℝ)
    (Z : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)))
    (hZ : ∀ i, ofLp Z i ∈ Ω) (hΨ : ContDiffAt ℝ 2 Ψ Z)
    (hmax : IsLocalMax (fun Y : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) =>
      (∑ i, θ i * v (ofLp Y i)) - Ψ Y) Z) :
    0 ≤ (fderiv ℝ (fderiv ℝ Ψ) Z)
      (toLp 2 (fun i => toLp 2 ((θ i)⁻¹ • (ofLp (ofLp (∇ Ψ Z) i)).1, (1:ℝ))))
      (toLp 2 (fun i => toLp 2 ((θ i)⁻¹ • (ofLp (ofLp (∇ Ψ Z) i)).1, (1:ℝ)))) := by
  classical
  borelize (WithLp 2 (F × ℝ))
  have hΩ : IsOpen Ω := hv.1
  have hvc : ContinuousOn v Ω := hv.2.1
  obtain ⟨ζ, hζd⟩ : ∃ ζ : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)),
      ζ = toLp 2 (fun i => toLp 2 ((θ i)⁻¹ • (ofLp (ofLp (∇ Ψ Z) i)).1, (1:ℝ))) := ⟨_, rfl⟩
  have hζi : ∀ i : Fin N, ofLp ζ i
      = toLp 2 ((θ i)⁻¹ • (ofLp (ofLp (∇ Ψ Z) i)).1, (1:ℝ)) := by
    intro i; rw [hζd]
  rw [← hζd]
  -- for every η > 0 the sum rule gives the matrix inequality at ζ
  have hall : ∀ η : ℝ, 0 < η →
      0 ≤ (fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ
        + η * ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖ ^ 2 := by
    intro η hη
    obtain ⟨X, hXsym, hXjet, hXmat⟩ :=
      SumRuleJets N (fun _ => Ω) (fun _ => hΩ) (fun i z => θ i * v z)
        (fun i => hvc.const_smul (θ i)) Ψ Z hZ hΨ hmax η hη
    have hXnn : ∀ i : Fin N, 0 ≤ X i (ofLp ζ i) (ofLp ζ i) := by
      intro i
      have h1 := hXjet i
      have h2 := (ClosedSuperjetScale (θ i) (hθ i) v (ofLp Z i)
        (ofLp (∇ Ψ Z) i) (X i)).mp h1
      have h3 := LimitSubClosedSuperjet Ω v hv (ofLp Z i) (hZ i)
        ((θ i)⁻¹ • ofLp (∇ Ψ Z) i) ((θ i)⁻¹ • X i) h2
      have h4 : (ofLp ((θ i)⁻¹ • ofLp (∇ Ψ Z) i)).1
          = (θ i)⁻¹ • (ofLp (ofLp (∇ Ψ Z) i)).1 := rfl
      rw [h4, ← hζi i] at h3
      have h5 : ((θ i)⁻¹ • X i) (ofLp ζ i) (ofLp ζ i)
          = (θ i)⁻¹ * X i (ofLp ζ i) (ofLp ζ i) := by
        simp only [smul_apply, smul_eq_mul]
      rw [h5] at h3
      have h6 : 0 < (θ i)⁻¹ := inv_pos.mpr (hθ i)
      nlinarith [h3, h6]
    have hsum : 0 ≤ ∑ i, X i (ofLp ζ i) (ofLp ζ i) :=
      Finset.sum_nonneg (fun i _ => hXnn i)
    linarith [hXmat ζ, hsum]
  -- η ↓ 0: neither the Hessian nor ζ depends on η
  by_contra hcon
  rw [not_le] at hcon
  have hden : (0:ℝ) < ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖ ^ 2 + 1 := by positivity
  have hη0 : 0 < -((fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ)
      / (2 * (‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖ ^ 2 + 1)) := by
    apply div_pos (by linarith) (by linarith)
  have hstep := hall _ hη0
  have hkey : -((fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ)
      / (2 * (‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖ ^ 2 + 1))
      * (‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖ ^ 2 + 1)
      = -((fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ) / 2 := by
    field_simp
  nlinarith [hstep, hkey, hη0, sq_nonneg ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ‖]
