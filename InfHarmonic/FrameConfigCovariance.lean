module

public import InfHarmonic.FrameChange
public import InfHarmonic.BaryRadius
public import InfHarmonic.IsBaryConfig

@[expose] public section
-- `FiniteDimensional ℝ F` is carried by the project's standing variable block but
-- is not needed for this statement, so the unused-section-variable linter is
-- switched off here.
set_option linter.unusedSectionVars false
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A sheared change of frame acts on barycentric configurations: at each fixed
new time the spatial map is an affine bijection which carries configurations
onto configurations, keeping the weights and scaling the radius by the frame
scale, and the barycentric defect of a single configuration transforms by the
reciprocal of that scale. -/
theorem FrameConfigCovariance (g : WithLp 2 (F × ℝ) → ℝ) (z₀ : WithLp 2 (F × ℝ))
    (R : ℝ) (hR : 0 < R) (p₀ : F) (a₀ s : ℝ) :
    (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (xb : F),
        IsBaryConfig n θ (fun i => (ofLp z₀).1 + R • (y i + s • p₀))
            ((ofLp z₀).1 + R • (xb + s • p₀)) ↔ IsBaryConfig n θ y xb) ∧
    (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (xb : F),
        BaryRadius n θ (fun i => (ofLp z₀).1 + R • (y i + s • p₀))
            ((ofLp z₀).1 + R • (xb + s • p₀)) = R * BaryRadius n θ y xb) ∧
    (∀ Y : F, ∃ y : F, (ofLp z₀).1 + R • (y + s • p₀) = Y) ∧
    (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (xb : F), IsBaryConfig n θ y xb →
        (∑ i, θ i * FrameChange g z₀ R p₀ a₀ (toLp 2 (y i, s)))
            - FrameChange g z₀ R p₀ a₀ (toLp 2 (xb, s))
          = (1 / R) *
            ((∑ i, θ i * g (toLp 2 ((ofLp z₀).1 + R • (y i + s • p₀),
                (ofLp z₀).2 + R * s)))
              - g (toLp 2 ((ofLp z₀).1 + R • (xb + s • p₀), (ofLp z₀).2 + R * s)))) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  -- the affine map transports weighted means
  have hmeanmap : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), (∑ i, θ i) = 1 →
      (∑ i, θ i • ((ofLp z₀).1 + R • (y i + s • p₀)))
        = (ofLp z₀).1 + R • ((∑ i, θ i • y i) + s • p₀) := by
    intro n θ y hsum
    have hA : (∑ i, θ i • ((ofLp z₀).1 + R • (y i + s • p₀)))
        = (∑ i, θ i • (ofLp z₀).1) + (∑ i, θ i • (R • (y i + s • p₀))) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => by rw [smul_add])
    have hB : (∑ i, θ i • (ofLp z₀).1) = (ofLp z₀).1 := by
      rw [← Finset.sum_smul, hsum, one_smul]
    have hC : (∑ i, θ i • (R • (y i + s • p₀)))
        = R • (∑ i, θ i • y i) + R • (s • p₀) := by
      have hC1 : ∀ i : Fin n, θ i • (R • (y i + s • p₀))
          = R • (θ i • y i) + (θ i * R) • (s • p₀) := fun i => by module
      rw [Finset.sum_congr rfl (fun i _ => hC1 i), Finset.sum_add_distrib,
        ← Finset.smul_sum, ← Finset.sum_smul,
        show (∑ i, θ i * R) = R from by rw [← Finset.sum_mul, hsum, one_mul]]
    rw [hA, hB, hC, smul_add]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n θ y xb
    constructor
    · rintro ⟨hpos, hsum, hmean⟩
      refine ⟨hpos, hsum, ?_⟩
      rw [hmeanmap n θ y hsum] at hmean
      have h2 : R • ((∑ i, θ i • y i) + s • p₀) = R • (xb + s • p₀) :=
        add_left_cancel hmean
      have h3 : (∑ i, θ i • y i) + s • p₀ = xb + s • p₀ :=
        smul_right_injective F hRne h2
      exact add_right_cancel h3
    · rintro ⟨hpos, hsum, hmean⟩
      refine ⟨hpos, hsum, ?_⟩
      rw [hmeanmap n θ y hsum, hmean]
  · intro n θ y xb
    have hnorm : ∀ i : Fin n, ‖((ofLp z₀).1 + R • (y i + s • p₀))
        - ((ofLp z₀).1 + R • (xb + s • p₀))‖ ^ 2 = R ^ 2 * ‖y i - xb‖ ^ 2 := by
      intro i
      have hdiff : ((ofLp z₀).1 + R • (y i + s • p₀))
          - ((ofLp z₀).1 + R • (xb + s • p₀)) = R • (y i - xb) := by
        rw [smul_sub, smul_add, smul_add]
        abel
      rw [hdiff, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    have hsumeq : (∑ i, θ i * ‖((ofLp z₀).1 + R • (y i + s • p₀))
        - ((ofLp z₀).1 + R • (xb + s • p₀))‖ ^ 2)
        = R ^ 2 * (∑ i, θ i * ‖y i - xb‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hnorm i]
      ring
    rw [BaryRadius, BaryRadius, hsumeq]
    rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ R ^ 2)]
    rw [Real.sqrt_sq hR.le]
  · intro Y
    refine ⟨R⁻¹ • (Y - (ofLp z₀).1) - s • p₀, ?_⟩
    rw [show (R⁻¹ • (Y - (ofLp z₀).1) - s • p₀) + s • p₀
      = R⁻¹ • (Y - (ofLp z₀).1) from by abel, smul_smul, mul_inv_cancel₀ hRne, one_smul]
    abel
  · intro n θ y xb hcfg
    obtain ⟨hpos, hsum, hmean⟩ := hcfg
    have hframe : ∀ w : F, FrameChange g z₀ R p₀ a₀ (toLp 2 (w, s))
        = (g (toLp 2 ((ofLp z₀).1 + R • (w + s • p₀), (ofLp z₀).2 + R * s)) - g z₀) / R
          - inner ℝ p₀ w - (a₀ + ‖p₀‖ ^ 2 / 2) * s := by
      intro w
      have h1 : z₀ + toLp 2 (R • (w + s • p₀), R * s)
          = toLp 2 ((ofLp z₀).1 + R • (w + s • p₀), (ofLp z₀).2 + R * s) := rfl
      simp only [FrameChange, h1]
    have hinner : (∑ i, θ i * (inner ℝ p₀ (y i) : ℝ)) = inner ℝ p₀ xb := by
      rw [← hmean, inner_sum]
      exact Finset.sum_congr rfl
        (fun i _ => (real_inner_smul_right p₀ (y i) (θ i)).symm)
    have hexp : (∑ i, θ i * FrameChange g z₀ R p₀ a₀ (toLp 2 (y i, s)))
        = (1 / R) * (∑ i, θ i * g (toLp 2 ((ofLp z₀).1 + R • (y i + s • p₀),
              (ofLp z₀).2 + R * s)))
          - (1 / R) * g z₀
          - (∑ i, θ i * (inner ℝ p₀ (y i) : ℝ))
          - (∑ i, θ i) * ((a₀ + ‖p₀‖ ^ 2 / 2) * s) := by
      have h1 : ∀ i : Fin n, θ i * FrameChange g z₀ R p₀ a₀ (toLp 2 (y i, s))
          = (1 / R) * (θ i * g (toLp 2 ((ofLp z₀).1 + R • (y i + s • p₀),
                (ofLp z₀).2 + R * s)))
            - ((1 / R) * g z₀) * θ i
            - θ i * (inner ℝ p₀ (y i) : ℝ)
            - θ i * ((a₀ + ‖p₀‖ ^ 2 / 2) * s) := by
        intro i
        rw [hframe (y i)]
        field_simp
      rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [show (∑ i, (1 / R * g z₀) * θ i) = 1 / R * g z₀ from by
        rw [← Finset.mul_sum, hsum, mul_one]]
      rw [← Finset.sum_mul]
    rw [hexp, hframe xb, hinner, hsum]
    field_simp
    ring
