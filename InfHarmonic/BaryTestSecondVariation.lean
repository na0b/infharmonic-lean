import InfHarmonic.LimitOp
import InfHarmonic.SecondFDerivCompLinear
import InfHarmonic.SecondVariationAddAffineOnLine
import InfHarmonic.BaryVarianceAffineAlongMotion
open Filter Topology
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The barycentric test function is admissible, and its second variation in the
common-time direction is exactly the limiting operator applied to the original test
function.  Lifting `φ` to the product by `Φ(Y,t) = φ(X(Y),t) + ct + Q(Y)/(2t)` adds two
summands that are affine along the straight motion with velocity
`((p + (y₀ᵢ - x₀)/t₀)ᵢ, 1)`, so neither contributes; what is left is `φ` composed with the
linear map `(Y,t) ↦ (X(Y),t)`, which sends that velocity to `(p, 1)`. -/
theorem BaryTestSecondVariation (n : ℕ) (θ : Fin n → ℝ) (hθ1 : ∑ i, θ i = 1)
    (y₀ : Fin n → F) (x₀ : F) (hmean : ∑ i, θ i • y₀ i = x₀)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (c : ℝ) (φ : WithLp 2 (F × ℝ) → ℝ)
    (hφ : ContDiffAt ℝ 2 φ (toLp 2 (x₀, t₀)))
    (Φ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) → ℝ)
    (hΦ : ∀ W, Φ W = φ (toLp 2 (∑ j, θ j • ofLp (ofLp W).1 j, (ofLp W).2))
        + c * (ofLp W).2
        + (∑ j, θ j * ‖ofLp (ofLp W).1 j - ∑ k, θ k • ofLp (ofLp W).1 k‖ ^ 2)
            / (2 * (ofLp W).2)) :
    ContDiffAt ℝ 2 Φ (toLp 2 (toLp 2 y₀, t₀))
      ∧ iteratedFDeriv ℝ 2 Φ (toLp 2 (toLp 2 y₀, t₀))
          (fun _ => toLp 2 (toLp 2 (fun i => (ofLp (∇ φ (toLp 2 (x₀, t₀)))).1
            + (t₀)⁻¹ • (y₀ i - x₀)), (1:ℝ)))
        = LimitOp φ (toLp 2 (x₀, t₀)) := by
  have ht0 : t₀ ≠ 0 := ne_of_gt ht₀
  -- the projections and the weighted mean, assembled from library pieces
  obtain ⟨P, hP⟩ : ∃ P : Fin n → (PiLp 2 (fun _ : Fin n => F) →L[ℝ] F),
      ∀ j Y, P j Y = ofLp Y j :=
    ⟨fun j => (ContinuousLinearMap.proj j).comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => F)).toContinuousLinearMap,
     fun j Y => rfl⟩
  obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ]
        PiLp 2 (fun _ : Fin n => F), ∀ W, π₁ W = (ofLp W).1 :=
    ⟨(ContinuousLinearMap.fst ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ
        ).toContinuousLinearMap, fun W => rfl⟩
  obtain ⟨π₂, hπ₂⟩ : ∃ π₂ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ] ℝ,
      ∀ W, π₂ W = (ofLp W).2 :=
    ⟨(ContinuousLinearMap.snd ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ
        ).toContinuousLinearMap, fun W => rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : PiLp 2 (fun _ : Fin n => F) →L[ℝ] F,
      ∀ Y, X Y = ∑ j, θ j • ofLp Y j := by
    refine ⟨∑ j, θ j • P j, fun Y => ?_⟩
    rw [sum_apply]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_apply, hP]
  obtain ⟨L, hL⟩ : ∃ L : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ]
        WithLp 2 (F × ℝ), ∀ W, L W = toLp 2 (∑ j, θ j • ofLp (ofLp W).1 j, (ofLp W).2) := by
    refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
      ((X.comp π₁).prod π₂), fun W => ?_⟩
    show toLp 2 (X (π₁ W), π₂ W) = _
    rw [hπ₁, hπ₂, hX]
  obtain ⟨M, hM⟩ : ∃ M : Fin n → (WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ] F),
      ∀ j W, M j W = ofLp (ofLp W).1 j - ∑ k, θ k • ofLp (ofLp W).1 k := by
    refine ⟨fun j => (P j).comp π₁ - X.comp π₁, fun j W => ?_⟩
    show (P j) (π₁ W) - X (π₁ W) = _
    rw [hπ₁, hP, hX]
  -- the base point, the velocity, and their images
  obtain ⟨p, hp⟩ : ∃ p : F, p = (ofLp (∇ φ (toLp 2 (x₀, t₀)))).1 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : Fin n → F, q = fun i => p + (t₀)⁻¹ • (y₀ i - x₀) := ⟨_, rfl⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W, W = (toLp 2 (toLp 2 y₀, t₀) :
      WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ)) := ⟨_, rfl⟩
  obtain ⟨ζ, hζ⟩ : ∃ ζ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ),
      ζ = toLp 2 (toLp 2 q, (1:ℝ)) := ⟨_, rfl⟩
  have hπ₂W₀ : π₂ W₀ = t₀ := by rw [hπ₂, hW₀]
  have hLW₀ : L W₀ = toLp 2 (x₀, t₀) := by
    rw [hL, hW₀]
    congr 1
    refine Prod.ext ?_ rfl
    show (∑ j, θ j • y₀ j) = x₀
    exact hmean
  -- the weighted mean of the velocities is `p`
  have hoff0 : ∑ j, θ j • (y₀ j - x₀) = 0 := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hθ1, one_smul, sub_self]
  have hqmean : ∑ j, θ j • q j = p := by
    rw [hq]
    simp only [smul_add]
    rw [Finset.sum_add_distrib, ← Finset.sum_smul, hθ1, one_smul]
    have h : ∑ j, θ j • ((t₀)⁻¹ • (y₀ j - x₀)) = (t₀)⁻¹ • ∑ j, θ j • (y₀ j - x₀) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_comm]
    rw [h, hoff0, smul_zero, add_zero]
  have hLζ : L ζ = toLp 2 (p, (1:ℝ)) := by
    rw [hL, hζ]
    congr 1
    refine Prod.ext ?_ rfl
    show (∑ j, θ j • q j) = p
    exact hqmean
  -- the three summands of `Φ`
  obtain ⟨g, hg⟩ : ∃ g : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) → ℝ,
      g = fun W => φ (L W) + c * π₂ W := ⟨_, rfl⟩
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) → ℝ,
      ψ = fun W => (∑ j, θ j * ‖M j W‖ ^ 2) / (2 * π₂ W) := ⟨_, rfl⟩
  have hΦfun : Φ = fun W => g W + ψ W := by
    funext W
    rw [hΦ W]
    simp only [hg, hψdef]
    rw [hL W, hπ₂ W]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by rw [hM]
  -- regularity of each summand at the base point
  have hφL : ContDiffAt ℝ 2 (fun W => φ (L W)) W₀ := by
    refine ContDiffAt.comp W₀ ?_ (L.contDiff (n := 2)).contDiffAt
    rw [hLW₀]; exact hφ
  have hct : ContDiffAt ℝ 2 (fun W => c * π₂ W) W₀ :=
    (contDiff_const.mul (π₂.contDiff (n := 2))).contDiffAt
  have hgC2 : ContDiffAt ℝ 2 g W₀ := by rw [hg]; exact hφL.add hct
  have hψC2 : ContDiffAt ℝ 2 ψ W₀ := by
    rw [hψdef]
    refine ContDiffAt.div ?_ ?_ ?_
    · refine ContDiffAt.sum fun j _ => ?_
      refine contDiff_const.contDiffAt.mul ?_
      exact ((contDiff_norm_sq ℝ).comp ((M j).contDiff (n := 2))).contDiffAt
    · exact (contDiff_const.mul (π₂.contDiff (n := 2))).contDiffAt
    · rw [hπ₂W₀]; positivity
  have hΦC2 : ContDiffAt ℝ 2 Φ W₀ := by rw [hΦfun]; exact hgC2.add hψC2
  refine ⟨by rw [← hW₀]; exact hΦC2, ?_⟩
  -- the straight motion in coordinates
  have hblocks : ∀ (h : ℝ) (i : Fin n), ofLp (ofLp (W₀ + h • ζ)).1 i = y₀ i + h • q i := by
    intro h i; rw [hW₀, hζ]; rfl
  have htime : ∀ h : ℝ, π₂ (W₀ + h • ζ) = t₀ + h := by
    intro h
    rw [hπ₂, hW₀, hζ]
    show t₀ + h * 1 = t₀ + h
    rw [mul_one]
  -- the variance summand is affine along it
  have haffψ : ∀ᶠ h : ℝ in nhds (0:ℝ),
      ψ (W₀ + h • ζ) = (∑ i, θ i * ‖y₀ i - x₀‖ ^ 2) / (2 * t₀)
        + (∑ i, θ i * ‖y₀ i - x₀‖ ^ 2) / (2 * t₀ ^ 2) * h := by
    have hnb : {h : ℝ | 0 < t₀ + h} ∈ nhds (0:ℝ) := by
      refine (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds ?_
      simpa using ht₀
    filter_upwards [hnb] with h hh
    rw [hψdef]
    show (∑ j, θ j * ‖M j (W₀ + h • ζ)‖ ^ 2) / (2 * π₂ (W₀ + h • ζ)) = _
    rw [htime h]
    have e : ∀ j, M j (W₀ + h • ζ)
        = (y₀ j + h • q j) - ∑ k, θ k • (y₀ k + h • q k) := by
      intro j
      rw [hM, hblocks h j]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by rw [hblocks h k]
    rw [Finset.sum_congr rfl fun j _ => by rw [e j], hq]
    exact BaryVarianceAffineAlongMotion n θ hθ1 y₀ x₀ hmean t₀ ht₀ p h hh
  -- and so is the time summand
  have haffct : ∀ᶠ h : ℝ in nhds (0:ℝ),
      (fun W => c * π₂ W) (W₀ + h • ζ) = c * t₀ + c * h := by
    filter_upwards with h
    show c * π₂ (W₀ + h • ζ) = _
    rw [htime h]; ring
  -- strip the penalty, then the time summand
  have hstep1 : iteratedFDeriv ℝ 2 Φ W₀ (fun _ => ζ)
      = iteratedFDeriv ℝ 2 g W₀ (fun _ => ζ) := by
    rw [hΦfun]
    exact SecondVariationAddAffineOnLine g ψ W₀ ζ hgC2 hψC2 _ _ haffψ
  have hstep2 : iteratedFDeriv ℝ 2 g W₀ (fun _ => ζ)
      = iteratedFDeriv ℝ 2 (fun W => φ (L W)) W₀ (fun _ => ζ) := by
    rw [hg]
    exact SecondVariationAddAffineOnLine (fun W => φ (L W)) (fun W => c * π₂ W) W₀ ζ
      hφL hct _ _ haffct
  -- what is left is the operator, because `L` sends the velocity to `(p, 1)`
  have hstep3 : iteratedFDeriv ℝ 2 (fun W => φ (L W)) W₀ (fun _ => ζ)
      = iteratedFDeriv ℝ 2 φ (toLp 2 (x₀, t₀)) (fun _ => toLp 2 (p, (1:ℝ))) := by
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply,
      SecondFDerivCompLinear L φ W₀ (by rw [hLW₀]; exact hφ) ζ ζ, hLW₀, hLζ]
  have hdirq : (fun i => (ofLp (∇ φ (toLp 2 (x₀, t₀)))).1 + (t₀)⁻¹ • (y₀ i - x₀)) = q := by
    rw [hq, hp]
  rw [← hW₀, hdirq, ← hζ, hstep1, hstep2, hstep3]
  simp only [LimitOp]
  rw [hp]
