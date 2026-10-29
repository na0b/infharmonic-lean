module

public import InfHarmonic.Preamble

@[expose] public section
open Filter Topology
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The common-time directions produced by the barycentric test function.  Hold a
weighted configuration `(θ, y₀)` of mean `x₀` fixed and lift a test function `φ` to the
product by `Φ(Y,t) = φ(X(Y),t) + ct + Q(Y)/(2t)`, where `X` is the weighted mean and `Q`
the weighted variance about it.  Then the direction the common-time sum rule reads off
the `i`-th block of `∇Φ`, namely `θᵢ⁻¹ ∇_{yᵢ}Φ`, is exactly `p + (y₀ᵢ - x₀)/t₀` with
`p = ∇_x φ`.  The penalty contributes the offset `(y₀ᵢ - x₀)/t₀` and nothing else, and
the constant-in-time term contributes nothing at all. -/
theorem BaryTestDirections (n : ℕ) (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i)
    (hθ1 : ∑ i, θ i = 1)
    (y₀ : Fin n → F) (x₀ : F) (hmean : ∑ i, θ i • y₀ i = x₀)
    (t₀ : ℝ) (ht₀ : 0 < t₀) (c : ℝ) (φ : WithLp 2 (F × ℝ) → ℝ)
    (hφ : ContDiffAt ℝ 2 φ (toLp 2 (x₀, t₀)))
    (Φ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) → ℝ)
    (hΦ : ∀ W, Φ W = φ (toLp 2 (∑ j, θ j • ofLp (ofLp W).1 j, (ofLp W).2))
        + c * (ofLp W).2
        + (∑ j, θ j * ‖ofLp (ofLp W).1 j - ∑ k, θ k • ofLp (ofLp W).1 k‖ ^ 2)
            / (2 * (ofLp W).2)) :
    ∀ i, (θ i)⁻¹ • ofLp (ofLp (∇ Φ (toLp 2 (toLp 2 y₀, t₀)))).1 i
      = (ofLp (∇ φ (toLp 2 (x₀, t₀)))).1 + (t₀)⁻¹ • (y₀ i - x₀) := by
  -- the coordinate, projection and mean maps, all assembled from library pieces
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
  -- the base point of the product and its images
  obtain ⟨W₀, hW₀⟩ : ∃ W, W = (toLp 2 (toLp 2 y₀, t₀) :
      WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ)) := ⟨_, rfl⟩
  have hπ₂W₀ : π₂ W₀ = t₀ := by rw [hπ₂, hW₀]
  have hLW₀ : L W₀ = toLp 2 (x₀, t₀) := by
    rw [hL, hW₀]
    congr 1
    refine Prod.ext ?_ rfl
    show (∑ j, θ j • y₀ j) = x₀
    exact hmean
  have hMW₀ : ∀ j, M j W₀ = y₀ j - x₀ := by
    intro j
    rw [hM, hW₀]
    show y₀ j - (∑ k, θ k • y₀ k) = y₀ j - x₀
    rw [hmean]
  have hoff0 : ∑ j, θ j • (y₀ j - x₀) = 0 := by
    simp only [smul_sub]
    rw [Finset.sum_sub_distrib, hmean, ← Finset.sum_smul, hθ1, one_smul, sub_self]
  -- the derivative of `Φ` at the base point
  have hφd : DifferentiableAt ℝ φ (L W₀) := by
    rw [hLW₀]; exact hφ.differentiableAt (by norm_num)
  obtain ⟨N, hNdef⟩ : ∃ N : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) → ℝ,
      N = fun W => ∑ j, θ j * ‖M j W‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨DN, hDNdef⟩ : ∃ DN : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ] ℝ,
      DN = ∑ j, θ j • (2 • (innerSL ℝ (M j W₀)).comp (M j)) := ⟨_, rfl⟩
  have hNd : HasFDerivAt N DN W₀ := by
    rw [hNdef, hDNdef]
    refine HasFDerivAt.fun_sum fun j _ => ?_
    have h1 : HasFDerivAt (fun W => ‖M j W‖ ^ 2)
        (2 • (innerSL ℝ (M j W₀)).comp (M j)) W₀ := (M j).hasFDerivAt.norm_sq
    exact h1.const_mul (θ j)
  obtain ⟨dinv, hdinv⟩ : ∃ d : ℝ, HasDerivAt (fun t : ℝ => (2 * t)⁻¹) d t₀ :=
    ⟨_, ((hasDerivAt_id t₀).const_mul (2:ℝ)).inv (by positivity)⟩
  have huf : HasFDerivAt (fun W => (2 * π₂ W)⁻¹) (dinv • π₂) W₀ := by
    have hpt : HasDerivAt (fun t : ℝ => (2 * t)⁻¹) dinv (π₂ W₀) := by
      rw [hπ₂W₀]; exact hdinv
    have h := hpt.comp_hasFDerivAt W₀ (π₂.hasFDerivAt (x := W₀))
    exact h
  have hpen : HasFDerivAt (fun W => N W * (2 * π₂ W)⁻¹)
      (N W₀ • (dinv • π₂) + (2 * π₂ W₀)⁻¹ • DN) W₀ := by
    have h := hNd.mul huf
    exact h
  have hcomp : HasFDerivAt (fun W => φ (L W)) ((fderiv ℝ φ (L W₀)).comp L) W₀ :=
    hφd.hasFDerivAt.comp W₀ L.hasFDerivAt
  have hct : HasFDerivAt (fun W => c * π₂ W) (c • π₂) W₀ := by
    have h := (π₂.hasFDerivAt (x := W₀)).const_mul c
    exact h
  have hΦrw : ∀ W, Φ W = (φ (L W) + c * π₂ W) + N W * (2 * π₂ W)⁻¹ := by
    intro W
    rw [hΦ W, hL W, hπ₂ W, div_eq_mul_inv]
    simp only [hNdef]
    congr 2
    exact Finset.sum_congr rfl fun j _ => by rw [hM]
  have hΦd : HasFDerivAt Φ
      (((fderiv ℝ φ (L W₀)).comp L + c • π₂)
        + (N W₀ • (dinv • π₂) + (2 * π₂ W₀)⁻¹ • DN)) W₀ := by
    have h := (hcomp.add hct).add hpen
    exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun W => hΦrw W)
  -- now test the gradient against the `i`-th block
  intro i
  rw [← hW₀]
  have hθi : θ i ≠ 0 := ne_of_gt (hθ i)
  have ht0 : t₀ ≠ 0 := ne_of_gt ht₀
  have hblock : ofLp (ofLp (∇ Φ W₀)).1 i
      = θ i • ((ofLp (∇ φ (toLp 2 (x₀, t₀)))).1 + (t₀)⁻¹ • (y₀ i - x₀)) := by
    refine ext_inner_right ℝ fun a => ?_
    -- the test direction: `i`-th block `a`, no time component
    obtain ⟨e, he⟩ : ∃ e : Fin n → F, e = Pi.single i a := ⟨_, rfl⟩
    have hei : e i = a := by rw [he, Pi.single_eq_same]
    have hej : ∀ j, j ≠ i → e j = 0 := fun j hj => by rw [he, Pi.single_eq_of_ne hj]
    obtain ⟨ξ, hξ⟩ : ∃ ξ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ),
        ξ = toLp 2 (toLp 2 e, (0:ℝ)) := ⟨_, rfl⟩
    have hπ₂ξ : π₂ ξ = 0 := by rw [hπ₂, hξ]
    have hsingle : (∑ j, θ j • e j) = θ i • a := by
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rw [hei]
      · intro j _ hj; rw [hej j hj, smul_zero]
    have hLξ : L ξ = toLp 2 (θ i • a, (0:ℝ)) := by
      rw [hL, hξ]
      congr 1
      refine Prod.ext ?_ rfl
      show (∑ j, θ j • e j) = θ i • a
      exact hsingle
    have hMξ : ∀ j : Fin n, M j ξ = e j - θ i • a := by
      intro j
      rw [hM, hξ]
      show e j - (∑ k, θ k • e k) = _
      rw [hsingle]
    -- the three summands of the derivative, evaluated on the test direction
    have hterm1 : ((fderiv ℝ φ (L W₀)).comp L) ξ
        = θ i * inner ℝ (ofLp (∇ φ (toLp 2 (x₀, t₀)))).1 a := by
      show fderiv ℝ φ (L W₀) (L ξ) = _
      rw [← inner_gradient_left, hLξ, hLW₀, WithLp.prod_inner_apply]
      simp only [inner_zero_right, add_zero]
      rw [real_inner_smul_right]
    have hzero : ∀ r : ℝ, (r • π₂) ξ = 0 := by
      intro r; simp only [smul_apply, smul_eq_mul, hπ₂ξ, mul_zero]
    have hoff0' : ∑ j, θ j * (inner ℝ (y₀ j - x₀) a : ℝ) = 0 := by
      have e : ∀ j, θ j * (inner ℝ (y₀ j - x₀) a : ℝ)
          = inner ℝ (θ j • (y₀ j - x₀)) a := fun j => by rw [real_inner_smul_left]
      rw [Finset.sum_congr rfl fun j _ => e j, ← sum_inner, hoff0, inner_zero_left]
    have hDNξ : DN ξ = 2 * (θ i * inner ℝ (y₀ i - x₀) a) := by
      rw [hDNdef, sum_apply]
      have e1 : ∀ j, (θ j • (2 • (innerSL ℝ (M j W₀)).comp (M j))) ξ
          = 2 * (θ j * (inner ℝ (y₀ j - x₀) (e j) : ℝ))
            - 2 * θ i * (θ j * (inner ℝ (y₀ j - x₀) a : ℝ)) := by
        intro j
        rw [smul_apply, smul_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
          innerSL_apply_apply, hMW₀, hMξ, inner_sub_right, real_inner_smul_right]
        simp only [smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
        ring
      rw [Finset.sum_congr rfl fun j _ => e1 j, Finset.sum_sub_distrib]
      have e2 : ∑ j, 2 * (θ j * (inner ℝ (y₀ j - x₀) (e j) : ℝ))
          = 2 * (θ i * inner ℝ (y₀ i - x₀) a) := by
        rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
        · rw [hei]
        · intro j _ hj; rw [hej j hj, inner_zero_right]; ring
      have e3 : ∑ j, 2 * θ i * (θ j * (inner ℝ (y₀ j - x₀) a : ℝ)) = 0 := by
        rw [← Finset.mul_sum, hoff0', mul_zero]
      rw [e2, e3, sub_zero]
    -- the block of the gradient is read off by pairing with the test direction
    have hinner : (inner ℝ (ofLp (ofLp (∇ Φ W₀)).1 i) a : ℝ) = fderiv ℝ Φ W₀ ξ := by
      rw [← inner_gradient_left, hξ, WithLp.prod_inner_apply]
      simp only [inner_zero_right, add_zero]
      have hofe : ∀ j : Fin n, ofLp (toLp 2 e) j = e j := fun j => rfl
      rw [PiLp.inner_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · rw [hofe i, hei]
      · intro j _ hj; rw [hofe j, hej j hj, inner_zero_right]
    rw [hinner, hΦd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, hterm1, hzero, hDNξ, hπ₂W₀, add_zero,
      zero_add, mul_zero, inner_add_left, real_inner_smul_left]
    field_simp
  rw [hblock, inv_smul_smul₀ hθi]
