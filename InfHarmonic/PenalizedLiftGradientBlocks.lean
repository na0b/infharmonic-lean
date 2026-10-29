import InfHarmonic.SecondFDerivCompLinear
open Set Metric Filter Topology
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Spatial blocks of the gradient of a penalised lift.  Let `L` collect the `N` spatial
blocks of a product configuration together with the *average* of its `N` time
coordinates, let `M` record the deviations of those time coordinates from their
average, and set `Ψ := g ∘ L + lam * ‖M ·‖²/2`.  The penalty depends only on time
coordinates, so it contributes nothing in the spatial directions: the `i`-th spatial
block of `∇Ψ` at `W` is the `i`-th spatial block of `∇g` at `L W`, for every weight
`lam`. -/
theorem PenalizedLiftGradientBlocks (N : ℕ)
    (L : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) →L[ℝ]
      WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ))
    (hL : ∀ W, L W = toLp 2 (toLp 2 (fun i => (ofLp (ofLp W i)).1),
      (N:ℝ)⁻¹ * ∑ i, (ofLp (ofLp W i)).2))
    (M : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) →L[ℝ] PiLp 2 (fun _ : Fin N => ℝ))
    (hM : ∀ W, M W = toLp 2 (fun i => (ofLp (ofLp W i)).2
      - (N:ℝ)⁻¹ * ∑ j, (ofLp (ofLp W j)).2))
    (g : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) → ℝ) (lam : ℝ)
    (W : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)))
    (hg : ContDiffAt ℝ 2 g (L W)) :
    ∀ i, (ofLp (ofLp (∇ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2)) W) i)).1
      = ofLp (ofLp (∇ g (L W))).1 i := by
  have hgd : DifferentiableAt ℝ g (L W) := hg.differentiableAt (by norm_num)
  have hq : ContDiff ℝ 2 (fun u : PiLp 2 (fun _ : Fin N => ℝ) => ‖u‖ ^ 2 / 2) :=
  (contDiff_norm_sq ℝ).div_const _
  intro i
  refine ext_inner_left ℝ (fun a => ?_)
  -- the test direction whose `i`-th block is `(a, 0)` and whose others vanish
  obtain ⟨ξ, hξ⟩ : ∃ ξ : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)),
      ξ = toLp 2 (Pi.single i (toLp 2 (a, (0:ℝ)))) := ⟨_, rfl⟩
  have hξj : ∀ j, ofLp ξ j = if j = i then (toLp 2 (a, (0:ℝ))) else 0 := by
    intro j; rw [hξ]; simp [Pi.single_apply]
  have hξ1 : ∀ j, (ofLp (ofLp ξ j)).1 = if j = i then a else 0 := by
    intro j; rw [hξj j]; split <;> simp
  have hξ2 : ∀ j, (ofLp (ofLp ξ j)).2 = 0 := by
    intro j; rw [hξj j]; split <;> simp
  have hsum0 : ∑ j, (ofLp (ofLp ξ j)).2 = (0:ℝ) :=
    Finset.sum_eq_zero fun j _ => hξ2 j
  -- `ξ` has no time content, so `M` kills it and `L` sends it to `(ι_i a, 0)`
  have hMξ : M ξ = 0 := by
    have h1 : M ξ = toLp 2 (fun _ : Fin N => (0:ℝ)) := by
      rw [hM]; congr 1; funext j; rw [hξ2 j, hsum0, mul_zero, sub_zero]
    rw [h1]; rfl
  have hLξ : L ξ = toLp 2 (toLp 2 (Pi.single i a), (0:ℝ)) := by
    rw [hL]
    congr 1
    refine Prod.ext ?_ ?_
    · simp only
      congr 1
      funext j
      rw [hξ1 j, Pi.single_apply]
    · show (N:ℝ)⁻¹ * ∑ j, (ofLp (ofLp ξ j)).2 = 0
      rw [hsum0, mul_zero]
  -- the derivative of the penalty annihilates `ξ`
  have hpen : fderiv ℝ (fun U => lam * (‖M U‖ ^ 2 / 2)) W ξ = 0 := by
    have h1 : HasFDerivAt (fun U => ‖M U‖ ^ 2 / 2)
        ((fderiv ℝ (fun u : PiLp 2 (fun _ : Fin N => ℝ) => ‖u‖ ^ 2 / 2) (M W)).comp M) W :=
      (hq.differentiable (by norm_num) (M W)).hasFDerivAt.comp W M.hasFDerivAt
    rw [(h1.const_mul lam).fderiv]
    simp [hMξ]
  have hgL : HasFDerivAt (fun U => g (L U)) ((fderiv ℝ g (L W)).comp L) W :=
    hgd.hasFDerivAt.comp W L.hasFDerivAt
  have hd2 : DifferentiableAt ℝ (fun U => lam * (‖M U‖ ^ 2 / 2)) W :=
    (((hq.differentiable (by norm_num)).comp M.differentiable).const_mul lam) W
  have hsum : fderiv ℝ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2)) W ξ
      = fderiv ℝ g (L W) (L ξ) := by
    have h3 : HasFDerivAt (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2))
        ((fderiv ℝ g (L W)).comp L
          + fderiv ℝ (fun U => lam * (‖M U‖ ^ 2 / 2)) W) W :=
      hgL.add hd2.hasFDerivAt
    rw [h3.fderiv]
    simp only [add_apply, hpen, add_zero]
    rfl
  -- both sides are the value of a derivative on the same test direction
  have hleft : (inner ℝ a
        (ofLp (ofLp (∇ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2)) W) i)).1 : ℝ)
      = fderiv ℝ (fun U => g (L U) + lam * (‖M U‖ ^ 2 / 2)) W ξ := by
    rw [← inner_gradient_left, PiLp.inner_apply,
      Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · rw [hξj i]
      simp [WithLp.prod_inner_apply, real_inner_comm]
    · intro j _ hj
      rw [hξj j]
      simp [hj]
  have hright : (inner ℝ a (ofLp (ofLp (∇ g (L W))).1 i) : ℝ)
      = fderiv ℝ g (L W) (L ξ) := by
    rw [← inner_gradient_left, hLξ, WithLp.prod_inner_apply]
    simp only [inner_zero_right, add_zero]
    rw [PiLp.inner_apply, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · simp [real_inner_comm]
    · intro j _ hj
      simp [hj]
  rw [hleft, hright, hsum]
