module

public import InfHarmonic.QuadEnvP
public import InfHarmonic.QuadShiftCompleteSquare
public import InfHarmonic.PartialSupConcaveOfAttained

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The forward envelope, corrected by the quadratic of its own time, is concave in the
centre.  If `f(·, t+l)` is concave after subtracting `|·|²/(2(t+l))`, and the supremum
defining `P_l f(·, t)` is attained at every centre, then
`x ↦ P_l f(x,t) - |x|²/(2t)` is concave.  Completing the square turns the defining
supremum into the partial supremum of a function that is jointly concave in the centre and
the competitor, and an attained partial supremum of a jointly concave function is
concave. -/
theorem QuadEnvPConcaveCorrection (f : WithLp 2 (F × ℝ) → ℝ) (t l : ℝ)
    (ht : 0 < t) (hl : 0 < l)
    (hconc : ConcaveOn ℝ (Set.univ : Set F)
      (fun y : F => f (toLp 2 (y, t + l)) - ‖y‖ ^ 2 / (2 * (t + l))))
    (hat : ∀ x : F, ∃ y : F, QuadEnvP f l (toLp 2 (x, t))
        = f (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l))
    (hub : ∀ x y : F, f (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l)
        ≤ QuadEnvP f l (toLp 2 (x, t))) :
    ConcaveOn ℝ (Set.univ : Set F)
      (fun x : F => QuadEnvP f l (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t)) := by
  have hs : (0:ℝ) < t + l := by linarith
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = t / (2 * l * (t + l)) := ⟨_, rfl⟩
  obtain ⟨c, hcd⟩ : ∃ c : ℝ, c = (t + l) / t := ⟨_, rfl⟩
  have ha : 0 < a := by rw [had]; positivity
  -- the convex-combination identity for the squared norm
  have hquad : ∀ (u₀ u₁ : F) (α β : ℝ), α + β = 1 →
      ‖α • u₀ + β • u₁‖ ^ 2
        = α * ‖u₀‖ ^ 2 + β * ‖u₁‖ ^ 2 - α * β * ‖u₀ - u₁‖ ^ 2 := by
    intro u₀ u₁ α β hαβ
    have hβ : β = 1 - α := by linarith
    subst hβ
    rw [norm_add_sq_real, norm_smul, norm_smul, norm_sub_sq_real,
      real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  -- the jointly concave function whose partial supremum the envelope is
  obtain ⟨Φ, hΦd⟩ : ∃ Φ : F × F → ℝ, Φ = fun p : F × F =>
      (f (toLp 2 (p.2, t + l)) - ‖p.2‖ ^ 2 / (2 * (t + l)))
        + -(a * ‖p.2 - c • p.1‖ ^ 2) := ⟨_, rfl⟩
  -- it is concave in the competitor alone, by hypothesis
  have hfst : ConcaveOn ℝ (Set.univ : Set (F × F))
      (fun p : F × F => f (toLp 2 (p.2, t + l)) - ‖p.2‖ ^ 2 / (2 * (t + l))) := by
    refine ⟨convex_univ, fun p₀ _ p₁ _ α β hα hβ hαβ => ?_⟩
    have h := hconc.2 (Set.mem_univ p₀.2) (Set.mem_univ p₁.2) hα hβ hαβ
    exact h
  -- and the penalty is the negative of a nonnegative quadratic form in the pair
  have hsq : ConcaveOn ℝ (Set.univ : Set (F × F))
      (fun p : F × F => -(a * ‖p.2 - c • p.1‖ ^ 2)) := by
    refine ⟨convex_univ, fun p₀ _ p₁ _ α β hα hβ hαβ => ?_⟩
    have hlin : (α • p₀ + β • p₁).2 - c • (α • p₀ + β • p₁).1
        = α • (p₀.2 - c • p₀.1) + β • (p₁.2 - c • p₁.1) := by
      show α • p₀.2 + β • p₁.2 - c • (α • p₀.1 + β • p₁.1) = _
      module
    show α • -(a * ‖p₀.2 - c • p₀.1‖ ^ 2) + β • -(a * ‖p₁.2 - c • p₁.1‖ ^ 2)
      ≤ -(a * ‖(α • p₀ + β • p₁).2 - c • (α • p₀ + β • p₁).1‖ ^ 2)
    rw [hlin, hquad _ _ α β hαβ]
    have hnn : 0 ≤ a * (α * β * ‖(p₀.2 - c • p₀.1) - (p₁.2 - c • p₁.1)‖ ^ 2) := by
      have : (0:ℝ) ≤ α * β := mul_nonneg hα hβ
      positivity
    simp only [smul_eq_mul]
    nlinarith [hnn]
  have hΦ : ConcaveOn ℝ (Set.univ : Set (F × F)) Φ := by
    refine ⟨convex_univ, fun p₀ _ p₁ _ α β hα hβ hαβ => ?_⟩
    have h1 := hfst.2 (Set.mem_univ p₀) (Set.mem_univ p₁) hα hβ hαβ
    have h2 := hsq.2 (Set.mem_univ p₀) (Set.mem_univ p₁) hα hβ hαβ
    simp only [hΦd, smul_eq_mul] at h1 h2 ⊢
    linarith
  -- completing the square identifies `Φ` with the competitor value, shifted by a constant
  have hshape : ∀ x y : F, Φ (x, y)
      = (f (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l)) - ‖x‖ ^ 2 / (2 * t) := by
    intro x y
    have hid := QuadShiftCompleteSquare t l ht hl y x
    rw [← had, ← hcd] at hid
    simp only [hΦd]
    show (f (toLp 2 (y, t + l)) - ‖y‖ ^ 2 / (2 * (t + l))) + -(a * ‖y - c • x‖ ^ 2) = _
    have hid' : -(a * ‖y - c • x‖ ^ 2)
        = ‖y‖ ^ 2 / (2 * (t + l)) - ‖y - x‖ ^ 2 / (2 * l) - ‖x‖ ^ 2 / (2 * t) := by
      rw [hid]; ring
    rw [hid']
    ring
  -- so the corrected envelope is an attained partial supremum of `Φ`
  refine PartialSupConcaveOfAttained Φ hΦ _ (fun x y => ?_) (fun x => ?_)
  · rw [hshape x y]
    have := hub x y
    linarith
  · obtain ⟨y, hy⟩ := hat x
    exact ⟨y, by rw [hshape x y, ← hy]⟩
