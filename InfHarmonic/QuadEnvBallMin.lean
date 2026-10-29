module

public import InfHarmonic.QuadEnvM

@[expose] public section
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 2 of Lemma 4.3, backward direction, as a localized reduction: once every
competitor outside the ball of radius `M` is strictly beaten by the competitor
`y = x`, the backward envelope is the minimum of the competitor function over the
fixed closed ball of radius `M`, and that minimum is attained inside the ball. -/
theorem QuadEnvBallMin (f : WithLp 2 (F × ℝ) → ℝ) (l : ℝ) (hl : 0 < l)
    (z : WithLp 2 (F × ℝ)) (M : ℝ) (hxM : ‖(ofLp z).1‖ ≤ M)
    (hfc : ContinuousOn (fun y : F => f (toLp 2 (y, (ofLp z).2 - l))) (closedBall (0 : F) M))
    (hfar : ∀ y : F, M < ‖y‖ →
      f (toLp 2 ((ofLp z).1, (ofLp z).2 - l))
        < f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) :
    QuadEnvM f l z = sInf ((fun y : F =>
        f (toLp 2 (y, (ofLp z).2 - l))
          + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) '' closedBall (0 : F) M) ∧
      ∃ y : F, ‖y‖ ≤ M ∧
        QuadEnvM f l z = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) := by
  have hl0 : l ≠ 0 := hl.ne'
  have hBc : IsCompact (closedBall (0 : F) M) := isCompact_closedBall _ _
  have hxB : (ofLp z).1 ∈ closedBall (0 : F) M := mem_closedBall_zero_iff.mpr hxM
  have hGc : ContinuousOn (fun y : F =>
      f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l))
      (closedBall (0 : F) M) := hfc.add (by fun_prop : Continuous (fun y : F =>
        ‖y - (ofLp z).1‖ ^ 2 / (2 * l))).continuousOn
  -- Weierstrass on the ball: a minimizer `y₀` together with the bound on the ball
  obtain ⟨y₀, hy₀B, hy₀inf, hy₀le⟩ := hBc.exists_sInf_image_eq_and_le ⟨_, hxB⟩ hGc
  have hy₀M : ‖y₀‖ ≤ M := mem_closedBall_zero_iff.mp hy₀B
  -- the competitor `y = x` has value `f (x, t - l)`
  have hcen : f (toLp 2 ((ofLp z).1, (ofLp z).2 - l))
      + ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l)
      = f (toLp 2 ((ofLp z).1, (ofLp z).2 - l)) := by simp
  -- the ball minimum is dominated by every competitor in `F`, so it is the least
  -- element of the competitor set of `QuadEnvM`; in particular that set is
  -- nonempty and bounded below, which is what licenses the infimum
  have hleast : IsLeast {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}
      (f (toLp 2 (y₀, (ofLp z).2 - l)) + ‖y₀ - (ofLp z).1‖ ^ 2 / (2 * l)) := by
    refine ⟨⟨y₀, rfl⟩, ?_⟩
    rintro w ⟨y, rfl⟩
    rcases le_or_gt ‖y‖ M with hy | hy
    · exact hy₀le y (mem_closedBall_zero_iff.mpr hy)
    · have h1 := hfar y hy
      have h2 := hy₀le (ofLp z).1 hxB
      rw [hcen] at h2
      linarith
  have hQ : QuadEnvM f l z
      = f (toLp 2 (y₀, (ofLp z).2 - l)) + ‖y₀ - (ofLp z).1‖ ^ 2 / (2 * l) := by
    rw [QuadEnvM, if_neg hl0]
    exact hleast.csInf_eq
  exact ⟨hQ.trans hy₀inf.symm, y₀, hy₀M, hQ⟩
