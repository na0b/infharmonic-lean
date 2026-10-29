import InfHarmonic.SubquadraticGrowth
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 1 of Lemma 4.3, the localization lemma: subquadratic spatial growth and
the quadratic cost produce one radius `M` and one bound `N` such that `|f| ≤ N` on
the box of radius `M` over `J`, and such that every spatial competitor outside the
ball of radius `M` is strictly beaten by the competitor `y = x` in both the forward
(maximizing) and the backward (minimizing) problem, uniformly for centers in the
ball of radius `R₀`, times in `J` and lengths in `(0, l₀]`. -/
theorem QuadEnvFarCompetitors (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f)
    (R₀ : ℝ) (hR₀ : 0 ≤ R₀) (J : Set ℝ) (hJI : J ⊆ I) (hJne : J.Nonempty) (hJc : IsCompact J)
    (l₀ : ℝ) (hl₀ : 0 < l₀) :
    ∃ M N : ℝ, max R₀ 1 ≤ M ∧
      (∀ (y : F) (s : ℝ), ‖y‖ ≤ M → s ∈ J → |f (toLp 2 (y, s))| ≤ N) ∧
      ∀ (x y : F) (s l : ℝ), ‖x‖ ≤ R₀ → s ∈ J → 0 < l → l ≤ l₀ → M < ‖y‖ →
        f (toLp 2 (y, s)) - ‖y - x‖ ^ 2 / (2 * l) < f (toLp 2 (x, s)) ∧
        f (toLp 2 (x, s)) < f (toLp 2 (y, s)) + ‖y - x‖ ^ 2 / (2 * l) := by
  have hR₀' : (0:ℝ) ≤ R₀ := hR₀
  -- The growth radius: `SubquadraticGrowth` at `ε = 1 / (8 l₀)`.
  obtain ⟨M₀, hM₀pos, hM₀⟩ := hgrow J hJI hJc (1 / (8 * l₀)) (by positivity)
  obtain ⟨M₁, hM₁def⟩ : ∃ M₁ : ℝ, M₁ = max (max M₀ (4 * R₀)) 1 := ⟨_, rfl⟩
  have hM₁M₀ : M₀ ≤ M₁ := by rw [hM₁def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hM₁R₀ : 4 * R₀ ≤ M₁ := by rw [hM₁def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hM₁one : (1:ℝ) ≤ M₁ := by rw [hM₁def]; exact le_max_right _ _
  -- `|f|` attains a finite maximum on the space-time box of radius `r` over `J`:
  -- that box is a compact subset of the time-preimage of `I`, where `f` is continuous.
  have hbox : ∀ r : ℝ, 0 ≤ r → ∃ Nr : ℝ, 0 ≤ Nr ∧
      ∀ (y : F) (s : ℝ), ‖y‖ ≤ r → s ∈ J → |f (toLp 2 (y, s))| ≤ Nr := by
    intro r hr
    obtain ⟨K, hKdef⟩ : ∃ K : Set (WithLp 2 (F × ℝ)),
        K = (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) '' (closedBall (0 : F) r ×ˢ J) :=
      ⟨_, rfl⟩
    have hKc : IsCompact K := by
      rw [hKdef]
      exact ((isCompact_closedBall _ _).prod hJc).image (by fun_prop)
    have hKsub : K ⊆ (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) ⁻¹' I := by
      rw [hKdef]
      rintro w ⟨p, hp, rfl⟩
      exact hJI hp.2
    have hKmem : ∀ (y : F) (s : ℝ), ‖y‖ ≤ r → s ∈ J →
        (toLp 2 (y, s) : WithLp 2 (F × ℝ)) ∈ K := by
      intro y s hy hs
      rw [hKdef]
      exact ⟨(y, s), ⟨mem_closedBall_zero_iff.mpr hy, hs⟩, rfl⟩
    obtain ⟨s₀, hs₀⟩ := hJne
    obtain ⟨w, -, hwmax⟩ :=
      hKc.exists_isMaxOn ⟨_, hKmem 0 s₀ (by simpa using hr) hs₀⟩ (hcont.mono hKsub).abs
    exact ⟨|f w|, abs_nonneg _, fun y s hy hs => hwmax (hKmem y s hy hs)⟩
  obtain ⟨N₁, hN₁0, hN₁⟩ := hbox M₁ (by linarith)
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M₁ (Real.sqrt (32 / 5 * N₁ * l₀) + 1) := ⟨_, rfl⟩
  have hMM₁ : M₁ ≤ M := by rw [hMdef]; exact le_max_left _ _
  have hMsq : Real.sqrt (32 / 5 * N₁ * l₀) + 1 ≤ M := by rw [hMdef]; exact le_max_right _ _
  obtain ⟨N, -, hN⟩ := hbox M (by linarith)
  refine ⟨M, N, max_le (by linarith) (by linarith), hN, ?_⟩
  intro x y s l hx hs hl hll₀ hyM
  have hy0 : (0:ℝ) < ‖y‖ := by linarith
  have h2l : (0:ℝ) < 2 * l := by linarith
  have hA0 : (0:ℝ) ≤ ‖y‖ ^ 2 := sq_nonneg _
  -- (a) the growth bound at `(y,s)`, cleared of denominators and then one-sided
  have hgrow8 : 8 * l * |f (toLp 2 (y, s))| ≤ ‖y‖ ^ 2 := by
    have hM₀y : M₀ ≤ ‖y‖ := by linarith
    have h1 : |f (toLp 2 (y, s))| ≤ 1 / (8 * l₀) * ‖y‖ ^ 2 := hM₀ (toLp 2 (y, s)) hM₀y hs
    have h2 : 8 * l₀ * |f (toLp 2 (y, s))| ≤ ‖y‖ ^ 2 := by
      calc 8 * l₀ * |f (toLp 2 (y, s))|
          ≤ 8 * l₀ * (1 / (8 * l₀) * ‖y‖ ^ 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = ‖y‖ ^ 2 := by field_simp
    nlinarith [mul_nonneg (abs_nonneg (f (toLp 2 (y, s)))) (sub_nonneg.mpr hll₀)]
  have hgyu : 8 * l * f (toLp 2 (y, s)) ≤ ‖y‖ ^ 2 := by
    have := mul_nonneg hl.le (sub_nonneg.mpr (le_abs_self (f (toLp 2 (y, s)))))
    nlinarith [hgrow8, this]
  have hgyl : -(‖y‖ ^ 2) ≤ 8 * l * f (toLp 2 (y, s)) := by
    have := mul_nonneg hl.le (by linarith [neg_abs_le (f (toLp 2 (y, s)))] :
      (0:ℝ) ≤ |f (toLp 2 (y, s))| + f (toLp 2 (y, s)))
    nlinarith [hgrow8, this]
  -- (b) the far competitor pays strictly more than `9 |y|² / 16`
  have hfarsq : 9 / 16 * ‖y‖ ^ 2 < ‖y - x‖ ^ 2 := by
    have h1 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le _ _
    have h2 : 3 / 4 * ‖y‖ < ‖y - x‖ := by linarith
    nlinarith [mul_pos (sub_pos.mpr h2)
      (by linarith [norm_nonneg (y - x)] : (0:ℝ) < ‖y - x‖ + 3 / 4 * ‖y‖)]
  -- (c) the choice of `M` pushes `|y|²` past `(32/5) N₁ l`
  have hN₁sq : 32 * N₁ * l < 5 * ‖y‖ ^ 2 := by
    have hS0 : (0:ℝ) ≤ 32 / 5 * N₁ * l₀ := by positivity
    have h1 : Real.sqrt (32 / 5 * N₁ * l₀) < ‖y‖ := by linarith
    have h2 : 32 / 5 * N₁ * l₀ < ‖y‖ ^ 2 := by
      nlinarith [Real.sq_sqrt hS0, Real.sqrt_nonneg (32 / 5 * N₁ * l₀),
        mul_pos (sub_pos.mpr h1)
          (by linarith [Real.sqrt_nonneg (32 / 5 * N₁ * l₀)] :
            (0:ℝ) < ‖y‖ + Real.sqrt (32 / 5 * N₁ * l₀))]
    nlinarith [mul_le_mul_of_nonneg_left hll₀ (by positivity : (0:ℝ) ≤ 32 * N₁)]
  -- (d) the center value is controlled by `N₁`
  have hfx : -N₁ ≤ f (toLp 2 (x, s)) ∧ f (toLp 2 (x, s)) ≤ N₁ :=
    abs_le.mp (hN₁ x s (by linarith [hR₀']) hs)
  have hlo := mul_le_mul_of_nonneg_left hfx.1 h2l.le
  have hup := mul_le_mul_of_nonneg_left hfx.2 h2l.le
  constructor
  · have key : (f (toLp 2 (y, s)) - f (toLp 2 (x, s))) * (2 * l) < ‖y - x‖ ^ 2 := by
      nlinarith [hgyu, hlo, hfarsq, hN₁sq]
    have h := (lt_div_iff₀ h2l).mpr key
    linarith
  · have key : (f (toLp 2 (x, s)) - f (toLp 2 (y, s))) * (2 * l) < ‖y - x‖ ^ 2 := by
      nlinarith [hgyl, hup, hfarsq, hN₁sq]
    have h := (lt_div_iff₀ h2l).mpr key
    linarith
