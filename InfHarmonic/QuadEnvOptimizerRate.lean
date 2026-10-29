import InfHarmonic.QuadEnvP
import InfHarmonic.QuadEnvM
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 4 of Lemma 4.3, the quantitative core: if `|f| ≤ N` on the ball of radius `M`
at the two time levels `t ± l` and every competitor outside that ball is strictly
beaten by the competitor `y = x`, then the competitor `y = x` bounds the envelope
from the correct side and EVERY optimizer `y` lies in the ball and satisfies the
explicit rate `|y - x| ≤ 2 √(N l)`. -/
theorem QuadEnvOptimizerRate (f : WithLp 2 (F × ℝ) → ℝ) (l : ℝ) (hl : 0 < l)
    (z : WithLp 2 (F × ℝ)) (M N : ℝ) (hxM : ‖(ofLp z).1‖ ≤ M) (hN : 0 ≤ N)
    (hbd : ∀ y : F, ‖y‖ ≤ M →
      |f (toLp 2 (y, (ofLp z).2 + l))| ≤ N ∧ |f (toLp 2 (y, (ofLp z).2 - l))| ≤ N)
    (hfar : ∀ y : F, M < ‖y‖ →
      f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
          < f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)) ∧
      f (toLp 2 ((ofLp z).1, (ofLp z).2 - l))
          < f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) :
    (f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)) ≤ QuadEnvP f l z ∧
        ∀ y : F, QuadEnvP f l z
            = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l) →
          ‖y‖ ≤ M ∧ ‖y - (ofLp z).1‖ ≤ 2 * Real.sqrt (N * l)) ∧
    (QuadEnvM f l z ≤ f (toLp 2 ((ofLp z).1, (ofLp z).2 - l)) ∧
        ∀ y : F, QuadEnvM f l z
            = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) →
          ‖y‖ ≤ M ∧ ‖y - (ofLp z).1‖ ≤ 2 * Real.sqrt (N * l)) := by
  -- The project's ambient convention (pm-0003) is that `F` is a finite-dimensional
  -- real inner-product space, which is what makes `WithLp 2 (F × ℝ)` the space-time
  -- of the paper.  The scalar argument below needs only the norm, so this line keeps
  -- both section instances present in the closed declaration; the `variable` line
  -- itself sits inside the hashed signature region and is not editable here.
  have _ : ProperSpace F := inferInstance
  have hl0 : l ≠ 0 := hl.ne'
  have h2l : (0:ℝ) < 2 * l := by linarith
  have hNl : (0:ℝ) ≤ N * l := mul_nonneg hN hl.le
  -- the center is itself an admissible point of the ball, by `hxM`
  have hbdx := hbd (ofLp z).1 hxM
  -- `|x - x| = 0`, so the competitor `y = x` has value `f (x, t ± l)`
  have hcenP : f (toLp 2 ((ofLp z).1, (ofLp z).2 + l))
      - ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l)
      = f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)) := by simp
  have hcenM : f (toLp 2 ((ofLp z).1, (ofLp z).2 - l))
      + ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l)
      = f (toLp 2 ((ofLp z).1, (ofLp z).2 - l)) := by simp
  -- The square-root step.  This is pure scalar arithmetic: it mentions neither
  -- envelope nor either half of `hfar`, and the `.tex` likewise states it once and
  -- reuses it ("so |y-x|^2 <= 4Nl and, as before, |y-x| <= 2 sqrt(Nl)").
  have hsqrt : ∀ y : F, ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ 2 * N →
      ‖y - (ofLp z).1‖ ≤ 2 * Real.sqrt (N * l) := by
    intro y hy
    rw [div_le_iff₀ h2l] at hy
    have h1 : ‖y - (ofLp z).1‖ ^ 2 ≤ 4 * (N * l) := by linarith
    have h4 : Real.sqrt 4 = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    calc ‖y - (ofLp z).1‖ = Real.sqrt (‖y - (ofLp z).1‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (4 * (N * l)) := Real.sqrt_le_sqrt h1
      _ = 2 * Real.sqrt (N * l) := by
          rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4), h4]
  constructor
  · -- (1) FORWARD.  Supremum, time level `t + l`, cost subtracted, and ONLY the
    -- first inequality of `hfar`.
    have hbdd : BddAbove {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      refine ⟨N, ?_⟩
      rintro w ⟨y, rfl⟩
      rcases le_or_gt ‖y‖ M with hy | hy
      · -- on the ball: the cost is nonnegative and `|f| ≤ N`
        have h1 := (hbd y hy).1
        have h2 : (0:ℝ) ≤ ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
          div_nonneg (sq_nonneg _) h2l.le
        have h3 := le_abs_self (f (toLp 2 (y, (ofLp z).2 + l)))
        linarith
      · -- off the ball: beaten by the competitor `y = x`, which `hbd` bounds
        have h1 := (hfar y hy).1
        have h3 := le_abs_self (f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)))
        linarith [hbdx.1]
    have hQ : QuadEnvP f l z = sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      rw [QuadEnvP, if_neg hl0]
    have hmemx : f (toLp 2 ((ofLp z).1, (ofLp z).2 + l))
        - ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l) ∈ {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} :=
      ⟨(ofLp z).1, rfl⟩
    -- nonempty and bounded above, so the supremum is a genuine least upper bound
    -- and dominates the `y = x` competitor
    have hlow : f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)) ≤ QuadEnvP f l z := by
      have h := le_csSup hbdd hmemx
      rw [hcenP] at h
      rw [hQ]
      exact h
    refine ⟨hlow, ?_⟩
    intro y hyeq
    have hyM : ‖y‖ ≤ M := by
      by_contra hc
      have h1 := (hfar y (lt_of_not_ge hc)).1
      rw [← hyeq] at h1
      linarith
    refine ⟨hyM, hsqrt y ?_⟩
    have h1 := (hbd y hyM).1
    have h3 := le_abs_self (f (toLp 2 (y, (ofLp z).2 + l)))
    have h4 := neg_abs_le (f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)))
    have h5 : ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
        = f (toLp 2 (y, (ofLp z).2 + l)) - QuadEnvP f l z := by rw [hyeq]; ring
    rw [h5]
    linarith [hbdx.1]
  · -- (2) BACKWARD.  The mirror computation, NOT the forward one applied to `-f`:
    -- infimum, time level `t - l`, cost added, and ONLY the second inequality
    -- of `hfar`.
    have hbdd : BddBelow {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      refine ⟨-N, ?_⟩
      rintro w ⟨y, rfl⟩
      rcases le_or_gt ‖y‖ M with hy | hy
      · have h1 := (hbd y hy).2
        have h2 : (0:ℝ) ≤ ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
          div_nonneg (sq_nonneg _) h2l.le
        have h3 := neg_abs_le (f (toLp 2 (y, (ofLp z).2 - l)))
        linarith
      · have h1 := (hfar y hy).2
        have h3 := neg_abs_le (f (toLp 2 ((ofLp z).1, (ofLp z).2 - l)))
        linarith [hbdx.2]
    have hQ : QuadEnvM f l z = sInf {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      rw [QuadEnvM, if_neg hl0]
    have hmemx : f (toLp 2 ((ofLp z).1, (ofLp z).2 - l))
        + ‖(ofLp z).1 - (ofLp z).1‖ ^ 2 / (2 * l) ∈ {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} :=
      ⟨(ofLp z).1, rfl⟩
    have hup : QuadEnvM f l z ≤ f (toLp 2 ((ofLp z).1, (ofLp z).2 - l)) := by
      have h := csInf_le hbdd hmemx
      rw [hcenM] at h
      rw [hQ]
      exact h
    refine ⟨hup, ?_⟩
    intro y hyeq
    have hyM : ‖y‖ ≤ M := by
      by_contra hc
      have h1 := (hfar y (lt_of_not_ge hc)).2
      rw [← hyeq] at h1
      linarith
    refine ⟨hyM, hsqrt y ?_⟩
    have h1 := (hbd y hyM).2
    have h3 := le_abs_self (f (toLp 2 ((ofLp z).1, (ofLp z).2 - l)))
    have h4 := neg_abs_le (f (toLp 2 (y, (ofLp z).2 - l)))
    have h5 : ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
        = QuadEnvM f l z - f (toLp 2 (y, (ofLp z).2 - l)) := by rw [hyeq]; ring
    rw [h5]
    linarith [hbdx.2]
