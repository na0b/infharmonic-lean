import InfHarmonic.Preamble
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 6 of Lemma 5.2: for each fixed slope the slope functional is an affine
function of the center, with the slope itself as linear part.  This is the
affine structure that makes the dual value an infimum of affine functions. -/
theorem BaryGammaAffineInCenter (f : WithLp 2 (F × ℝ) → ℝ) (s t : ℝ) (hs : 0 < s)
    (hbdd : ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A y}) :
    ∃ c : F → ℝ, ∀ A x : F,
      sSup {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)}
        = c A + inner ℝ A x := by
  -- Body-only acknowledgements (traps 2 and 3): `[FiniteDimensional ℝ F]` and `hs` are part
  -- of this node's protected signature.  The statement is purely formal in `f` and `s` and
  -- needs no dimension hypothesis, so neither is consumed; they are named here rather than
  -- by editing any line above `-- BODY`.
  have _ : FiniteDimensional ℝ F := inferInstance
  have _ := hs
  refine ⟨fun A => sSup {w : ℝ | ∃ y : F,
    w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A y}, ?_⟩
  intro A x
  -- C(A), the UNtranslated competitor set: nonempty with witness `y = 0`, and bounded
  -- above by `hbdd A` verbatim.  Both halves are established before `c A` is used as a
  -- least upper bound anywhere (pm-0026 ordering).
  have hCne : {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A y}.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  -- Pointwise, the conclusion's competitor is C(A)'s shifted by the CONSTANT ⟪A, x⟫.
  have hshift : ∀ y : F,
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - (inner ℝ A (y - x) : ℝ)
        = (f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - (inner ℝ A y : ℝ))
          + (inner ℝ A x : ℝ) := by
    intro y
    rw [inner_sub_right]
    ring
  have hGne : {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)}.Nonempty := ⟨_, ⟨0, rfl⟩⟩
  -- The shifted value `c A + ⟪A, x⟫` is an upper bound for the translated set; this is
  -- what makes that set bounded above, so that ITS supremum is a genuine lub too.
  have hGub : ∀ b ∈ {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)},
      b ≤ sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A y} + (inner ℝ A x : ℝ) := by
    rintro b ⟨y, rfl⟩
    rw [hshift y]
    have := le_csSup (hbdd A)
      (show f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - (inner ℝ A y : ℝ) ∈ _ from ⟨y, rfl⟩)
    linarith
  have hGbdd : BddAbove {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} :=
    ⟨_, fun b hb => hGub b hb⟩
  refine le_antisymm (csSup_le hGne hGub) ?_
  -- Reverse inequality: every element of C(A) is below `sSup G - ⟪A, x⟫`, because its
  -- shift lies in G and G is bounded above.  Leastness of `c A` then finishes.
  have hrev : sSup {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A y}
      ≤ sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)}
        - (inner ℝ A x : ℝ) := by
    refine csSup_le hCne ?_
    rintro b ⟨y, rfl⟩
    have h := le_csSup hGbdd
      (show f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - (inner ℝ A (y - x) : ℝ) ∈ _ from ⟨y, rfl⟩)
    rw [hshift y] at h
    linarith
  linarith
