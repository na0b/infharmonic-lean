import InfHarmonic.Preamble
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 3 of paper Proposition 2.6, the maximization step, in the form the
penalized three-point functional needs it.

Let `Φ` be a functional of triples of points of the closed ball of radius `3/4`
which is continuous on the constrained set `K` of triples whose first two
entries are separated by at least `β / (2 C')`. Suppose `Φ` reaches the positive
level `β` at one admissible triple, and that off the small-separation region it
obeys the paper's upper bound `Φ x y z ≤ ‖x - y‖ * C'`. Then `Φ` attains a
maximum over `K` at a triple `(x, y, z)` which still has `Φ x y z ≥ β`, whose
first two entries are distinct, and whose separation satisfies the *strictly
better* lower bound `β / C' ≤ ‖x - y‖` --- twice the radius that defines `K`,
so the maximizer is strictly inside the constraint and the maximum is a genuine
local maximum of `Φ`. The ambient space is an arbitrary finite-dimensional real
inner-product space `E`; finite-dimensionality is what makes the closed balls
compact. -/
theorem ConstrainedThreePointMaximizer (Φ : E → E → E → ℝ) (xk yk zk : E) (β C' : ℝ)
    (hβ : 0 < β) (hC'pos : 0 < C')
    (hxk : xk ∈ closedBall (0 : E) (3 / 4)) (hyk : yk ∈ closedBall (0 : E) (3 / 4))
    (hzk : zk ∈ closedBall (0 : E) (3 / 4))
    (hlowk : β / (2 * C') ≤ ‖xk - yk‖)
    (hΦk : β ≤ Φ xk yk zk)
    (hcont : ContinuousOn (fun P : E × E × E => Φ P.1 P.2.1 P.2.2)
      ((closedBall (0 : E) (3 / 4) ×ˢ
          (closedBall (0 : E) (3 / 4) ×ˢ closedBall (0 : E) (3 / 4)))
        ∩ {P : E × E × E | β / (2 * C') ≤ ‖P.1 - P.2.1‖}))
    (hub : ∀ x y z : E, x ∈ closedBall (0 : E) (3 / 4) →
      y ∈ closedBall (0 : E) (3 / 4) → z ∈ closedBall (0 : E) (3 / 4) → x ≠ y →
      Φ x y z ≤ ‖x - y‖ * C') :
    ∃ x y z : E, x ∈ closedBall (0 : E) (3 / 4) ∧ y ∈ closedBall (0 : E) (3 / 4)
      ∧ z ∈ closedBall (0 : E) (3 / 4) ∧ x ≠ y
      ∧ β ≤ Φ x y z
      ∧ (∀ x' y' z' : E, x' ∈ closedBall (0 : E) (3 / 4) →
          y' ∈ closedBall (0 : E) (3 / 4) → z' ∈ closedBall (0 : E) (3 / 4) →
          β / (2 * C') ≤ ‖x' - y'‖ → Φ x' y' z' ≤ Φ x y z)
      ∧ β / C' ≤ ‖x - y‖ := by
  classical
  -- the constrained set, in `E × E × E`: compactness and continuity are topological, so
  -- the product norm is irrelevant here.
  obtain ⟨S, hS⟩ : ∃ S : Set (E × E × E), S =
      (closedBall (0 : E) (3 / 4) ×ˢ
        (closedBall (0 : E) (3 / 4) ×ˢ closedBall (0 : E) (3 / 4)))
      ∩ {P : E × E × E | β / (2 * C') ≤ ‖P.1 - P.2.1‖} := ⟨_, rfl⟩
  have hlowpos : 0 < β / (2 * C') := div_pos hβ (by linarith only [hC'pos])
  have hScpt : IsCompact S := by
    rw [hS]
    exact ((isCompact_closedBall _ _).prod
      ((isCompact_closedBall _ _).prod (isCompact_closedBall _ _))).inter_right
      (isClosed_le continuous_const (by fun_prop))
  have hSmem : ∀ P ∈ S, P.1 ∈ closedBall (0 : E) (3 / 4) ∧
      P.2.1 ∈ closedBall (0 : E) (3 / 4) ∧ P.2.2 ∈ closedBall (0 : E) (3 / 4) ∧
      β / (2 * C') ≤ ‖P.1 - P.2.1‖ := by
    intro P hP
    rw [hS] at hP
    exact ⟨hP.1.1, hP.1.2.1, hP.1.2.2, hP.2⟩
  -- the admissible triple of the hypotheses lies in the constrained set
  have hkS : (xk, yk, zk) ∈ S := by
    rw [hS]; exact ⟨⟨hxk, hyk, hzk⟩, hlowk⟩
  have hSne : S.Nonempty := ⟨_, hkS⟩
  have hFcont : ContinuousOn (fun P : E × E × E => Φ P.1 P.2.1 P.2.2) S := by
    rw [hS]; exact hcont
  -- the maximum is attained
  obtain ⟨P, hPS, hPmax⟩ := hScpt.exists_isMaxOn hSne hFcont
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hSmem P hPS
  have hmaxge : β ≤ Φ P.1 P.2.1 P.2.2 := le_trans hΦk (hPmax hkS)
  have hne : P.1 ≠ P.2.1 := by
    intro hcon
    rw [hcon, sub_self, norm_zero] at hP4
    linarith only [hP4, hlowpos]
  -- the maximizer is strictly inside the constraint
  have hrlow : β / C' ≤ ‖P.1 - P.2.1‖ := by
    have hub' := hub P.1 P.2.1 P.2.2 hP1 hP2 hP3 hne
    rw [div_le_iff₀ hC'pos]
    linarith only [hmaxge, hub']
  refine ⟨P.1, P.2.1, P.2.2, hP1, hP2, hP3, hne, hmaxge, ?_, hrlow⟩
  intro x' y' z' hx' hy' hz' hlow'
  exact hPmax (show (x', y', z') ∈ S from by rw [hS]; exact ⟨⟨hx', hy', hz'⟩, hlow'⟩)
