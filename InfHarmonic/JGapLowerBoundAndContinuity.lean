import InfHarmonic.EnvelopeCompetitorBounds
import InfHarmonic.QuadEnvAttained
import InfHarmonic.UniformSubquadratic
import InfHarmonic.JGap
import InfHarmonic.ContactEnv
open Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The two regularity facts about the one-step gap `J_ε` of \noderef{JGap} that the
walk estimates of paper Proposition 6.7 need: a lower bound on a space-time box,
and the continuity of the gap after the time coordinate has been retracted away
from `0`.

Let `v` be a member of the fit class `A_{m,C₀}` centered at `(0,1)`, let
`W = ContactEnv v κ` be continuous and of subquadratic spatial growth on
positive times, and let `Rb`, `Tb`, `d`, `ε` be scales with `0 ≤ Rb`,
`0 ≤ Tb`, `0 < d ≤ 1/2` and `0 < ε ≤ d/4`. Then there is a constant
`Lam0 ≥ 0`, depending on all of these, such that

* `-Lam0 ≤ J_ε(w)` whenever the space coordinate of `w` has norm at most `Rb`
  and its time coordinate lies in `[d - ε, Tb + ε]`; and
* `w ↦ J_ε(x_w, max t_w (d/2))` is continuous on all of space-time.

The bound is one constant for the whole box: `Lam0 = (K_W + K_v) / (2ε)`, where
`K_W` and `K_v` bound `W` and `v` on the compact box
`closedBall 0 Rb ×ˢ [d/2, Tb + 1]`, which contains every competitor point
`(x_w, t_w ± ε)` used by `J_ε` --- this is where `ε ≤ d/4` and `d ≤ 1/2` are
spent. The retraction `t ↦ max t (d/2)` keeps the time positive, so the
continuity of the two quadratic envelopes applies at every point and the
composite is continuous without any hypothesis on `w`.

The walk itself, its filtration and the probability space play no part in
either statement. -/
theorem JGapLowerBoundAndContinuity (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ))
    (Rb Tb d ε : ℝ) (hR0 : (0 : ℝ) ≤ Rb) (hT0 : (0 : ℝ) ≤ Tb) (hd0 : 0 < d)
    (hdle : d ≤ 1 / 2) (hε0 : 0 < ε) (hεd : ε ≤ d / 4) :
    ∃ Lam0 : ℝ, 0 ≤ Lam0 ∧
      (∀ w : WithLp 2 (F × ℝ), ‖(ofLp w).1‖ ≤ Rb → d - ε ≤ (ofLp w).2 →
        (ofLp w).2 ≤ Tb + ε → -Lam0 ≤ JGap v κ ε w) ∧
      Continuous (fun w : WithLp 2 (F × ℝ) =>
        JGap v κ ε (toLp 2 ((ofLp w).1, max (ofLp w).2 (d / 2)))) := by
  -- ## the lower bound for `J_ε` on the box
  set Jt : Set ℝ := Set.Icc (d / 2) (Tb + 1) with hJt
  have hJtc : IsCompact Jt := by rw [hJt]; exact isCompact_Icc
  have hJtpos : ∀ s ∈ Jt, 0 < s := by
    intro s hs
    rw [hJt] at hs
    have h1 := hs.1
    linarith only [h1, hd0]
  have hboxc : IsCompact ((fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
      (Metric.closedBall (0 : F) Rb ×ˢ Jt)) := by
    refine IsCompact.image ((isCompact_closedBall (0 : F) Rb).prod hJtc) ?_
    exact WithLp.prod_continuous_toLp 2 F ℝ
  have hboxmem : ∀ (y : F) (s : ℝ), ‖y‖ ≤ Rb → s ∈ Jt →
      (toLp 2 (y, s) : WithLp 2 (F × ℝ))
        ∈ (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
            (Metric.closedBall (0 : F) Rb ×ˢ Jt) :=
    fun y s hy hs => ⟨(y, s), ⟨by simpa using hy, hs⟩, rfl⟩
  have hvcontOn : ContinuousOn v (Set.univ : Set (WithLp 2 (F × ℝ))) := hv.1.1.2.1
  obtain ⟨Kw, hKw⟩ := hboxc.exists_bound_of_continuousOn (hWcont.mono (by
    rintro _ ⟨⟨y, s⟩, ⟨-, hs⟩, rfl⟩
    exact hJtpos s hs))
  obtain ⟨Kv, hKv⟩ := hboxc.exists_bound_of_continuousOn (hvcontOn.mono (Set.subset_univ _))
  set Lam0 : ℝ := (Kw + Kv) / (2 * ε) with hLam0
  have hboxne : (d / 2) ∈ Jt := by
    rw [hJt]
    constructor
    · exact le_rfl
    · linarith only [hdle, hT0]
  have hKw0 : (0 : ℝ) ≤ Kw :=
    le_trans (norm_nonneg _) (hKw _ (hboxmem 0 (d / 2) (by simp; linarith only [hR0]) hboxne))
  have hKv0 : (0 : ℝ) ≤ Kv :=
    le_trans (norm_nonneg _) (hKv _ (hboxmem 0 (d / 2) (by simp; linarith only [hR0]) hboxne))
  have hLam00 : (0 : ℝ) ≤ Lam0 := by
    rw [hLam0]
    exact div_nonneg (by linarith only [hKw0, hKv0]) (by linarith only [hε0])
  have hJlow : ∀ w : WithLp 2 (F × ℝ), ‖(ofLp w).1‖ ≤ Rb → d - ε ≤ (ofLp w).2 →
      (ofLp w).2 ≤ Tb + ε → -Lam0 ≤ JGap v κ ε w := by
    intro w hxn htn1 htn2
    have htn : d - ε ≤ (ofLp w).2 ∧ (ofLp w).2 ≤ Tb + ε := ⟨htn1, htn2⟩
    have hwpos : 0 < (ofLp w).2 := by linarith only [htn.1, hd0, hεd]
    have hplus : (ofLp w).2 + ε ∈ Jt := by
      rw [hJt]
      constructor
      · linarith only [htn.1, hd0]
      · linarith only [htn.2, hεd, hdle]
    have hminus : (ofLp w).2 - ε ∈ Jt := by
      rw [hJt]
      constructor
      · linarith only [htn.1, hεd]
      · linarith only [htn.2]
    -- the two competitor bounds at the center `x_n`
    have hPlow : ContactEnv v κ (toLp 2 ((ofLp w).1, (ofLp w).2 + ε))
        ≤ QuadEnvP (ContactEnv v κ) ε w := by
      have h1 := ((EnvelopeCompetitorBounds (Set.Ioi (0 : ℝ)) (ContactEnv v κ) hWcont hWgrow).1
        ε w hε0 (by exact hwpos) (by
          simp only [Set.mem_Ioi]
          linarith only [hwpos, hε0])).1 (ofLp w).1
      have hz0' : ‖(ofLp w).1 - (ofLp w).1‖ ^ 2 / (2 * ε) = 0 := by
        rw [sub_self, norm_zero]
        simp
      rw [hz0', sub_zero] at h1
      exact h1
    have hMup : QuadEnvM v ε w
        ≤ v (toLp 2 ((ofLp w).1, (ofLp w).2 - ε)) := by
      have h1 := ((EnvelopeCompetitorBounds (Set.univ : Set ℝ) v
        (by simpa using hvcontOn) (by
          intro Jc _ hJc e he
          obtain ⟨M, hM0, hMb⟩ := UniformSubquadratic (F := F) C₀ hC₀
            (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) Jc hJc e he
          exact ⟨M, hM0, fun w hw hs => hMb v hv hcent w hw hs⟩)).2.1
        ε w hε0 (Set.mem_univ _) (Set.mem_univ _)).1 (ofLp w).1
      have hz0' : ‖(ofLp w).1 - (ofLp w).1‖ ^ 2 / (2 * ε) = 0 := by
        rw [sub_self, norm_zero]
        simp
      rw [hz0', add_zero] at h1
      exact h1
    have hWb : |ContactEnv v κ (toLp 2 ((ofLp w).1, (ofLp w).2 + ε))| ≤ Kw := by
      have h1 := hKw _ (hboxmem _ _ hxn hplus)
      rwa [Real.norm_eq_abs] at h1
    have hvb : |v (toLp 2 ((ofLp w).1, (ofLp w).2 - ε))| ≤ Kv := by
      have h1 := hKv _ (hboxmem _ _ hxn hminus)
      rwa [Real.norm_eq_abs] at h1
    have habsW := abs_le.mp hWb
    have habsv := abs_le.mp hvb
    rw [JGap, hLam0, neg_le, ← neg_div, div_le_div_iff_of_pos_right (by linarith only [hε0] : (0:ℝ) < 2 * ε)]
    linarith only [hPlow, hMup, habsW.1, habsv.2]
  -- ## `J_ε` is continuous where the time is positive, hence measurable along the walk
  have hc1 : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).1) := by fun_prop
  have hc2 : Continuous (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) := by fun_prop
  have hvgrowu : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro Jc _ hJc e he
    obtain ⟨M, hM0, hMb⟩ := UniformSubquadratic (F := F) C₀ hC₀
      (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) Jc hJc e he
    exact ⟨M, hM0, fun w hw hs => hMb v hv hcent w hw hs⟩
  have hQEA_W := QuadEnvAttained (Set.Ioi (0 : ℝ)) isOpen_Ioi (ContactEnv v κ) hWcont hWgrow
  have hQEA_v := QuadEnvAttained (Set.univ : Set ℝ) isOpen_univ v (by simpa using hvcontOn) hvgrowu
  have hJca : ∀ w : WithLp 2 (F × ℝ), 0 < (ofLp w).2 →
      ContinuousAt (fun w' : WithLp 2 (F × ℝ) => JGap v κ ε w') w := by
    intro w hw
    have hpair : ContinuousAt (fun w' : WithLp 2 (F × ℝ) => (ε, w')) w := by fun_prop
    have hP : ContinuousAt (fun w' : WithLp 2 (F × ℝ) => QuadEnvP (ContactEnv v κ) ε w') w :=
      (hQEA_W.2.2.1 ε hε0 w hw (by simp only [Set.mem_Ioi]; linarith only [hw, hε0])).comp hpair
    have hM : ContinuousAt (fun w' : WithLp 2 (F × ℝ) => QuadEnvM v ε w') w :=
      (hQEA_v.2.2.2.1 ε hε0 w (Set.mem_univ _) (Set.mem_univ _)).comp hpair
    have : ContinuousAt (fun w' : WithLp 2 (F × ℝ) =>
        (QuadEnvP (ContactEnv v κ) ε w' - QuadEnvM v ε w') / (2 * ε)) w := (hP.sub hM).div_const _
    exact this
  have hretr : Continuous (fun w : WithLp 2 (F × ℝ) =>
      (toLp 2 ((ofLp w).1, max (ofLp w).2 (d / 2)) : WithLp 2 (F × ℝ))) := by
    refine (WithLp.prod_continuous_toLp 2 F ℝ).comp ?_
    exact hc1.prodMk (hc2.max continuous_const)
  have hJretr : Continuous (fun w : WithLp 2 (F × ℝ) =>
      JGap v κ ε (toLp 2 ((ofLp w).1, max (ofLp w).2 (d / 2)))) := by
    rw [continuous_iff_continuousAt]
    intro w
    have hpos : 0 < (ofLp (toLp 2 ((ofLp w).1, max (ofLp w).2 (d / 2))
        : WithLp 2 (F × ℝ))).2 := by
      have h1 : (ofLp (toLp 2 ((ofLp w).1, max (ofLp w).2 (d / 2))
          : WithLp 2 (F × ℝ))).2 = max (ofLp w).2 (d / 2) := by simp
      rw [h1]
      have h2 : d / 2 ≤ max (ofLp w).2 (d / 2) := le_max_right _ _
      linarith only [h2, hd0]
    exact ContinuousAt.comp (g := fun w' : WithLp 2 (F × ℝ) => JGap v κ ε w')
      (f := fun w' : WithLp 2 (F × ℝ) =>
        (toLp 2 ((ofLp w').1, max (ofLp w').2 (d / 2)) : WithLp 2 (F × ℝ)))
      (hJca _ hpos) hretr.continuousAt
  exact ⟨Lam0, hLam00, hJlow, hJretr⟩
