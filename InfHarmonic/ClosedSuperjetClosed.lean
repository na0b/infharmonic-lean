import InfHarmonic.ClosedSuperjet
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Part I(D) of the theorem of sums: the closed superjet is a closed subset of
the space of jets, so it absorbs limits of its own elements. -/
theorem ClosedSuperjetClosed (f : E → ℝ) (z : E) :
    IsClosed (ClosedSuperjet f z) := by
  -- `E × 𝓑(E)` is a product of metric spaces, hence a sequential space, so sequential
  -- closedness suffices -- the reduction the .tex opens with.
  refine IsSeqClosed.isClosed ?_
  intro q Q hq hQ
  -- the two component limits of `q → Q`
  have hQ1 : Tendsto (fun m => (q m).1) atTop (𝓝 Q.1) := (continuous_fst.tendsto Q).comp hQ
  have hQ2 : Tendsto (fun m => (q m).2) atTop (𝓝 Q.2) := (continuous_snd.tendsto Q).comp hQ
  -- unpack the defining sequences of each `q m`
  simp only [ClosedSuperjet, Set.mem_ofPred_eq] at hq
  choose zs ps Xs hjet hz hfz hp hX using hq
  -- EVERY LIMIT BELOW IS RUN THROUGH `dist` AND `Metric.tendsto_atTop`, NEVER THROUGH
  -- `squeeze_zero_norm` OR `tendsto_sub_nhds_zero_iff`.  On the operator space
  -- `E →L[ℝ] E →L[ℝ] ℝ` the zero element has two instance paths -- `ContinuousLinearMap.zero`
  -- and the one `SubtractionMonoid` hands to those two lemmas -- and reconciling them sends the
  -- unifier into a `whnf` timeout.  `dist` has no such split, and `Metric.tendsto_atTop` goes
  -- both ways on this space in under a second.
  -- THE DIAGONAL CHOICE.  Each of the four convergences holds for all large `k`, so the
  -- conjunction of the four `Eventually`s is itself eventually true and has a witness; that
  -- witness is an index past all four thresholds at once.  The extraction is legitimate
  -- precisely because the two targets `z` and `f z` do not depend on `m`.
  have hdiag : ∀ m : ℕ, ∃ k : ℕ,
      dist (zs m k) z < 1 / ((m : ℝ) + 1) ∧
      dist (f (zs m k)) (f z) < 1 / ((m : ℝ) + 1) ∧
      dist (ps m k) ((q m).1) < 1 / ((m : ℝ) + 1) ∧
      dist (Xs m k) ((q m).2) < 1 / ((m : ℝ) + 1) := by
    intro m
    have hm : (0:ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have e1 : ∀ᶠ k in atTop, zs m k ∈ Metric.ball z (1 / ((m : ℝ) + 1)) :=
      hz m (Metric.ball_mem_nhds z hm)
    have e2 : ∀ᶠ k in atTop, f (zs m k) ∈ Metric.ball (f z) (1 / ((m : ℝ) + 1)) :=
      hfz m (Metric.ball_mem_nhds (f z) hm)
    have e3 : ∀ᶠ k in atTop, ps m k ∈ Metric.ball ((q m).1) (1 / ((m : ℝ) + 1)) :=
      hp m (Metric.ball_mem_nhds ((q m).1) hm)
    have e4 : ∀ᶠ k in atTop, Xs m k ∈ Metric.ball ((q m).2) (1 / ((m : ℝ) + 1)) :=
      hX m (Metric.ball_mem_nhds ((q m).2) hm)
    exact (e1.and (e2.and (e3.and e4))).exists
  choose kk hk1 hk2 hk3 hk4 using hdiag
  -- the rate `1/(m+1)` eventually undercuts any `ε > 0`
  have hrateN : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, 1 / ((m : ℝ) + 1) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
    refine ⟨N, fun m hm => ?_⟩
    have h1 : (N : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hm
    have h2 : 1 / ε < (m : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hε] at h2
    rw [div_lt_iff₀ (by positivity : (0:ℝ) < (m : ℝ) + 1)]
    linarith
  -- the two limits whose target does not move with `m`
  have hζ : Tendsto (fun m => zs m (kk m)) atTop (𝓝 z) := by
    refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hrateN ε hε
    exact ⟨N, fun m hm => lt_trans (hk1 m) (hN m hm)⟩
  have hfζ : Tendsto (fun m => f (zs m (kk m))) atTop (𝓝 (f z)) := by
    refine Metric.tendsto_atTop.mpr (fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hrateN ε hε
    exact ⟨N, fun m hm => lt_trans (hk2 m) (hN m hm)⟩
  -- name the term: `Metric.tendsto_atTop.mp` applied inline leaves the index type a
  -- metavariable and the `SemilatticeSup` instance gets stuck, so read both rates off first
  have hQ1' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, dist ((q n).1) Q.1 < ε :=
    Metric.tendsto_atTop.mp hQ1
  have hQ2' : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, dist ((q n).2) Q.2 < ε :=
    Metric.tendsto_atTop.mp hQ2
  -- and the two triangle inequalities of the .tex: `1/m` plus a term that vanishes by `q → Q`
  have hπ : Tendsto (fun m => ps m (kk m)) atTop (𝓝 Q.1) := by
    have hgoal : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, dist (ps m (kk m)) Q.1 < ε := by
      intro ε hε
      obtain ⟨N1, hN1⟩ := hrateN (ε / 2) (by linarith)
      obtain ⟨N2, hN2⟩ := hQ1' (ε / 2) (by linarith)
      refine ⟨max N1 N2, fun m hm => ?_⟩
      have ha := hN1 m (le_trans (le_max_left _ _) hm)
      have hb := hN2 m (le_trans (le_max_right _ _) hm)
      have htri : dist (ps m (kk m)) Q.1
          ≤ dist (ps m (kk m)) ((q m).1) + dist ((q m).1) Q.1 := dist_triangle _ _ _
      have h3 := hk3 m
      linarith
    exact Metric.tendsto_atTop.mpr hgoal
  have hΞ : Tendsto (fun m => Xs m (kk m)) atTop (𝓝 Q.2) := by
    -- same shape, and here the typed `have` is mandatory: applied with `refine ... (fun ε hε =>
    -- ?_)` the index type of `Metric.tendsto_atTop` stays a metavariable on the operator space
    -- and `SemilatticeSup ?β` gets stuck
    have hgoal : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, dist (Xs m (kk m)) Q.2 < ε := by
      intro ε hε
      obtain ⟨N1, hN1⟩ := hrateN (ε / 2) (by linarith)
      obtain ⟨N2, hN2⟩ := hQ2' (ε / 2) (by linarith)
      refine ⟨max N1 N2, fun m hm => ?_⟩
      have ha := hN1 m (le_trans (le_max_left _ _) hm)
      have hb := hN2 m (le_trans (le_max_right _ _) hm)
      have htri : dist (Xs m (kk m)) Q.2
          ≤ dist (Xs m (kk m)) ((q m).2) + dist ((q m).2) Q.2 := dist_triangle _ _ _
      have h4 := hk4 m
      linarith
    exact Metric.tendsto_atTop.mpr hgoal
  -- The five requirements of `ClosedSuperjet` for `Q`.  Symmetry of the `Xs m (kk m)` needs no
  -- separate check: `Superjet` carries it as its first conjunct, so `hjet` already supplies it.
  exact ⟨fun m => zs m (kk m), fun m => ps m (kk m), fun m => Xs m (kk m),
    fun m => hjet m (kk m), hζ, hfζ, hπ, hΞ⟩
