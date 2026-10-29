module

public import InfHarmonic.SemiconvexOn
public import InfHarmonic.ConvexSubgradientExists
public import InfHarmonic.MaxMultiplierPinsSubgradient
public import InfHarmonic.SemiconvexMultiplierLipschitz
public import InfHarmonic.StrictMaxPerturbLocalization
public import InfHarmonic.LipschitzImageHaarBound

@[expose] public section
open Set MeasureTheory Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Jensen's lemma: for a semiconvex function with a strict maximum at the centre
of a ball, the set of nearby points that are local maxima of a small linear
perturbation has positive measure. -/
theorem JensenLemma (μ : Measure E) [μ.IsAddHaarMeasure] (lam r : ℝ) (hlam : 0 < lam)
    (hr : 0 < r) (φ : E → ℝ) (z₀ : E) (hφc : ContinuousOn φ (closedBall z₀ r))
    (hφ : SemiconvexOn lam (ball z₀ r) φ)
    (hstrict : ∀ z ∈ closedBall z₀ r, z ≠ z₀ → φ z < φ z₀)
    (δ : ℝ) (hδ : 0 < δ) :
    0 < μ {z ∈ ball z₀ r | ∃ p : E, ‖p‖ ≤ δ ∧
      IsLocalMaxOn (fun w => φ w + inner ℝ p w) (ball z₀ r) z} := by
  classical
  -- the three radii: the inner ball `r₁`, the localization radius `ρ`, and the
  -- free room `η = r₁ - ρ` around a localized point
  obtain ⟨r₁, hr₁d⟩ : ∃ x : ℝ, x = r / 2 := ⟨_, rfl⟩
  obtain ⟨ρ, hρd⟩ : ∃ x : ℝ, x = r / 8 := ⟨_, rfl⟩
  obtain ⟨η, hηd⟩ : ∃ x : ℝ, x = 3 * r / 8 := ⟨_, rfl⟩
  have hρpos : 0 < ρ := by rw [hρd]; positivity
  have hηpos : 0 < η := by rw [hηd]; positivity
  have hr₁pos : 0 < r₁ := by rw [hr₁d]; positivity
  have hρr₁ : ρ ≤ r₁ := by rw [hρd, hr₁d]; linarith
  have hr₁r : r₁ < r := by rw [hr₁d]; linarith
  have hsub₁ : closedBall z₀ r₁ ⊆ closedBall z₀ r := closedBall_subset_closedBall hr₁r.le
  -- Step 1: the localization threshold `δ₀`, and the working bound `d = min δ δ₀`
  obtain ⟨δ₀, hδ₀pos, hloc⟩ := StrictMaxPerturbLocalization φ z₀ r₁ ρ hρpos hρr₁
    (hφc.mono hsub₁) (fun z hz hne => hstrict z (hsub₁ hz) hne)
  obtain ⟨d, hdd⟩ : ∃ x : ℝ, x = min δ δ₀ := ⟨_, rfl⟩
  have hdpos : 0 < d := by rw [hdd]; exact lt_min hδ hδ₀pos
  have hdδ : d ≤ δ := by rw [hdd]; exact min_le_left _ _
  have hdδ₀ : d ≤ δ₀ := by rw [hdd]; exact min_le_right _ _
  -- Step 2: the set `K`
  obtain ⟨K, hKd⟩ : ∃ S : Set E, S = {z : E | z ∈ closedBall z₀ r₁ ∧ ∃ p : E, ‖p‖ ≤ d ∧
      ∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p w ≤ φ z + inner ℝ p z} := ⟨_, rfl⟩
  have hKmem : ∀ z : E, z ∈ K ↔ (z ∈ closedBall z₀ r₁ ∧ ∃ p : E, ‖p‖ ≤ d ∧
      ∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p w ≤ φ z + inner ℝ p z) := by
    intro z; rw [hKd]; exact Iff.rfl
  -- the geometric room: a ball of radius `η` about a point within `ρ` of `z₀`
  have hballsub : ∀ z : E, ‖z - z₀‖ < ρ → ball z η ⊆ closedBall z₀ r₁ ∩ ball z₀ r := by
    intro z hzρ w hw
    have h1 : ‖w - z‖ < η := by simpa [mem_ball, dist_eq_norm] using hw
    have h3 : ‖w - z₀‖ ≤ ‖w - z‖ + ‖z - z₀‖ := by
      have he : w - z₀ = (w - z) + (z - z₀) := by abel
      rw [he]; exact norm_add_le _ _
    rw [hηd] at h1
    rw [hρd] at hzρ
    have h2 : ‖w - z₀‖ < r₁ := by rw [hr₁d]; linarith
    refine ⟨?_, ?_⟩
    · simpa [mem_closedBall, dist_eq_norm] using h2.le
    · simp only [mem_ball, dist_eq_norm]; linarith [h2, hr₁r]
  have hKloc : ∀ z ∈ K, ‖z - z₀‖ < ρ := by
    intro z hz
    obtain ⟨hz1, p, hp, hmp⟩ := (hKmem z).mp hz
    exact hloc p (le_trans hp hdδ₀) z hz1 hmp
  -- Step 3: the multiplier of a point of `K` is unique
  have huniq : ∀ z ∈ K, ∀ p p' : E,
      (∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p w ≤ φ z + inner ℝ p z) →
      (∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p' w ≤ φ z + inner ℝ p' z) → p = p' := by
    intro z hz p p' hp hp'
    have hbs := hballsub z (hKloc z hz)
    have hzΩ : z ∈ ball z₀ r := (hbs (mem_ball_self hηpos)).2
    obtain ⟨s, hs⟩ := ConvexSubgradientExists (ball z₀ r) isOpen_ball
      (fun w => φ w + lam * ‖w‖ ^ 2 / 2) hφ z hzΩ
    have hs' : ∀ w ∈ ball z₀ r, φ z + lam * ‖z‖ ^ 2 / 2 + inner ℝ s (w - z)
        ≤ φ w + lam * ‖w‖ ^ 2 / 2 := hs
    have e1 : s = lam • z - p := MaxMultiplierPinsSubgradient lam φ (closedBall z₀ r₁)
      (ball z₀ r) z p s η hηpos hbs hp hs'
    have e2 : s = lam • z - p' := MaxMultiplierPinsSubgradient lam φ (closedBall z₀ r₁)
      (ball z₀ r) z p' s η hηpos hbs hp' hs'
    have he := e1.symm.trans e2
    linear_combination (norm := module) -he
  -- the multiplier map `H`, chosen on `K` and set to `0` off `K`
  have hHex : ∀ z : E, ∃ p : E, z ∈ K → (‖p‖ ≤ d ∧
      ∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p w ≤ φ z + inner ℝ p z) := by
    intro z
    by_cases hz : z ∈ K
    · obtain ⟨-, p, hp⟩ := (hKmem z).mp hz
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose H hH using hHex
  -- Step 4: `H` is `2 * lam`-Lipschitz on `K`
  have hlipreal : ∀ x ∈ K, ∀ y ∈ K, ‖H x - H y‖ ≤ 2 * lam * ‖x - y‖ := by
    intro x hx y hy
    have hb1 := hballsub x (hKloc x hx)
    have hb2 := hballsub y (hKloc y hy)
    have hxy : ‖x - y‖ < η := by
      have h1 := hKloc x hx
      have h2 := hKloc y hy
      have h3 : ‖x - y‖ ≤ ‖x - z₀‖ + ‖z₀ - y‖ := by
        have he : x - y = (x - z₀) + (z₀ - y) := by abel
        rw [he]; exact norm_add_le _ _
      have h4 : ‖z₀ - y‖ = ‖y - z₀‖ := by rw [← neg_sub, norm_neg]
      rw [hηd]; rw [hρd] at h1 h2; linarith
    exact SemiconvexMultiplierLipschitz lam hlam (ball z₀ r) isOpen_ball φ hφ
      (closedBall z₀ r₁) x y (H x) (H y) η hηpos hb1 hb2 hxy (hH x hx).2 (hH y hy).2
  have hlip : LipschitzOnWith (2 * lam).toNNReal H K := by
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (by positivity)]
    exact hlipreal x hx y hy
  -- Step 5: the measure estimate
  have himg := LipschitzImageHaarBound μ (2 * lam).toNNReal K H hlip
  have honto : closedBall (0 : E) d ⊆ H '' K := by
    intro p hp
    have hpn : ‖p‖ ≤ d := by simpa [mem_closedBall, dist_zero_right] using hp
    have hcont : ContinuousOn (fun w => φ w + inner ℝ p w) (closedBall z₀ r₁) :=
      (hφc.mono hsub₁).add (continuous_const.inner continuous_id).continuousOn
    obtain ⟨z, hzmem, hzmax⟩ := (isCompact_closedBall z₀ r₁).exists_isMaxOn
      ⟨z₀, mem_closedBall_self hr₁pos.le⟩ hcont
    have hmp : ∀ w ∈ closedBall z₀ r₁, φ w + inner ℝ p w ≤ φ z + inner ℝ p z :=
      fun w hw => hzmax hw
    have hzK : z ∈ K := (hKmem z).mpr ⟨hzmem, p, hpn, hmp⟩
    exact ⟨z, hzK, huniq z hzK (H z) p (hH z hzK).2 hmp⟩
  have hbpos : 0 < μ (closedBall (0 : E) d) :=
    lt_of_lt_of_le (Metric.measure_ball_pos μ 0 hdpos) (measure_mono ball_subset_closedBall)
  have hchain : μ (closedBall (0 : E) d)
      ≤ ((2 * lam).toNNReal : ENNReal) ^ (Module.finrank ℝ E) * μ K :=
    le_trans (measure_mono honto) himg
  have hKpos : 0 < μ K := by
    rcases eq_or_ne (μ K) 0 with h0 | h
    · rw [h0, mul_zero] at hchain
      exact absurd hbpos (not_lt.mpr hchain)
    · exact zero_lt_iff.mpr h
  -- `K` is contained in the set of the statement
  refine lt_of_lt_of_le hKpos (measure_mono ?_)
  intro z hzK
  have hbs := hballsub z (hKloc z hzK)
  refine ⟨(hbs (mem_ball_self hηpos)).2, H z, le_trans (hH z hzK).1 hdδ, ?_⟩
  have hnb : ∀ᶠ w in nhds z, φ w + inner ℝ (H z) w ≤ φ z + inner ℝ (H z) z := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hηpos)] with w hw
    exact (hH z hzK).2 w (hbs hw).1
  exact hnb.filter_mono nhdsWithin_le_nhds
