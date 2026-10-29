import InfHarmonic.QuadEnvP
import InfHarmonic.QuadEnvM
import InfHarmonic.SubquadraticGrowth
import InfHarmonic.QuadEnvFarCompetitors
import InfHarmonic.QuadEnvBallMax
import InfHarmonic.QuadEnvBallMin
import InfHarmonic.QuadEnvBoxRepresentation
import InfHarmonic.QuadEnvOptimizerRate
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.3, attainment and continuity: for a continuous function with
subquadratic spatial growth on compact time intervals the two quadratic envelopes
are attained, are continuous in the center at each fixed positive length, tend to
the function as the length tends to zero, and their optimizers collapse to the
center. -/
theorem QuadEnvAttained (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f) :
    (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), 0 < l → (ofLp z).2 ∈ I → (ofLp z).2 + l ∈ I →
        ∃ y : F, QuadEnvP f l z
          = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) ∧
    (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), 0 < l → (ofLp z).2 ∈ I → (ofLp z).2 - l ∈ I →
        ∃ y : F, QuadEnvM f l z
          = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) ∧
    (∀ l₀ : ℝ, 0 < l₀ → ∀ z₀ : WithLp 2 (F × ℝ), (ofLp z₀).2 ∈ I → (ofLp z₀).2 + l₀ ∈ I →
        ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => QuadEnvP f p.1 p.2) (l₀, z₀)) ∧
    (∀ l₀ : ℝ, 0 < l₀ → ∀ z₀ : WithLp 2 (F × ℝ), (ofLp z₀).2 ∈ I → (ofLp z₀).2 - l₀ ∈ I →
        ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => QuadEnvM f p.1 p.2) (l₀, z₀)) ∧
    (∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K → (∀ z ∈ K, (ofLp z).2 ∈ I) →
        ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, 0 < l → l < δ → ∀ z ∈ K,
          |QuadEnvP f l z - f z| ≤ η ∧ |QuadEnvM f l z - f z| ≤ η) ∧
    (∀ z : WithLp 2 (F × ℝ), (ofLp z).2 ∈ I → ∀ η : ℝ, 0 < η → ∃ δ : ℝ, 0 < δ ∧
        ∀ l : ℝ, 0 < l → l < δ → ∀ y : F,
          (QuadEnvP f l z = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l) →
            ‖y - (ofLp z).1‖ ≤ η) ∧
          (QuadEnvM f l z = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) →
            ‖y - (ofLp z).1‖ ≤ η)) := by
  -- A time slice of `f` is continuous on any spatial set as soon as the time level
  -- lies in `I`: the slice map lands in the set where `hcont` applies.
  have hslice : ∀ s : ℝ, s ∈ I → ∀ S : Set F,
      ContinuousOn (fun y : F => f (toLp 2 (y, s))) S := by
    intro s hs S
    have hmap : Continuous (fun y : F => (toLp 2 (y, s) : WithLp 2 (F × ℝ))) := by fun_prop
    exact hcont.comp hmap.continuousOn (fun y _ => hs)
  have hrt : ∀ z : WithLp 2 (F × ℝ),
      (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := fun z => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1), forward attainment: Step 1 at `R₀ = |x|`, `J = {t+ℓ}`, `ℓ₀ = ℓ`, then Step 2.
    intro l z hl _ htl
    obtain ⟨M, N, hM, hbd, hfar⟩ :=
      QuadEnvFarCompetitors I f hcont hgrow ‖(ofLp z).1‖ (norm_nonneg _)
        {(ofLp z).2 + l} (singleton_subset_iff.mpr htl) (singleton_nonempty _)
        isCompact_singleton l hl
    have hxM : ‖(ofLp z).1‖ ≤ M := le_trans (le_max_left _ _) hM
    obtain ⟨-, y, -, hy⟩ :=
      QuadEnvBallMax f l hl z M hxM (hslice _ htl _)
        (fun y hy => (hfar (ofLp z).1 y ((ofLp z).2 + l) l le_rfl rfl hl le_rfl hy).1)
    exact ⟨y, hy⟩
  · -- (1), backward attainment: the same with `J = {t-ℓ}` and the second inequality.
    intro l z hl _ htl
    obtain ⟨M, N, hM, hbd, hfar⟩ :=
      QuadEnvFarCompetitors I f hcont hgrow ‖(ofLp z).1‖ (norm_nonneg _)
        {(ofLp z).2 - l} (singleton_subset_iff.mpr htl) (singleton_nonempty _)
        isCompact_singleton l hl
    have hxM : ‖(ofLp z).1‖ ≤ M := le_trans (le_max_left _ _) hM
    obtain ⟨-, y, -, hy⟩ :=
      QuadEnvBallMin f l hl z M hxM (hslice _ htl _)
        (fun y hy => (hfar (ofLp z).1 y ((ofLp z).2 - l) l le_rfl rfl hl le_rfl hy).2)
    exact ⟨y, hy⟩
  · -- (2), forward: the box representation of Step 3 carries the joint continuity.
    intro l₀ hl₀ z₀ _ htl₀
    obtain ⟨ρ, M, -, -, -, hcts⟩ :=
      (QuadEnvBoxRepresentation I hI f hcont hgrow l₀ hl₀ z₀).1 htl₀
    exact hcts
  · -- (2), backward.
    intro l₀ hl₀ z₀ _ htl₀
    obtain ⟨ρ, M, -, -, -, hcts⟩ :=
      (QuadEnvBoxRepresentation I hI f hcont hgrow l₀ hl₀ z₀).2 htl₀
    exact hcts
  · -- (3), uniform convergence at length zero on a compact set of centers.
    intro K hK hKI η hη
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · refine ⟨1, one_pos, fun l _ _ z hz => ?_⟩
      rw [hKe] at hz
      simp at hz
    -- the compact time projection of `K`, thickened inside `I`
    obtain ⟨T, hTdef⟩ : ∃ T : Set ℝ,
        T = (fun z : WithLp 2 (F × ℝ) => (ofLp z).2) '' K := ⟨_, rfl⟩
    have hTc : IsCompact T := by rw [hTdef]; exact hK.image (by fun_prop)
    have hTI : T ⊆ I := by
      rw [hTdef]; rintro s ⟨w, hw, rfl⟩; exact hKI w hw
    obtain ⟨L, hL, hLsub⟩ := hTc.exists_cthickening_subset_open hI hTI
    obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Metric.cthickening L T := ⟨_, rfl⟩
    have hJc : IsCompact J := by rw [hJdef]; exact hTc.cthickening
    have hJI : J ⊆ I := by rw [hJdef]; exact hLsub
    have hTJ : T ⊆ J := by rw [hJdef]; exact self_subset_cthickening T
    have hJne : J.Nonempty := by
      obtain ⟨w, hw⟩ := hKne
      exact ⟨(ofLp w).2, hTJ (by rw [hTdef]; exact ⟨w, hw, rfl⟩)⟩
    -- the spatial radius of `K`
    obtain ⟨w₀, hw₀K, hw₀max⟩ :=
      hK.exists_isMaxOn hKne (f := fun z : WithLp 2 (F × ℝ) => ‖(ofLp z).1‖) (by fun_prop)
    obtain ⟨R₀, hR₀def⟩ : ∃ R₀ : ℝ, R₀ = ‖(ofLp w₀).1‖ := ⟨_, rfl⟩
    have hR₀0 : (0:ℝ) ≤ R₀ := by rw [hR₀def]; exact norm_nonneg _
    have hR₀K : ∀ z ∈ K, ‖(ofLp z).1‖ ≤ R₀ := by
      intro z hz; rw [hR₀def]; exact hw₀max hz
    obtain ⟨M, N, hM, hbd, hfar⟩ :=
      QuadEnvFarCompetitors I f hcont hgrow R₀ hR₀0 J hJI hJne hJc L hL
    have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos (le_trans (le_max_right R₀ 1) hM)
    have hN0 : (0:ℝ) ≤ N := by
      obtain ⟨s, hs⟩ := hJne
      exact le_trans (abs_nonneg _) (hbd 0 s (by simpa using hM0.le) hs)
    -- uniform continuity of `f` on the compact box `{|y| ≤ M} × J`
    obtain ⟨Q, hQdef⟩ : ∃ Q : Set (F × ℝ), Q = Metric.closedBall (0:F) M ×ˢ J := ⟨_, rfl⟩
    have hQc : IsCompact Q := by rw [hQdef]; exact (isCompact_closedBall _ _).prod hJc
    have hQmem : ∀ (y : F) (s : ℝ), ‖y‖ ≤ M → s ∈ J → (y, s) ∈ Q := by
      intro y s hy hs
      rw [hQdef]
      exact ⟨mem_closedBall_zero_iff.mpr hy, hs⟩
    have hgc : ContinuousOn (fun p : F × ℝ => f (toLp 2 p)) Q := by
      have hmap : Continuous (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) := by fun_prop
      refine hcont.comp hmap.continuousOn ?_
      intro p hp
      rw [hQdef] at hp
      exact hJI hp.2
    obtain ⟨δ₁, hδ₁, hδ₁u⟩ :=
      Metric.uniformContinuousOn_iff_le.mp (hQc.uniformContinuousOn_of_continuous hgc) η hη
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ,
        δ = min L (min (δ₁ / 2) (δ₁ ^ 2 / (32 * N + 1))) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδdef]
      exact lt_min hL (lt_min (by positivity) (by positivity))
    refine ⟨δ, hδ0, ?_⟩
    intro l hl hlδ z hzK
    have hlL : l ≤ L := le_trans hlδ.le (by rw [hδdef]; exact min_le_left _ _)
    have hlδ₁ : l ≤ δ₁ / 2 :=
      le_trans hlδ.le (by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_left _ _))
    have hlsq : l * (32 * N + 1) ≤ δ₁ ^ 2 := by
      have h := le_trans hlδ.le
        (by rw [hδdef]; exact le_trans (min_le_right _ _) (min_le_right _ _) :
          δ ≤ δ₁ ^ 2 / (32 * N + 1))
      rwa [le_div_iff₀ (by positivity : (0:ℝ) < 32 * N + 1)] at h
    have htJ : (ofLp z).2 ∈ J := hTJ (by rw [hTdef]; exact ⟨z, hzK, rfl⟩)
    have htpJ : (ofLp z).2 + l ∈ J := by
      rw [hJdef]
      refine mem_cthickening_of_dist_le _ (ofLp z).2 L T (by rw [hTdef]; exact ⟨z, hzK, rfl⟩) ?_
      rw [Real.dist_eq, add_sub_cancel_left, abs_of_pos hl]
      exact hlL
    have htmJ : (ofLp z).2 - l ∈ J := by
      rw [hJdef]
      refine mem_cthickening_of_dist_le _ (ofLp z).2 L T (by rw [hTdef]; exact ⟨z, hzK, rfl⟩) ?_
      rw [Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hl]
      exact hlL
    have hxR₀ : ‖(ofLp z).1‖ ≤ R₀ := hR₀K z hzK
    have hxM : ‖(ofLp z).1‖ ≤ M := le_trans hxR₀ (le_trans (le_max_left _ _) hM)
    have hbd' : ∀ y : F, ‖y‖ ≤ M →
        |f (toLp 2 (y, (ofLp z).2 + l))| ≤ N ∧ |f (toLp 2 (y, (ofLp z).2 - l))| ≤ N :=
      fun y hy => ⟨hbd y _ hy htpJ, hbd y _ hy htmJ⟩
    have hfarP : ∀ y : F, M < ‖y‖ →
        f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
          < f (toLp 2 ((ofLp z).1, (ofLp z).2 + l)) :=
      fun y hy => (hfar (ofLp z).1 y ((ofLp z).2 + l) l hxR₀ htpJ hl hlL hy).1
    have hfarM : ∀ y : F, M < ‖y‖ →
        f (toLp 2 ((ofLp z).1, (ofLp z).2 - l))
          < f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
      fun y hy => (hfar (ofLp z).1 y ((ofLp z).2 - l) l hxR₀ htmJ hl hlL hy).2
    obtain ⟨⟨hlowP, hrateP⟩, ⟨hupM, hrateM⟩⟩ :=
      QuadEnvOptimizerRate f l hl z M N hxM hN0 hbd'
        (fun y hy => ⟨hfarP y hy, hfarM y hy⟩)
    obtain ⟨-, yP, -, hyP⟩ :=
      QuadEnvBallMax f l hl z M hxM (hslice _ (hJI htpJ) _) hfarP
    obtain ⟨-, yM, -, hyM⟩ :=
      QuadEnvBallMin f l hl z M hxM (hslice _ (hJI htmJ) _) hfarM
    obtain ⟨hyPM, hyPrate⟩ := hrateP yP hyP
    obtain ⟨hyMM, hyMrate⟩ := hrateM yM hyM
    -- the optimizer displacement is below `δ₁ / 2`
    have hrate : ∀ y : F, ‖y - (ofLp z).1‖ ≤ 2 * Real.sqrt (N * l) → ‖y - (ofLp z).1‖ ≤ δ₁ / 2 := by
      intro y hy
      have h1 : N * l ≤ (δ₁ / 4) ^ 2 := by nlinarith [hl.le, hδ₁.le]
      refine hy.trans ?_
      calc 2 * Real.sqrt (N * l) ≤ 2 * Real.sqrt ((δ₁ / 4) ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (by norm_num)
        _ = 2 * (δ₁ / 4) := by rw [Real.sqrt_sq (by positivity)]
        _ = δ₁ / 2 := by ring
    -- the three relevant points of the box, and the two uniform-continuity estimates
    have hcmp : ∀ y : F, ‖y‖ ≤ M → ∀ s : ℝ, s ∈ J → ‖y - (ofLp z).1‖ ≤ δ₁ / 2 → |s - (ofLp z).2| ≤ δ₁ →
        |f (toLp 2 (y, s)) - f z| ≤ η := by
      intro y hy s hs hyd hsd
      have hd : dist ((y, s) : F × ℝ) ((ofLp z).1, (ofLp z).2) ≤ δ₁ := by
        rw [Prod.dist_eq]
        refine max_le ?_ ?_
        · rw [dist_eq_norm]; linarith [hyd, hδ₁.le]
        · rw [Real.dist_eq]; exact hsd
      have h := hδ₁u _ (hQmem y s hy hs) _ (hQmem (ofLp z).1 (ofLp z).2 hxM htJ) hd
      rw [Real.dist_eq, hrt z] at h
      exact h
    have hldist : |((ofLp z).2 + l) - (ofLp z).2| ≤ δ₁ := by
      rw [add_sub_cancel_left, abs_of_pos hl]; linarith [hδ₁.le]
    have hldist' : |((ofLp z).2 - l) - (ofLp z).2| ≤ δ₁ := by
      rw [sub_sub_cancel_left, abs_neg, abs_of_pos hl]; linarith [hδ₁.le]
    have hx0 : ‖(ofLp z).1 - (ofLp z).1‖ ≤ δ₁ / 2 := by simp; positivity
    constructor
    · -- forward
      have hPup : QuadEnvP f l z ≤ f (toLp 2 (yP, (ofLp z).2 + l)) := by
        rw [hyP]
        have : (0:ℝ) ≤ ‖yP - (ofLp z).1‖ ^ 2 / (2 * l) := by positivity
        linarith
      have h1 := hcmp yP hyPM _ htpJ (hrate yP hyPrate) hldist
      have h2 := hcmp (ofLp z).1 hxM _ htpJ hx0 hldist
      rw [abs_le] at h1 h2 ⊢
      constructor <;> [linarith [h2.1, hlowP]; linarith [h1.2, hPup]]
    · -- backward
      have hMlow : f (toLp 2 (yM, (ofLp z).2 - l)) ≤ QuadEnvM f l z := by
        rw [hyM]
        have : (0:ℝ) ≤ ‖yM - (ofLp z).1‖ ^ 2 / (2 * l) := by positivity
        linarith
      have h1 := hcmp yM hyMM _ htmJ (hrate yM hyMrate) hldist'
      have h2 := hcmp (ofLp z).1 hxM _ htmJ hx0 hldist'
      rw [abs_le] at h1 h2 ⊢
      constructor <;> [linarith [h1.1, hMlow]; linarith [h2.2, hupM]]
  · -- (4), the optimizer collapse at a single admissible center.
    intro z ht η hη
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hI _ ht
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = ε / 2 := ⟨_, rfl⟩
    have hL : 0 < L := by rw [hLdef]; positivity
    obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Metric.closedBall (ofLp z).2 L := ⟨_, rfl⟩
    have hJI : J ⊆ I := by
      rw [hJdef]
      refine subset_trans (Metric.closedBall_subset_ball ?_) hεsub
      rw [hLdef]; linarith
    have hJc : IsCompact J := by rw [hJdef]; exact isCompact_closedBall _ _
    have hJne : J.Nonempty :=
      ⟨(ofLp z).2, by rw [hJdef]; exact Metric.mem_closedBall_self hL.le⟩
    obtain ⟨M, N, hM, hbd, hfar⟩ :=
      QuadEnvFarCompetitors I f hcont hgrow ‖(ofLp z).1‖ (norm_nonneg _) J hJI hJne hJc L hL
    have hM0 : (0:ℝ) < M := lt_of_lt_of_le one_pos (le_trans (le_max_right _ 1) hM)
    have hN0 : (0:ℝ) ≤ N := by
      obtain ⟨s, hs⟩ := hJne
      exact le_trans (abs_nonneg _) (hbd 0 s (by simpa using hM0.le) hs)
    have hxM : ‖(ofLp z).1‖ ≤ M := le_trans (le_max_left _ _) hM
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min L (η ^ 2 / (4 * N + 1)) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by
      rw [hδdef]; exact lt_min hL (by positivity)
    refine ⟨δ, hδ0, ?_⟩
    intro l hl hlδ y
    have hlL : l ≤ L := le_trans hlδ.le (by rw [hδdef]; exact min_le_left _ _)
    have hlsq : l * (4 * N + 1) ≤ η ^ 2 := by
      have h := le_trans hlδ.le
        (by rw [hδdef]; exact min_le_right _ _ : δ ≤ η ^ 2 / (4 * N + 1))
      rwa [le_div_iff₀ (by positivity : (0:ℝ) < 4 * N + 1)] at h
    have htpJ : (ofLp z).2 + l ∈ J := by
      rw [hJdef, Metric.mem_closedBall, Real.dist_eq, add_sub_cancel_left, abs_of_pos hl]
      exact hlL
    have htmJ : (ofLp z).2 - l ∈ J := by
      rw [hJdef, Metric.mem_closedBall, Real.dist_eq, sub_sub_cancel_left, abs_neg, abs_of_pos hl]
      exact hlL
    obtain ⟨⟨-, hrateP⟩, ⟨-, hrateM⟩⟩ :=
      QuadEnvOptimizerRate f l hl z M N hxM hN0
        (fun y hy => ⟨hbd y _ hy htpJ, hbd y _ hy htmJ⟩)
        (fun y hy => ⟨(hfar (ofLp z).1 y ((ofLp z).2 + l) l le_rfl htpJ hl hlL hy).1,
          (hfar (ofLp z).1 y ((ofLp z).2 - l) l le_rfl htmJ hl hlL hy).2⟩)
    have key : 2 * Real.sqrt (N * l) ≤ η := by
      have h1 : N * l ≤ (η / 2) ^ 2 := by nlinarith [hl.le, hη.le]
      calc 2 * Real.sqrt (N * l) ≤ 2 * Real.sqrt ((η / 2) ^ 2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) (by norm_num)
        _ = 2 * (η / 2) := by rw [Real.sqrt_sq (by positivity)]
        _ = η := by ring
    exact ⟨fun hy => le_trans (hrateP y hy).2 key, fun hy => le_trans (hrateM y hy).2 key⟩
