module

public import InfHarmonic.QuadEnvAttained

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.5), the composition identities
`P_ℓ (P_h f) = P_{ℓ+h} f` and `M_ℓ (M_h f) = M_{ℓ+h} f`. -/
theorem QuadEnvComposition (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f) :
    (∀ (l h : ℝ) (z : WithLp 2 (F × ℝ)), 0 < l → 0 < h →
        (ofLp z).2 ∈ I → (ofLp z).2 + h ∈ I → (ofLp z).2 + (l + h) ∈ I →
        QuadEnvP (QuadEnvP f h) l z = QuadEnvP f (l + h) z) ∧
    (∀ (l h : ℝ) (z : WithLp 2 (F × ℝ)), 0 < l → 0 < h →
        (ofLp z).2 ∈ I → (ofLp z).2 - h ∈ I → (ofLp z).2 - (l + h) ∈ I →
        QuadEnvM (QuadEnvM f h) l z = QuadEnvM f (l + h) z) := by
  classical
  -- Openness of `I` is not used: Step 2 needs only the growth condition at the single
  -- time slice and continuity of `f` there, and the identity itself needs only the
  -- outermost time argument, as the .tex records.  The binder is in the frozen
  -- signature, so it is acknowledged here rather than renamed.
  have _unused_hI : IsOpen I := hI
  -- ===================== Step 1: the parallel-axis identity ========================
  -- Pure inner-product algebra in `x`, `w`, `y`, `l`, `h`: expand the four squared
  -- norms into the six scalars and clear denominators.
  have paxis : ∀ (l h : ℝ), 0 < l → 0 < h → ∀ x w y : F,
      ‖y - x‖ ^ 2 / (2 * l) + ‖w - y‖ ^ 2 / (2 * h)
        = ‖w - x‖ ^ 2 / (2 * (l + h))
          + (l + h) / (2 * l * h)
            * ‖y - ((h / (l + h)) • x + (l / (l + h)) • w)‖ ^ 2 := by
    intro l h hl hh x w y
    have hlh : (0 : ℝ) < l + h := by linarith
    have c1 : (inner ℝ w y : ℝ) = inner ℝ y w := real_inner_comm y w
    have c2 : (inner ℝ w x : ℝ) = inner ℝ x w := real_inner_comm x w
    have c3 : (inner ℝ y x : ℝ) = inner ℝ x y := real_inner_comm x y
    simp only [norm_sub_sq_real, norm_add_sq_real, inner_add_right, real_inner_smul_right,
      real_inner_smul_left, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, c1, c2, c3]
    field_simp
    ring
  -- (1a) the cost of any intermediate point dominates the direct cost
  have p1a : ∀ (l h : ℝ), 0 < l → 0 < h → ∀ x w y : F,
      ‖w - x‖ ^ 2 / (2 * (l + h))
        ≤ ‖y - x‖ ^ 2 / (2 * l) + ‖w - y‖ ^ 2 / (2 * h) := by
    intro l h hl hh x w y
    have h1 := paxis l h hl hh x w y
    have h2 : (0 : ℝ) ≤ (l + h) / (2 * l * h)
        * ‖y - ((h / (l + h)) • x + (l / (l + h)) • w)‖ ^ 2 := by positivity
    linarith
  -- (1b) with equality at the midpoint `y_*`
  have p1b : ∀ (l h : ℝ), 0 < l → 0 < h → ∀ x w : F,
      ‖((h / (l + h)) • x + (l / (l + h)) • w) - x‖ ^ 2 / (2 * l)
          + ‖w - ((h / (l + h)) • x + (l / (l + h)) • w)‖ ^ 2 / (2 * h)
        = ‖w - x‖ ^ 2 / (2 * (l + h)) := by
    intro l h hl hh x w
    have h1 := paxis l h hl hh x w ((h / (l + h)) • x + (l / (l + h)) • w)
    rw [sub_self, norm_zero] at h1
    simpa using h1
  -- ===================== Step 2: the one-sided bound on a single time slice =========
  -- One statement serves both halves: it bounds `|f|` against the direct cost, so the
  -- forward family is bounded ABOVE by `B` and the backward family below by `-B`.
  have bound : ∀ (σ r : ℝ), 0 < r → σ ∈ I → ∀ x : F, ∃ B : ℝ, 0 ≤ B ∧
      ∀ w : F, |f (toLp 2 (w, σ))| - ‖w - x‖ ^ 2 / (2 * r) ≤ B := by
    intro σ r hr hσ x
    have h2r : (0 : ℝ) < 2 * r := by linarith
    have h8r : (0 : ℝ) < 8 * r := by linarith
    obtain ⟨M, hM0, hMb⟩ := hgrow {σ} (by simpa using hσ) isCompact_singleton
      (1 / (8 * r)) (by positivity)
    have hdiv : ∀ w : F, 1 / (8 * r) * ‖w‖ ^ 2 = ‖w‖ ^ 2 / (8 * r) := by
      intro w; field_simp
    obtain ⟨R, hRd⟩ : ∃ t : ℝ, t = max M (2 * ‖x‖) := ⟨_, rfl⟩
    have hR0 : 0 < R := by rw [hRd]; exact lt_max_of_lt_left hM0
    -- far field: the direct cost already dominates `|f|`
    have hfar : ∀ w : F, R ≤ ‖w‖ → |f (toLp 2 (w, σ))| - ‖w - x‖ ^ 2 / (2 * r) ≤ 0 := by
      intro w hw
      have hwM : M ≤ ‖w‖ := le_trans (by rw [hRd]; exact le_max_left _ _) hw
      have hwx : 2 * ‖x‖ ≤ ‖w‖ := le_trans (by rw [hRd]; exact le_max_right _ _) hw
      have hb : |f (toLp 2 (w, σ))| ≤ ‖w‖ ^ 2 / (8 * r) := by
        calc |f (toLp 2 (w, σ))| ≤ 1 / (8 * r) * ‖w‖ ^ 2 := by
              simpa using hMb (toLp 2 (w, σ)) (by simpa using hwM) (by simp)
          _ = ‖w‖ ^ 2 / (8 * r) := hdiv w
      have hb2 : |f (toLp 2 (w, σ))| * (8 * r) ≤ ‖w‖ ^ 2 := by
        rw [← le_div_iff₀ h8r]; exact hb
      have hd : ‖w‖ / 2 ≤ ‖w - x‖ := by
        have h1 : ‖w‖ - ‖x‖ ≤ ‖w - x‖ := by simpa using norm_sub_norm_le w x
        linarith
      have hd2 : ‖w‖ ^ 2 / 4 ≤ ‖w - x‖ ^ 2 := by
        have hy0 : (0 : ℝ) ≤ ‖w‖ / 2 := by positivity
        nlinarith [mul_le_mul hd hd hy0 (norm_nonneg (w - x))]
      have hle : |f (toLp 2 (w, σ))| ≤ ‖w - x‖ ^ 2 / (2 * r) := by
        rw [le_div_iff₀ h2r]; linarith
      linarith
    -- near field: continuity on a compact ball
    have hmap : Continuous (fun w : F => (toLp 2 (w, σ) : WithLp 2 (F × ℝ))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hmaps : ∀ w : F, (toLp 2 (w, σ) : WithLp 2 (F × ℝ))
        ∈ (fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' I := fun w => hσ
    have hcty : ContinuousOn (fun w : F => f (toLp 2 (w, σ))) (Metric.closedBall (0 : F) R) :=
      ContinuousOn.comp hcont hmap.continuousOn (fun w _ => hmaps w)
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : F) R).exists_bound_of_continuousOn hcty
    refine ⟨max C 0, le_max_right _ _, fun w => ?_⟩
    rcases le_or_gt R ‖w‖ with hw | hw
    · exact le_trans (hfar w hw) (le_max_right _ _)
    · have h1 : |f (toLp 2 (w, σ))| ≤ C := by
        simpa using hC w (by simpa using hw.le)
      have h2 : (0 : ℝ) ≤ ‖w - x‖ ^ 2 / (2 * r) := by positivity
      have h3 : C ≤ max C 0 := le_max_left _ _
      linarith
  refine ⟨?_, ?_⟩
  -- ===================== the forward identity =======================================
  · intro l h z hl hh _ht _hth hs
    have hlne : l ≠ 0 := ne_of_gt hl
    have hhne : h ≠ 0 := ne_of_gt hh
    have hlh : (0 : ℝ) < l + h := by linarith
    have hlhne : l + h ≠ 0 := ne_of_gt hlh
    -- the three envelopes, as suprema over explicit families
    have hinner : ∀ y : F, QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l))
        = sSup {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 + (l + h)))
            - ‖w - y‖ ^ 2 / (2 * h)} := by
      intro y
      have he : QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l))
          = sSup {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 + l + h))
              - ‖w - y‖ ^ 2 / (2 * h)} := by
        rw [QuadEnvP, if_neg hhne]
      rw [he, show (ofLp z).2 + l + h = (ofLp z).2 + (l + h) from by ring]
    have houter : QuadEnvP (QuadEnvP f h) l z
        = sSup {u : ℝ | ∃ y : F, u = QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l))
            - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      rw [QuadEnvP, if_neg hlne]
    have htarget : QuadEnvP f (l + h) z
        = sSup {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 + (l + h)))
            - ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} := by
      rw [QuadEnvP, if_neg hlhne]
    obtain ⟨B, hB0, hBb⟩ := bound ((ofLp z).2 + (l + h)) (l + h) hlh hs (ofLp z).1
    -- the target family: nonempty and bounded above by `B`
    have htne : {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 + (l + h)))
        - ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))}.Nonempty := ⟨_, (ofLp z).1, rfl⟩
    have htbd : BddAbove {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 + (l + h)))
        - ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} := by
      refine ⟨B, ?_⟩
      rintro u ⟨w, rfl⟩
      have h1 := hBb w
      have h2 := le_abs_self (f (toLp 2 (w, (ofLp z).2 + (l + h))))
      linarith
    -- each inner family: nonempty and bounded above by `B + ‖y - x‖²/(2ℓ)`
    have hine : ∀ y : F, {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 + (l + h)))
        - ‖w - y‖ ^ 2 / (2 * h)}.Nonempty := fun y => ⟨_, y, rfl⟩
    have hinub : ∀ (y : F) (v : ℝ), v ∈ {v : ℝ | ∃ w : F,
        v = f (toLp 2 (w, (ofLp z).2 + (l + h))) - ‖w - y‖ ^ 2 / (2 * h)} →
        v ≤ B + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) := by
      rintro y v ⟨w, rfl⟩
      have h1 := hBb w
      have h2 := le_abs_self (f (toLp 2 (w, (ofLp z).2 + (l + h))))
      have h3 := p1a l h hl hh (ofLp z).1 w y
      linarith
    have hinbd : ∀ y : F, BddAbove {v : ℝ | ∃ w : F,
        v = f (toLp 2 (w, (ofLp z).2 + (l + h))) - ‖w - y‖ ^ 2 / (2 * h)} :=
      fun y => ⟨B + ‖y - (ofLp z).1‖ ^ 2 / (2 * l), hinub y⟩
    -- the outer family: nonempty and bounded above by `B`
    have hone : {u : ℝ | ∃ y : F, u = QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l))
        - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}.Nonempty := ⟨_, (ofLp z).1, rfl⟩
    have honbd : BddAbove {u : ℝ | ∃ y : F,
        u = QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      refine ⟨B, ?_⟩
      rintro u ⟨y, rfl⟩
      rw [hinner y]
      have h1 := csSup_le (hine y) (hinub y)
      linarith
    rw [houter, htarget]
    refine le_antisymm (csSup_le hone ?_) (csSup_le htne ?_)
    · -- every outer value is at most the target supremum
      rintro u ⟨y, rfl⟩
      rw [hinner y]
      have h1 : sSup {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 + (l + h)))
          - ‖w - y‖ ^ 2 / (2 * h)}
          ≤ sSup {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 + (l + h)))
              - ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) := by
        refine csSup_le (hine y) ?_
        rintro v ⟨w, rfl⟩
        have h2 : f (toLp 2 (w, (ofLp z).2 + (l + h)))
            - ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))
            ≤ sSup {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 + (l + h)))
                - ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} := le_csSup htbd ⟨w, rfl⟩
        have h3 := p1a l h hl hh (ofLp z).1 w y
        linarith
      linarith
    · -- every target value is attained in the outer family, at the midpoint
      rintro u ⟨w, rfl⟩
      obtain ⟨y, hyd⟩ : ∃ p : F, p = (h / (l + h)) • (ofLp z).1 + (l / (l + h)) • w :=
        ⟨_, rfl⟩
      have hmid : ‖y - (ofLp z).1‖ ^ 2 / (2 * l) + ‖w - y‖ ^ 2 / (2 * h)
          = ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h)) := by
        rw [hyd]; exact p1b l h hl hh (ofLp z).1 w
      have h1 : f (toLp 2 (w, (ofLp z).2 + (l + h))) - ‖w - y‖ ^ 2 / (2 * h)
          ≤ QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l)) := by
        rw [hinner y]
        exact le_csSup (hinbd y) ⟨w, rfl⟩
      have h2 : QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
          ≤ sSup {u : ℝ | ∃ y : F, u = QuadEnvP f h (toLp 2 (y, (ofLp z).2 + l))
              - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := le_csSup honbd ⟨y, rfl⟩
      linarith
  -- ===================== the backward identity ======================================
  -- Not the forward case applied to `-f`: unwinding `QuadEnvP` for `-f` shifts time
  -- FORWARD by `l`, while `QuadEnvM` shifts it backward, and reconciling the two would
  -- reflect the time variable and so replace `I` by its reflection.  The cost signs are
  -- not reversed either: both costs are added and the SAME infimum (1b) is used.
  · intro l h z hl hh _ht _hth hs
    have hlne : l ≠ 0 := ne_of_gt hl
    have hhne : h ≠ 0 := ne_of_gt hh
    have hlh : (0 : ℝ) < l + h := by linarith
    have hlhne : l + h ≠ 0 := ne_of_gt hlh
    have hinner : ∀ y : F, QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l))
        = sInf {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 - (l + h)))
            + ‖w - y‖ ^ 2 / (2 * h)} := by
      intro y
      have he : QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l))
          = sInf {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 - l - h))
              + ‖w - y‖ ^ 2 / (2 * h)} := by
        rw [QuadEnvM, if_neg hhne]
      rw [he, show (ofLp z).2 - l - h = (ofLp z).2 - (l + h) from by ring]
    have houter : QuadEnvM (QuadEnvM f h) l z
        = sInf {u : ℝ | ∃ y : F, u = QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l))
            + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      rw [QuadEnvM, if_neg hlne]
    have htarget : QuadEnvM f (l + h) z
        = sInf {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 - (l + h)))
            + ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} := by
      rw [QuadEnvM, if_neg hlhne]
    obtain ⟨B, hB0, hBb⟩ := bound ((ofLp z).2 - (l + h)) (l + h) hlh hs (ofLp z).1
    have htne : {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 - (l + h)))
        + ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))}.Nonempty := ⟨_, (ofLp z).1, rfl⟩
    have htbd : BddBelow {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 - (l + h)))
        + ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} := by
      refine ⟨-B, ?_⟩
      rintro u ⟨w, rfl⟩
      have h1 := hBb w
      have h2 := neg_abs_le (f (toLp 2 (w, (ofLp z).2 - (l + h))))
      linarith
    have hine : ∀ y : F, {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 - (l + h)))
        + ‖w - y‖ ^ 2 / (2 * h)}.Nonempty := fun y => ⟨_, y, rfl⟩
    have hinlb : ∀ (y : F) (v : ℝ), v ∈ {v : ℝ | ∃ w : F,
        v = f (toLp 2 (w, (ofLp z).2 - (l + h))) + ‖w - y‖ ^ 2 / (2 * h)} →
        -B - ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ v := by
      rintro y v ⟨w, rfl⟩
      have h1 := hBb w
      have h2 := neg_abs_le (f (toLp 2 (w, (ofLp z).2 - (l + h))))
      have h3 := p1a l h hl hh (ofLp z).1 w y
      linarith
    have hinbd : ∀ y : F, BddBelow {v : ℝ | ∃ w : F,
        v = f (toLp 2 (w, (ofLp z).2 - (l + h))) + ‖w - y‖ ^ 2 / (2 * h)} :=
      fun y => ⟨-B - ‖y - (ofLp z).1‖ ^ 2 / (2 * l), hinlb y⟩
    have hone : {u : ℝ | ∃ y : F, u = QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l))
        + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}.Nonempty := ⟨_, (ofLp z).1, rfl⟩
    have honbd : BddBelow {u : ℝ | ∃ y : F,
        u = QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      refine ⟨-B, ?_⟩
      rintro u ⟨y, rfl⟩
      rw [hinner y]
      have h1 := le_csInf (hine y) (hinlb y)
      linarith
    rw [houter, htarget]
    refine le_antisymm (le_csInf htne ?_) (le_csInf hone ?_)
    · -- every target value dominates the outer infimum, via the midpoint
      rintro u ⟨w, rfl⟩
      obtain ⟨y, hyd⟩ : ∃ p : F, p = (h / (l + h)) • (ofLp z).1 + (l / (l + h)) • w :=
        ⟨_, rfl⟩
      have hmid : ‖y - (ofLp z).1‖ ^ 2 / (2 * l) + ‖w - y‖ ^ 2 / (2 * h)
          = ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h)) := by
        rw [hyd]; exact p1b l h hl hh (ofLp z).1 w
      have h1 : QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l))
          ≤ f (toLp 2 (w, (ofLp z).2 - (l + h))) + ‖w - y‖ ^ 2 / (2 * h) := by
        rw [hinner y]
        exact csInf_le (hinbd y) ⟨w, rfl⟩
      have h2 : sInf {u : ℝ | ∃ y : F, u = QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l))
              + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}
          ≤ QuadEnvM f h (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
        csInf_le honbd ⟨y, rfl⟩
      linarith
    · -- every outer value dominates the target infimum
      rintro u ⟨y, rfl⟩
      rw [hinner y]
      have h1 : sInf {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 - (l + h)))
              + ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))} - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
          ≤ sInf {v : ℝ | ∃ w : F, v = f (toLp 2 (w, (ofLp z).2 - (l + h)))
              + ‖w - y‖ ^ 2 / (2 * h)} := by
        refine le_csInf (hine y) ?_
        rintro v ⟨w, rfl⟩
        have h2 : sInf {u : ℝ | ∃ w : F, u = f (toLp 2 (w, (ofLp z).2 - (l + h)))
                + ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h))}
            ≤ f (toLp 2 (w, (ofLp z).2 - (l + h)))
              + ‖w - (ofLp z).1‖ ^ 2 / (2 * (l + h)) := csInf_le htbd ⟨w, rfl⟩
        have h3 := p1a l h hl hh (ofLp z).1 w y
        linarith
      linarith
