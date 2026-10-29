import InfHarmonic.QuadEnvFarCompetitors
import InfHarmonic.QuadEnvBallMax
import InfHarmonic.QuadEnvBallMin
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 3 of Lemma 4.3: around an admissible pair `(l₀, z₀)` with `l₀ > 0` there is a
compact box of lengths and centers on which ONE fixed closed ball of radius `M`
localizes the envelope, so that on the whole box the envelope is the extremum of a
jointly continuous function over a parameter-independent compact set; joint
continuity of the envelope at `(l₀, z₀)` follows. -/
theorem QuadEnvBoxRepresentation (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f)
    (l₀ : ℝ) (hl₀ : 0 < l₀) (z₀ : WithLp 2 (F × ℝ)) :
    ((ofLp z₀).2 + l₀ ∈ I → ∃ ρ M : ℝ, 0 < ρ ∧ 0 < M ∧
        (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), |l - l₀| ≤ ρ →
            ‖(ofLp z).1 - (ofLp z₀).1‖ ≤ ρ → |(ofLp z).2 - (ofLp z₀).2| ≤ ρ →
            0 < l ∧ (ofLp z).2 + l ∈ I ∧
            QuadEnvP f l z = sSup ((fun y : F =>
                f (toLp 2 (y, (ofLp z).2 + l))
                  - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) '' closedBall (0 : F) M)) ∧
        ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => QuadEnvP f p.1 p.2) (l₀, z₀)) ∧
    ((ofLp z₀).2 - l₀ ∈ I → ∃ ρ M : ℝ, 0 < ρ ∧ 0 < M ∧
        (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), |l - l₀| ≤ ρ →
            ‖(ofLp z).1 - (ofLp z₀).1‖ ≤ ρ → |(ofLp z).2 - (ofLp z₀).2| ≤ ρ →
            0 < l ∧ (ofLp z).2 - l ∈ I ∧
            QuadEnvM f l z = sInf ((fun y : F =>
                f (toLp 2 (y, (ofLp z).2 - l))
                  + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) '' closedBall (0 : F) M)) ∧
        ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => QuadEnvM f p.1 p.2) (l₀, z₀)) := by
  -- A space-time point whose time level lies in `I` lies where `f` is continuous.
  have hΩ : ∀ s : ℝ, s ∈ I → ∀ y : F,
      (toLp 2 (y, s) : WithLp 2 (F × ℝ))
        ∈ (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) ⁻¹' I := fun _ hs _ => hs
  constructor
  · -- FORWARD.  The time window `J` around `t₀ + l₀`.
    intro htl₀
    obtain ⟨σ, hσ, hσsub⟩ := Metric.isOpen_iff.mp hI _ htl₀
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (σ / 4) (l₀ / 4) := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min (by linarith) (by linarith)
    have hρσ : 4 * ρ ≤ σ := by
      have h := min_le_left (σ / 4) (l₀ / 4); rw [hρdef]; linarith
    have hρl : 4 * ρ ≤ l₀ := by
      have h := min_le_right (σ / 4) (l₀ / 4); rw [hρdef]; linarith
    obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (ofLp z₀).2 + l₀ - 2 * ρ := ⟨_, rfl⟩
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (ofLp z₀).2 + l₀ + 2 * ρ := ⟨_, rfl⟩
    have hab : a ≤ b := by rw [hadef, hbdef]; linarith
    obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Icc a b := ⟨_, rfl⟩
    have hJc : IsCompact J := by rw [hJdef]; exact isCompact_Icc
    have hJne : J.Nonempty := ⟨a, by rw [hJdef]; exact ⟨le_rfl, hab⟩⟩
    have hJI : J ⊆ I := by
      rw [hJdef]
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      rw [hadef] at hs1
      rw [hbdef] at hs2
      refine hσsub ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    -- Step 1 at `R₀ = |x₀| + ρ`, this `J`, and the length bound `l₀ + ρ`.
    obtain ⟨M, N, hM, hbd, hfar⟩ :=
      QuadEnvFarCompetitors I f hcont hgrow (‖(ofLp z₀).1‖ + ρ) (by positivity)
        J hJI hJne hJc (l₀ + ρ) (by linarith)
    have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ 1) hM)
    have hMR : ‖(ofLp z₀).1‖ + ρ ≤ M := le_trans (le_max_left _ _) hM
    have hBc : IsCompact (closedBall (0 : F) M) := isCompact_closedBall _ _
    -- The ball representation, uniformly on the closed box.
    have hbox : ∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), |l - l₀| ≤ ρ →
        ‖(ofLp z).1 - (ofLp z₀).1‖ ≤ ρ → |(ofLp z).2 - (ofLp z₀).2| ≤ ρ →
        0 < l ∧ (ofLp z).2 + l ∈ I ∧
        QuadEnvP f l z = sSup ((fun y : F =>
            f (toLp 2 (y, (ofLp z).2 + l))
              - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) '' closedBall (0 : F) M) := by
      intro l z hlb hxb htb
      obtain ⟨hl1, hl2⟩ := abs_le.mp hlb
      obtain ⟨ht1, ht2⟩ := abs_le.mp htb
      have hl : 0 < l := by linarith
      have hlmax : l ≤ l₀ + ρ := by linarith
      have hsJ : (ofLp z).2 + l ∈ J := by
        rw [hJdef, hadef, hbdef]; exact ⟨by linarith, by linarith⟩
      have hxR : ‖(ofLp z).1‖ ≤ ‖(ofLp z₀).1‖ + ρ := by
        have h1 := norm_sub_norm_le (ofLp z).1 (ofLp z₀).1
        linarith
      have hfc : ContinuousOn (fun y : F => f (toLp 2 (y, (ofLp z).2 + l)))
          (closedBall (0 : F) M) :=
        (hcont.comp_continuous (by fun_prop : Continuous (fun y : F =>
          (toLp 2 (y, (ofLp z).2 + l) : WithLp 2 (F × ℝ))))
          (fun y => hΩ _ (hJI hsJ) y)).continuousOn
      exact ⟨hl, hJI hsJ, (QuadEnvBallMax f l hl z M (le_trans hxR hMR) hfc
        (fun y hy =>
          (hfar (ofLp z).1 y ((ofLp z).2 + l) l hxR hsJ hl hlmax hy).1)).1⟩
    refine ⟨ρ, M, hρ0, hM0, hbox, ?_⟩
    -- The open box, a neighbourhood of `(l₀, z₀)` inside the closed box.
    obtain ⟨U, hUdef⟩ : ∃ U : Set (ℝ × WithLp 2 (F × ℝ)),
        U = {p : ℝ × WithLp 2 (F × ℝ) | |p.1 - l₀| < ρ} ∩
            ({p : ℝ × WithLp 2 (F × ℝ) | ‖(ofLp p.2).1 - (ofLp z₀).1‖ < ρ} ∩
              {p : ℝ × WithLp 2 (F × ℝ) | |(ofLp p.2).2 - (ofLp z₀).2| < ρ}) := ⟨_, rfl⟩
    have hUopen : IsOpen U := by
      rw [hUdef]
      exact (isOpen_lt (by fun_prop) continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_const).inter
          (isOpen_lt (by fun_prop) continuous_const))
    have hUmem : (l₀, z₀) ∈ U := by
      rw [hUdef]; refine ⟨?_, ?_, ?_⟩ <;> simp [hρ0]
    have hUle : ∀ p ∈ U, |p.1 - l₀| ≤ ρ ∧ ‖(ofLp p.2).1 - (ofLp z₀).1‖ ≤ ρ ∧
        |(ofLp p.2).2 - (ofLp z₀).2| ≤ ρ := by
      intro p hp
      rw [hUdef] at hp
      exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
    -- The competitor function with the length and the time level CLAMPED, which
    -- makes it continuous on the whole parameter space while changing nothing on `U`.
    have hgJ : ∀ p : ℝ × WithLp 2 (F × ℝ),
        min (max ((ofLp p.2).2 + p.1) a) b ∈ J := fun p => by
      rw [hJdef]; exact ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩
    have hHc : Continuous (fun q : (ℝ × WithLp 2 (F × ℝ)) × F =>
        f (toLp 2 (q.2, min (max ((ofLp q.1.2).2 + q.1.1) a) b))
          - ‖q.2 - (ofLp q.1.2).1‖ ^ 2 / (2 * max q.1.1 (l₀ / 2))) := by
      refine Continuous.sub ?_ ?_
      · exact hcont.comp_continuous (by fun_prop) (fun q => hΩ _ (hJI (hgJ q.1)) q.2)
      · have hne : ∀ q : (ℝ × WithLp 2 (F × ℝ)) × F, 2 * max q.1.1 (l₀ / 2) ≠ 0 := by
          intro q
          have h := le_max_right q.1.1 (l₀ / 2)
          have : (0:ℝ) < 2 * max q.1.1 (l₀ / 2) := by linarith
          exact this.ne'
        simp only [div_eq_mul_inv]
        exact (by fun_prop : Continuous (fun q : (ℝ × WithLp 2 (F × ℝ)) × F =>
          ‖q.2 - (ofLp q.1.2).1‖ ^ 2)).mul
          ((by fun_prop : Continuous (fun q : (ℝ × WithLp 2 (F × ℝ)) × F =>
            2 * max q.1.1 (l₀ / 2))).inv₀ hne)
    have hΦ : Continuous (fun p : ℝ × WithLp 2 (F × ℝ) => sSup ((fun y : F =>
        f (toLp 2 (y, min (max ((ofLp p.2).2 + p.1) a) b))
          - ‖y - (ofLp p.2).1‖ ^ 2 / (2 * max p.1 (l₀ / 2))) '' closedBall (0 : F) M)) :=
      hBc.continuous_sSup
        (f := fun (p : ℝ × WithLp 2 (F × ℝ)) (y : F) =>
          f (toLp 2 (y, min (max ((ofLp p.2).2 + p.1) a) b))
            - ‖y - (ofLp p.2).1‖ ^ 2 / (2 * max p.1 (l₀ / 2))) hHc
    refine hΦ.continuousAt.congr ?_
    filter_upwards [hUopen.mem_nhds hUmem] with p hp
    obtain ⟨h1, h2, h3⟩ := hUle p hp
    obtain ⟨hl1, hl2⟩ := abs_le.mp h1
    obtain ⟨ht1, ht2⟩ := abs_le.mp h3
    have hmaxl : max p.1 (l₀ / 2) = p.1 := max_eq_left (by linarith)
    have hminmax : min (max ((ofLp p.2).2 + p.1) a) b = (ofLp p.2).2 + p.1 := by
      rw [max_eq_left (by rw [hadef]; linarith), min_eq_left (by rw [hbdef]; linarith)]
    rw [hmaxl, hminmax]
    exact ((hbox p.1 p.2 h1 h2 h3).2.2).symm
  · -- BACKWARD.  The mirror argument, with the time level `t - ℓ`, the window `J`
    -- around `t₀ - l₀`, the `+` cost, and minima in place of maxima.
    intro htl₀
    obtain ⟨σ, hσ, hσsub⟩ := Metric.isOpen_iff.mp hI _ htl₀
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (σ / 4) (l₀ / 4) := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min (by linarith) (by linarith)
    have hρσ : 4 * ρ ≤ σ := by
      have h := min_le_left (σ / 4) (l₀ / 4); rw [hρdef]; linarith
    have hρl : 4 * ρ ≤ l₀ := by
      have h := min_le_right (σ / 4) (l₀ / 4); rw [hρdef]; linarith
    obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = (ofLp z₀).2 - l₀ - 2 * ρ := ⟨_, rfl⟩
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = (ofLp z₀).2 - l₀ + 2 * ρ := ⟨_, rfl⟩
    have hab : a ≤ b := by rw [hadef, hbdef]; linarith
    obtain ⟨J, hJdef⟩ : ∃ J : Set ℝ, J = Icc a b := ⟨_, rfl⟩
    have hJc : IsCompact J := by rw [hJdef]; exact isCompact_Icc
    have hJne : J.Nonempty := ⟨a, by rw [hJdef]; exact ⟨le_rfl, hab⟩⟩
    have hJI : J ⊆ I := by
      rw [hJdef]
      intro s hs
      obtain ⟨hs1, hs2⟩ := hs
      rw [hadef] at hs1
      rw [hbdef] at hs2
      refine hσsub ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith, by linarith⟩
    obtain ⟨M, N, hM, hbd, hfar⟩ :=
      QuadEnvFarCompetitors I f hcont hgrow (‖(ofLp z₀).1‖ + ρ) (by positivity)
        J hJI hJne hJc (l₀ + ρ) (by linarith)
    have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one (le_trans (le_max_right _ 1) hM)
    have hMR : ‖(ofLp z₀).1‖ + ρ ≤ M := le_trans (le_max_left _ _) hM
    have hBc : IsCompact (closedBall (0 : F) M) := isCompact_closedBall _ _
    have hbox : ∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), |l - l₀| ≤ ρ →
        ‖(ofLp z).1 - (ofLp z₀).1‖ ≤ ρ → |(ofLp z).2 - (ofLp z₀).2| ≤ ρ →
        0 < l ∧ (ofLp z).2 - l ∈ I ∧
        QuadEnvM f l z = sInf ((fun y : F =>
            f (toLp 2 (y, (ofLp z).2 - l))
              + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) '' closedBall (0 : F) M) := by
      intro l z hlb hxb htb
      obtain ⟨hl1, hl2⟩ := abs_le.mp hlb
      obtain ⟨ht1, ht2⟩ := abs_le.mp htb
      have hl : 0 < l := by linarith
      have hlmax : l ≤ l₀ + ρ := by linarith
      have hsJ : (ofLp z).2 - l ∈ J := by
        rw [hJdef, hadef, hbdef]; exact ⟨by linarith, by linarith⟩
      have hxR : ‖(ofLp z).1‖ ≤ ‖(ofLp z₀).1‖ + ρ := by
        have h1 := norm_sub_norm_le (ofLp z).1 (ofLp z₀).1
        linarith
      have hfc : ContinuousOn (fun y : F => f (toLp 2 (y, (ofLp z).2 - l)))
          (closedBall (0 : F) M) :=
        (hcont.comp_continuous (by fun_prop : Continuous (fun y : F =>
          (toLp 2 (y, (ofLp z).2 - l) : WithLp 2 (F × ℝ))))
          (fun y => hΩ _ (hJI hsJ) y)).continuousOn
      exact ⟨hl, hJI hsJ, (QuadEnvBallMin f l hl z M (le_trans hxR hMR) hfc
        (fun y hy =>
          (hfar (ofLp z).1 y ((ofLp z).2 - l) l hxR hsJ hl hlmax hy).2)).1⟩
    refine ⟨ρ, M, hρ0, hM0, hbox, ?_⟩
    obtain ⟨U, hUdef⟩ : ∃ U : Set (ℝ × WithLp 2 (F × ℝ)),
        U = {p : ℝ × WithLp 2 (F × ℝ) | |p.1 - l₀| < ρ} ∩
            ({p : ℝ × WithLp 2 (F × ℝ) | ‖(ofLp p.2).1 - (ofLp z₀).1‖ < ρ} ∩
              {p : ℝ × WithLp 2 (F × ℝ) | |(ofLp p.2).2 - (ofLp z₀).2| < ρ}) := ⟨_, rfl⟩
    have hUopen : IsOpen U := by
      rw [hUdef]
      exact (isOpen_lt (by fun_prop) continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_const).inter
          (isOpen_lt (by fun_prop) continuous_const))
    have hUmem : (l₀, z₀) ∈ U := by
      rw [hUdef]; refine ⟨?_, ?_, ?_⟩ <;> simp [hρ0]
    have hUle : ∀ p ∈ U, |p.1 - l₀| ≤ ρ ∧ ‖(ofLp p.2).1 - (ofLp z₀).1‖ ≤ ρ ∧
        |(ofLp p.2).2 - (ofLp z₀).2| ≤ ρ := by
      intro p hp
      rw [hUdef] at hp
      exact ⟨hp.1.le, hp.2.1.le, hp.2.2.le⟩
    have hgJ : ∀ p : ℝ × WithLp 2 (F × ℝ),
        min (max ((ofLp p.2).2 - p.1) a) b ∈ J := fun p => by
      rw [hJdef]; exact ⟨le_min (le_max_right _ _) hab, min_le_right _ _⟩
    have hHc : Continuous (fun q : (ℝ × WithLp 2 (F × ℝ)) × F =>
        f (toLp 2 (q.2, min (max ((ofLp q.1.2).2 - q.1.1) a) b))
          + ‖q.2 - (ofLp q.1.2).1‖ ^ 2 / (2 * max q.1.1 (l₀ / 2))) := by
      refine Continuous.add ?_ ?_
      · exact hcont.comp_continuous (by fun_prop) (fun q => hΩ _ (hJI (hgJ q.1)) q.2)
      · have hne : ∀ q : (ℝ × WithLp 2 (F × ℝ)) × F, 2 * max q.1.1 (l₀ / 2) ≠ 0 := by
          intro q
          have h := le_max_right q.1.1 (l₀ / 2)
          have : (0:ℝ) < 2 * max q.1.1 (l₀ / 2) := by linarith
          exact this.ne'
        simp only [div_eq_mul_inv]
        exact (by fun_prop : Continuous (fun q : (ℝ × WithLp 2 (F × ℝ)) × F =>
          ‖q.2 - (ofLp q.1.2).1‖ ^ 2)).mul
          ((by fun_prop : Continuous (fun q : (ℝ × WithLp 2 (F × ℝ)) × F =>
            2 * max q.1.1 (l₀ / 2))).inv₀ hne)
    have hΦ : Continuous (fun p : ℝ × WithLp 2 (F × ℝ) => sInf ((fun y : F =>
        f (toLp 2 (y, min (max ((ofLp p.2).2 - p.1) a) b))
          + ‖y - (ofLp p.2).1‖ ^ 2 / (2 * max p.1 (l₀ / 2))) '' closedBall (0 : F) M)) :=
      hBc.continuous_sInf
        (f := fun (p : ℝ × WithLp 2 (F × ℝ)) (y : F) =>
          f (toLp 2 (y, min (max ((ofLp p.2).2 - p.1) a) b))
            + ‖y - (ofLp p.2).1‖ ^ 2 / (2 * max p.1 (l₀ / 2))) hHc
    refine hΦ.continuousAt.congr ?_
    filter_upwards [hUopen.mem_nhds hUmem] with p hp
    obtain ⟨h1, h2, h3⟩ := hUle p hp
    obtain ⟨hl1, hl2⟩ := abs_le.mp h1
    obtain ⟨ht1, ht2⟩ := abs_le.mp h3
    have hmaxl : max p.1 (l₀ / 2) = p.1 := max_eq_left (by linarith)
    have hminmax : min (max ((ofLp p.2).2 - p.1) a) b = (ofLp p.2).2 - p.1 := by
      rw [max_eq_left (by rw [hadef]; linarith), min_eq_left (by rw [hbdef]; linarith)]
    rw [hmaxl, hminmax]
    exact ((hbox p.1 p.2 h1 h2 h3).2.2).symm
