module

public import InfHarmonic.FlatnessModulus
public import InfHarmonic.ThreePointFlatness
public import InfHarmonic.AffineBlowups
public import InfHarmonic.NormalizedFamilyLipschitz
public import InfHarmonic.InfHarmonicMono
public import InfHarmonic.NormalizedFamilyInfHarmonic
public import InfHarmonic.EquiLipschitzUniformLimit
public import InfHarmonic.MidpointLinearOnBall
public import InfHarmonic.SlowScalesAndBlowupLimit
public import InfHarmonic.BlowupLimitVanishingMidpointDefect

@[expose] public section
open Set Metric

/-- Uniform qualitative flatness (paper Lemma 3.2, the `b(s) → 0` display): the
family flatness modulus of the normalized family tends to zero as the scale
ratio tends to zero. -/
theorem FamilyFlatness (d : ℕ) (hd : 1 ≤ d) :
    ∀ ε > 0, ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 8 ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → FlatnessModulus d hd s ≤ ε := by
  classical
  -- THE sSup GOAL CARRIES NO NONEMPTINESS OBLIGATION, and the .tex says so: its opening
  -- paragraph establishes "boundedness above, and nothing more" and records that
  -- nonemptiness "is needed only for the approximation property of a supremum" in Step 2.
  -- `Real.sSup_le` is the matching Lean lemma: it takes the per-element upper bound and
  -- `0 ≤ ε`, and the junk value `sSup ∅ = 0` of pm-0026 satisfies the goal on its own.
  -- So the whole node reduces to the bound at an arbitrary admissible triple.
  intro ε hε
  -- THE REMAINING OBLIGATION, stated per admissible triple rather than on the supremum.
  -- The threshold `s₀` depends on `ε`; it is produced in the .tex by Steps 2-10, which
  -- negate this statement and derive a contradiction.
  obtain ⟨s₀, hs₀pos, hs₀le, hbd⟩ : ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 8 ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ →
      ∀ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
        (z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (r : ℝ),
        NormalizedInfFamily d U →
        z ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) →
        0 < r →
        r ≤ s * infDist z
          (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) →
        BetaFlatness U z r ≤ ε := by
    -- The whole of Steps 2-10 is one proof by contradiction: `hcon` is the negation of the
    -- per-triple bound, and it is what Step 2's hole consumes.
    by_contra hcon
    push Not at hcon
    -- ===================== NOTATION AND THE COMMON CONSTANT =====================
    -- `e_b = (0,1)` is the unit time direction; `L` is the constant of eq:ff-lip.
    obtain ⟨eb, hebdef⟩ : ∃ eb : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        eb = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) := ⟨_, rfl⟩
    obtain ⟨L, hL0, hLb⟩ := NormalizedFamilyLipschitz d hd
    -- ===================== STEP 2: THE CONTRADICTION HYPOTHESIS =====================
    -- eq:ff-badb, eq:ff-beta and eq:ff-lam together.  This is the ONE place the
    -- approximation property of a supremum -- hence nonemptiness of the two defining
    -- sets -- is used, and the .tex derives it at the point of use from the strict
    -- positivity of the suprema concerned; pm-0026 bites here and nowhere else in this
    -- node.  The last conjunct is the .tex's `r_i ≤ ¾ s_i`, which uses `D(z) ≤ ¾`.
    obtain ⟨sq, Uq, zq, rq, lamq, hsq0, hsqle, hUq, hzq, hrq0, hrqle, hlamq, hlamqbad⟩ :
        ∃ (sq : ℕ → ℝ) (Uq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
          (zq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rq lamq : ℕ → ℝ),
          (∀ i, 0 < sq i) ∧
          (∀ i, sq i ≤ 1 / ((i : ℝ) + 1)) ∧
          (∀ i, NormalizedInfFamily d (Uq i)) ∧
          (∀ i, zq i ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)) ∧
          (∀ i, 0 < rq i) ∧
          (∀ i, rq i ≤ 3 / 4 * sq i) ∧
          (∀ i, lamq i ∈ Ioo ε 1) ∧
          (∀ i, ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit (Uq i) (zq i) (rq i) (lamq i) P) := by
      -- `D(z) ≤ 3/4`: the frontier of the 3/4-ball is the sphere of that radius, and the
      -- radial projection of `z` onto it is at distance `3/4 - ‖z‖ ≤ 3/4`.  This is what
      -- turns `r ≤ s · D(z)` into the `r ≤ ¾ s` recorded in the package.
      have hDle : ∀ z ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4),
          infDist z
            (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)))
            ≤ 3 / 4 := by
        intro z hz
        rw [mem_ball, dist_zero_right] at hz
        rw [frontier_ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          (by norm_num : (3:ℝ)/4 ≠ 0)]
        have key : ∀ y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖y‖ = 3/4 → ‖z - y‖ ≤ 3/4 →
            infDist z (sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3/4)) ≤ 3/4 := by
          intro y hyn hzy
          have hymem : y ∈ sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3/4) := by
            rw [mem_sphere, dist_zero_right, hyn]
          refine le_trans (infDist_le_dist_of_mem hymem) ?_
          rw [dist_eq_norm]; exact hzy
        rcases eq_or_ne z 0 with h0 | h0
        · obtain ⟨v, hv⟩ := exists_ne (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
          refine key ((3/4 * ‖v‖⁻¹) • v) ?_ ?_
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc,
              inv_mul_cancel₀ hvn, mul_one]
          · rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
              abs_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ hvn, mul_one]
        · have hzn : (0:ℝ) < ‖z‖ := norm_pos_iff.mpr h0
          refine key ((3/4 / ‖z‖) • z) ?_ ?_
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
              div_mul_cancel₀ _ (ne_of_gt hzn)]
          · have hsub : z - (3/4 / ‖z‖) • z = (1 - 3/4 / ‖z‖) • z := by
              rw [sub_smul, one_smul]
            rw [hsub, norm_smul, Real.norm_eq_abs]
            have hneg : 1 - 3/4 / ‖z‖ ≤ 0 := by
              rw [sub_nonpos, le_div_iff₀ hzn]; linarith only [hz]
            rw [abs_of_nonpos hneg]
            have h1 : -(1 - 3/4 / ‖z‖) * ‖z‖ = 3/4 - ‖z‖ := by
              field_simp
              ring
            rw [h1]
            linarith only [hzn]
      -- THE APPROXIMATION PROPERTY, used here and nowhere else in this node.  The
      -- defining set of `BetaFlatness` is bounded above by `1`; it is NONEMPTY because
      -- its supremum exceeds `ε > 0` while an empty supremum is `0` (pm-0026's junk
      -- value is what supplies nonemptiness here, rather than obstructing it).
      have happrox : ∀ (Uv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
          (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
          ε < BetaFlatness Uv zv rv →
          ∃ lamv : ℝ, lamv ∈ Ioo ε 1 ∧
            ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
              IsCylinderFit Uv zv rv lamv P := by
        intro Uv zv rv hgt
        rw [BetaFlatness] at hgt
        have hne : {lam : ℝ | lam ∈ Ioo (0 : ℝ) 1 ∧
            ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
              IsCylinderFit Uv zv rv lam P}.Nonempty := by
          rcases Set.eq_empty_or_nonempty {lam : ℝ | lam ∈ Ioo (0 : ℝ) 1 ∧
              ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
                IsCylinderFit Uv zv rv lam P} with hemp | hne'
          · rw [hemp, Real.sSup_empty] at hgt
            exact absurd hgt (not_lt.mpr (le_of_lt hε))
          · exact hne'
        obtain ⟨lamv, hlamvmem, hlamvgt⟩ := exists_lt_of_lt_csSup hne hgt
        exact ⟨lamv, ⟨hlamvgt, hlamvmem.1.2⟩, hlamvmem.2⟩
      -- one failing triple for each index, from `hcon` at `s₀ = min (1/8) (1/(i+1))`
      have hstep : ∀ i : ℕ, ∃ (sv : ℝ) (Uv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
          (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv lamv : ℝ),
          0 < sv ∧ sv ≤ 1 / ((i : ℝ) + 1) ∧ NormalizedInfFamily d Uv ∧
          zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
          0 < rv ∧ rv ≤ 3 / 4 * sv ∧ lamv ∈ Ioo ε 1 ∧
          ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit Uv zv rv lamv P := by
        intro i
        have hipos : (0 : ℝ) < 1 / ((i : ℝ) + 1) := by positivity
        obtain ⟨sv, hsv0, hsvle, Uv, zv, rv, hUv, hzv, hrv0, hrvle, hbeta⟩ :=
          hcon (min (1 / 8) (1 / ((i : ℝ) + 1))) (lt_min (by norm_num) hipos)
            (min_le_left _ _)
        obtain ⟨lamv, hlamv, hlamvbad⟩ := happrox Uv zv rv hbeta
        refine ⟨sv, Uv, zv, rv, lamv, hsv0, le_trans hsvle (min_le_right _ _), hUv, hzv,
          hrv0, ?_, hlamv, hlamvbad⟩
        have hD := hDle zv hzv
        have h1 : sv * infDist zv
            (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)))
            ≤ sv * (3 / 4) := mul_le_mul_of_nonneg_left hD (le_of_lt hsv0)
        linarith only [hrvle, h1]
      choose sqv Uqv zqv rqv lamqv g1 g2 g3 g4 g5 g6 g7 g8 using hstep
      exact ⟨sqv, Uqv, zqv, rqv, lamqv, g1, g2, g3, g4, g5, g6, g7, g8⟩
    -- `r_i → 0`
    have hrqlim : Filter.Tendsto rq Filter.atTop (nhds 0) := by
      have hbase : Filter.Tendsto (fun i : ℕ => 3 / 4 * (1 / ((i : ℝ) + 1)))
          Filter.atTop (nhds 0) := by
        have h := Filter.Tendsto.const_mul (3 / 4 : ℝ)
          tendsto_one_div_add_atTop_nhds_zero_nat
        rw [mul_zero] at h
        exact h
      refine squeeze_zero (fun i => le_of_lt (hrq0 i)) (fun i => ?_) hbase
      refine le_trans (hrqle i) ?_
      have h := hsqle i
      have h34 : (0:ℝ) < 3 / 4 := by norm_num
      nlinarith only [h, h34]
    -- ===================== STEP 3: THE CONVERGENT SUBSEQUENCE =======================
    -- eq:ff-unif and eq:ff-limharm.  `z_i → z_*` by Bolzano-Weierstrass (preamble) on the
    -- compact closed 3/4-ball; `U_i → U_∘` uniformly on the closed 7/8-ball by
    -- `EquiLipschitzUniformLimit` with `a = 0`, `ρ = 7/8` and `A = Λ = L` from eq:ff-lip;
    -- and `U_∘` is infinity-harmonic on the open 7/8-ball by `InfHarmonicStability`, whose
    -- hypothesis that each `U_i` is infinity-harmonic there is
    -- `NormalizedFamilyInfHarmonic` followed by `InfHarmonicMono` (the 7/8-ball sits inside
    -- the unit ball).  THIS IS THE FIRST CONSUMPTION OF BOTH NEW HELPERS.
    obtain ⟨ι, zstar, Ucirc, hι, hzstar, hzconv, hUunif, hUharm⟩ :
        ∃ (ι : ℕ → ℕ) (zstar : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          (Ucirc : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ),
          StrictMono ι ∧
          ‖zstar‖ ≤ 3 / 4 ∧
          Filter.Tendsto (fun k => zq (ι k)) Filter.atTop (nhds zstar) ∧
          TendstoUniformlyOn (fun k => Uq (ι k)) Ucirc Filter.atTop
            (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) ∧
          IsInfHarmonicOn
            (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) Ucirc := by
      -- the centers lie in the compact closed 3/4-ball
      have hzc : ∀ i, zq i ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) :=
        fun i => ball_subset_closedBall (hzq i)
      obtain ⟨zstar, hzstarmem, ι₁, hι₁, hz₁⟩ :=
        (isCompact_closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4)).tendsto_subseq hzc
      -- each member is bounded by `L` and `L`-Lipschitz on the closed 7/8-ball (eq:ff-lip)
      have hbd : ∀ k, ∀ w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
          |Uq (ι₁ k) w| ≤ L := fun k => (hLb (Uq (ι₁ k)) (hUq (ι₁ k))).1
      have hlip : ∀ k, ∀ w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
          ∀ w' ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
          |Uq (ι₁ k) w - Uq (ι₁ k) w'| ≤ L * ‖w - w'‖ :=
        fun k => (hLb (Uq (ι₁ k)) (hUq (ι₁ k))).2
      obtain ⟨ι₂, Ucirc, hι₂, hUunif₂⟩ :=
        EquiLipschitzUniformLimit (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) L L
          (by norm_num) (fun k => Uq (ι₁ k)) hbd hlip
      refine ⟨fun k => ι₁ (ι₂ k), zstar, Ucirc, hι₁.comp hι₂, ?_, ?_, hUunif₂, ?_⟩
      · rw [mem_closedBall, dist_zero_right] at hzstarmem; exact hzstarmem
      · exact hz₁.comp hι₂.tendsto_atTop
      -- the limit is infinity-harmonic there, by stability over the subsequence
      · refine InfHarmonicStability
          (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) isOpen_ball
          (fun k => Uq (ι₁ (ι₂ k))) Ucirc (fun k => ?_) (fun K hKsub hKc => ?_)
        · exact InfHarmonicMono (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1)
            (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) isOpen_ball
            (ball_subset_ball (by norm_num)) (Uq (ι₁ (ι₂ k)))
            (NormalizedFamilyInfHarmonic d (Uq (ι₁ (ι₂ k))) (hUq (ι₁ (ι₂ k))))
        · exact hUunif₂.mono (hKsub.trans ball_subset_closedBall)
    -- eq:ff-inside: `|z_*| + R ≤ 3/4 + 1/16 < 7/8` whenever `R ≤ 1/16`, so `z_* + R • X`
    -- stays in the closed 7/8-ball for `‖X‖ ≤ 1`.  This is what licenses both
    -- `AffineBlowups` at `z_*` in Step 5 and the rescaling in Step 6.
    have hinside : ∀ (Rv : ℝ), 0 < Rv → Rv ≤ 1 / 16 →
        ∀ X : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖X‖ ≤ 1 →
          zstar + Rv • X ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
      intro Rv hRv0 hRv16 X hX
      rw [mem_closedBall, dist_zero_right]
      have h1 : ‖zstar + Rv • X‖ ≤ ‖zstar‖ + ‖Rv • X‖ := norm_add_le _ _
      have h2 : ‖Rv • X‖ = Rv * ‖X‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hRv0)]
      have h3 : Rv * ‖X‖ ≤ Rv * 1 := mul_le_mul_of_nonneg_left hX (le_of_lt hRv0)
      rw [h2] at h1
      linarith only [h1, h3, hzstar, hRv16]
    -- ===================== STEPS 4, 5 AND 7: THE FURTHER EXTRACTIONS ================
    -- Three further "pass to a subsequence" steps, chained -- each extracts from the output
    -- of the previous -- so they share one hole, with every conclusion stated separately
    -- and labelled by its .tex equation.  Step 4 supplies the slow scales
    -- (eq:ff-slow, and `Rs ≤ 1/16` which is eq:ff-inside's hypothesis); Step 5 supplies
    -- `P0` and eq:ff-hatconv via `AffineBlowups` at `zstar` plus the Riesz step; Step 7
    -- supplies `Wlim` (eq:ff-Wconv, eq:ff-Web) via `EquiLipschitzUniformLimit` again, now
    -- with `a = 0`, `ρ = 2`, `A = 2L` and `Λ = L`.
    obtain ⟨j, Rs, Wlim, P0, hj, hRs0, hRs16, hslow, hhatconv,
        hWconv, hWcont, hW0, hWeb⟩ :=
      SlowScalesAndBlowupLimit d eb hebdef L hL0 hLb Uq zq rq hUq hzq hrq0 hrqlim
        ι hι zstar Ucirc hzstar hzconv hUunif hUharm hinside
    -- the composed index, used from here on
    obtain ⟨κ, hκdef⟩ : ∃ κ : ℕ → ℕ, κ = fun k => ι (j k) := ⟨_, rfl⟩
    have hκ : StrictMono κ := by rw [hκdef]; exact hι.comp hj
    -- ===================== STEP 6: THE THREE-POINT ESTIMATE AT THE SCALES `Rs` ======
    -- eq:ff-threepoint.  Each hatted blow-up is infinity-harmonic on `ball 0 1` by
    -- `NormalizedFamilyInfHarmonic`, `InfHarmonicMono`, `InfHarmonicRescale` and
    -- `InfHarmonicNormalize`; it is `L`-Lipschitz there by eq:ff-lip; and eq:ff-hatconv is
    -- exactly `ThreePointFlatness`'s flatness hypothesis for the slopes `P0` and the
    -- constants `0`, which is why that hypothesis is stated in the `∀ ε > 0, ∃ i₀` form.
    have tpf : ∀ ε' > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀,
        ∀ X ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 4),
        ∀ Y ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 4), X ≠ Y →
          |(Uq (κ k) (zstar + Rs k • X) - Uq (κ k) zstar) / Rs k
            + (Uq (κ k) (zstar + Rs k • Y) - Uq (κ k) zstar) / Rs k
            - 2 * ((Uq (κ k) (zstar + Rs k • ((2 : ℝ)⁻¹ • (X + Y))) - Uq (κ k) zstar)
                / Rs k)| ≤ ε' * ‖X - Y‖ := by
      simp only [hκdef]
      -- the rescaling map carries the OPEN unit ball strictly inside the 7/8-ball, which
      -- is what `InfHarmonicMono` needs after the rescaling
      have hstrict : ∀ (k : ℕ) (X : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), ‖X‖ < 1 →
          ‖zstar + Rs k • X‖ < 7 / 8 := by
        intro k X hX
        have h1 : ‖zstar + Rs k • X‖ ≤ ‖zstar‖ + ‖Rs k • X‖ := norm_add_le _ _
        have h2 : ‖Rs k • X‖ = Rs k * ‖X‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hRs0 k))]
        have h3 : Rs k * ‖X‖ < Rs k * 1 := mul_lt_mul_of_pos_left hX (hRs0 k)
        rw [h2] at h1
        linarith only [h1, h3, hzstar, hRs16 k]
      have hpre : ∀ k : ℕ, ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1 ⊆
          (fun Y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => zstar + Rs k • Y) ⁻¹'
            ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
        intro k X hX
        rw [mem_ball, dist_zero_right] at hX
        rw [Set.mem_preimage, mem_ball, dist_zero_right]
        exact hstrict k X hX
      -- (i) each hatted blow-up is infinity-harmonic on the unit ball
      have hharm : ∀ k : ℕ, IsInfHarmonicOn
          (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1)
          (fun X => (Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) zstar) / Rs k) := by
        intro k
        have h1 : IsInfHarmonicOn
            (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) (Uq (ι (j k))) :=
          InfHarmonicMono (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1)
            (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) isOpen_ball
            (ball_subset_ball (by norm_num)) (Uq (ι (j k)))
            (NormalizedFamilyInfHarmonic d (Uq (ι (j k))) (hUq (ι (j k))))
        have h2 := InfHarmonicRescale
          (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) (Uq (ι (j k))) h1
          zstar (Rs k) (hRs0 k)
        have h3 := InfHarmonicNormalize _ _ h2 (Uq (ι (j k)) zstar) (Rs k) (hRs0 k)
        exact InfHarmonicMono _ (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1)
          isOpen_ball (hpre k) _ h3
      -- (ii) each hatted blow-up is `L`-Lipschitz there, by eq:ff-lip at the same scale
      have hhatlip : ∀ k : ℕ,
          ∀ X ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1,
          ∀ Y ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1,
          |(Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) zstar) / Rs k
            - (Uq (ι (j k)) (zstar + Rs k • Y) - Uq (ι (j k)) zstar) / Rs k|
            ≤ L * ‖X - Y‖ := by
        intro k X hX Y hY
        rw [mem_ball, dist_zero_right] at hX hY
        have hA := hinside (Rs k) (hRs0 k) (hRs16 k) X (le_of_lt hX)
        have hB := hinside (Rs k) (hRs0 k) (hRs16 k) Y (le_of_lt hY)
        have hlip := (hLb (Uq (ι (j k))) (hUq (ι (j k)))).2 _ hA _ hB
        have hdn : ‖zstar + Rs k • X - (zstar + Rs k • Y)‖ = Rs k * ‖X - Y‖ := by
          rw [show zstar + Rs k • X - (zstar + Rs k • Y) = Rs k • (X - Y) from by module,
            norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hRs0 k))]
        rw [hdn] at hlip
        rw [div_sub_div_same,
          show Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) zstar
              - (Uq (ι (j k)) (zstar + Rs k • Y) - Uq (ι (j k)) zstar)
            = Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) (zstar + Rs k • Y) from by ring,
          abs_div, abs_of_pos (hRs0 k), div_le_iff₀ (hRs0 k)]
        linarith only [hlip]
      -- (iii) eq:ff-hatconv IS the flatness hypothesis, with slopes `P0` and constants `0`
      have hhatflat : ∀ ε' > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀,
          ∀ X ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1,
          |(Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) zstar) / Rs k
            - ((inner ℝ P0 X : ℝ) + 0)| ≤ ε' := by
        intro ε' hε'
        obtain ⟨k₀, hk₀⟩ := hhatconv ε' hε'
        refine ⟨k₀, fun k hk X hX => ?_⟩
        rw [add_zero]
        exact hk₀ k hk X hX
      exact ThreePointFlatness L
        (fun k X => (Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) zstar) / Rs k)
        (fun _ => P0) (fun _ => 0) hharm hhatlip hhatflat
    -- ===================== STEP 8: `Wlim` HAS VANISHING MIDPOINT DEFECT ==============
    -- eq:ff-midpoint, from `BlowupLimitVanishingMidpointDefect`.  Its two convergence
    -- hypotheses are eq:ff-slow and eq:ff-Wconv restated along the composed index `κ`;
    -- the substitution `X = (z_i - z_* + r_i H)/R_i` that turns Step 6's three-point
    -- estimate into the midpoint identity lives inside that node.
    have hslowκ : Filter.Tendsto
        (fun k => (‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k) Filter.atTop (nhds 0) := by
      simp only [hκdef]; exact hslow
    have hWconvκ : TendstoUniformlyOn
        (fun k Hv => (Uq (κ k) (zq (κ k) + rq (κ k) • Hv)
          - Uq (κ k) (zq (κ k))) / rq (κ k)) Wlim Filter.atTop
        (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2) := by
      simp only [hκdef]; exact hWconv
    have hmidpoint := BlowupLimitVanishingMidpointDefect d Uq zq rq Rs zstar Wlim κ
      hrq0 hRs0 hslowκ hWconvκ tpf
    -- ===================== STEP 9: `Wlim` IS LINEAR ==================================
    -- eq:ff-P, straight from `MidpointLinearOnBall` at `R = 2`.  That node internalises
    -- the .tex's two-ball bookkeeping (eq:ff-add lives on the 1-ball, eq:ff-half carries
    -- the conclusion back to the 2-ball), so no halving dance is re-derived here.
    obtain ⟨P, hP⟩ := MidpointLinearOnBall Wlim 2 (by norm_num) hWcont hW0 hmidpoint
    have hPne : P ≠ 0 := by
      intro hzero
      have hebmem : eb ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := by
        rw [mem_closedBall, dist_zero_right, hebdef]
        rw [WithLp.prod_norm_eq_of_L2]
        norm_num
      have h := hP eb hebmem
      rw [hzero, inner_zero_left, hWeb] at h
      norm_num at h
    -- ===================== STEP 10: THE CONTRADICTION ================================
    -- eq:ff-final: uniform convergence of the `W_i` to `Wlim = ⟪P, ·⟫` puts the affine
    -- error below `ε r_i` at some index.
    obtain ⟨k, hfinal⟩ : ∃ k : ℕ,
        ∀ H ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
          |Uq (κ k) (zq (κ k) + rq (κ k) • H) - Uq (κ k) (zq (κ k))
            - rq (κ k) * (inner ℝ P H : ℝ)| < ε * rq (κ k) := by
      -- the `κ` / `ι ∘ j` bridge: `hWconv` is stated along `ι (j k)`
      simp only [hκdef]
      obtain ⟨k, hk⟩ := (Metric.tendstoUniformlyOn_iff.mp hWconv ε hε).exists
      refine ⟨k, fun H hH => ?_⟩
      have hrk : 0 < rq (ι (j k)) := hrq0 (ι (j k))
      have h := hk H hH
      rw [Real.dist_eq, hP H hH] at h
      -- the two differ by the factor `r`, so the estimate transfers
      have hid : Uq (ι (j k)) (zq (ι (j k)) + rq (ι (j k)) • H) - Uq (ι (j k)) (zq (ι (j k)))
          - rq (ι (j k)) * (inner ℝ P H : ℝ)
          = -(rq (ι (j k)) * ((inner ℝ P H : ℝ)
            - (Uq (ι (j k)) (zq (ι (j k)) + rq (ι (j k)) • H) - Uq (ι (j k)) (zq (ι (j k)))) / rq (ι (j k)))) := by
        field_simp
        ring
      rw [hid, abs_neg, abs_mul, abs_of_nonneg (le_of_lt hrk)]
      calc rq (ι (j k)) * |(inner ℝ P H : ℝ)
            - (Uq (ι (j k)) (zq (ι (j k)) + rq (ι (j k)) • H) - Uq (ι (j k)) (zq (ι (j k)))) / rq (ι (j k))|
          < rq (ι (j k)) * ε := by
            exact mul_lt_mul_of_pos_left h hrk
        _ = ε * rq (ι (j k)) := by ring
    -- the cylinder of `FitCylinder` sits in the ball of radius `2 r`: its two components
    -- are orthogonal, so `‖Z - z‖² ≤ r² + λ r² ≤ 2 r²` using `λ < 1`.
    have hcyl : ∀ (z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (r lam : ℝ) (Q : WithLp 2
          (EuclideanSpace ℝ (Fin d) × ℝ)), 0 < r → lam < 1 → Q ≠ 0 →
        ∀ Z ∈ FitCylinder z r lam Q, ‖Z - z‖ ≤ 2 * r := by
      intro z r lam Q hr hlam hQ Z hZ
      obtain ⟨hax, htr⟩ := hZ
      obtain ⟨e, hedef⟩ : ∃ e : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          e = ‖Q‖⁻¹ • Q := ⟨_, rfl⟩
      have hQn : ‖Q‖ ≠ 0 := norm_ne_zero_iff.mpr hQ
      have hen : ‖e‖ = 1 := by
        rw [hedef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hQn]
      rw [← hedef] at hax htr
      obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = (inner ℝ e (Z - z) : ℝ) := ⟨_, rfl⟩
      rw [← htdef] at hax htr
      -- the orthogonal split: the axial and transverse components
      have horth : (inner ℝ (t • e) ((Z - z) - t • e) : ℝ) = 0 := by
        rw [inner_sub_right, real_inner_smul_left, real_inner_smul_left,
          real_inner_smul_right, real_inner_self_eq_norm_sq, hen, ← htdef]
        ring
      have hpyth : ‖Z - z‖ * ‖Z - z‖
          = ‖t • e‖ * ‖t • e‖ + ‖(Z - z) - t • e‖ * ‖(Z - z) - t • e‖ := by
        have h := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
        rw [show t • e + ((Z - z) - t • e) = Z - z from by abel] at h
        exact h
      have hte : ‖t • e‖ = |t| := by
        rw [norm_smul, Real.norm_eq_abs, hen, mul_one]
      have ht2 : |t| ^ 2 ≤ r ^ 2 := by
        have := abs_nonneg t
        nlinarith only [hax, this, hr]
      have hsq : (Real.sqrt lam) ^ 2 ≤ 1 := by
        rcases le_or_gt 0 lam with h | h
        · rw [Real.sq_sqrt h]; linarith only [hlam]
        · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt h)]; norm_num
      have htr2 : ‖(Z - z) - t • e‖ ^ 2 ≤ r ^ 2 := by
        have h0 : 0 ≤ Real.sqrt lam * r := mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hr)
        have h1 : ‖(Z - z) - t • e‖ ^ 2 ≤ (Real.sqrt lam * r) ^ 2 := by
          nlinarith only [htr, norm_nonneg ((Z - z) - t • e), h0]
        nlinarith only [h1, hsq, hr]
      rw [hte] at hpyth
      nlinarith only [hpyth, ht2, htr2, norm_nonneg (Z - z), hr]
    -- assembling the fit contradicts the badness of `lamq (κ k)`
    refine hlamqbad (κ k) ⟨P, hPne, ?_⟩
    intro Z hZ
    have hrk : 0 < rq (κ k) := hrq0 (κ k)
    have hlam1 : lamq (κ k) < 1 := (hlamq (κ k)).2
    have hlamε : ε < lamq (κ k) := (hlamq (κ k)).1
    have hZle := hcyl (zq (κ k)) (rq (κ k)) (lamq (κ k)) P hrk hlam1 hPne Z hZ
    obtain ⟨Hv, hHvdef⟩ : ∃ Hv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        Hv = (rq (κ k))⁻¹ • (Z - zq (κ k)) := ⟨_, rfl⟩
    have hHvmem : Hv ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := by
      rw [mem_closedBall, dist_zero_right, hHvdef, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hrk))]
      rw [inv_mul_le_iff₀ hrk]
      linarith only [hZle]
    have hZeq : zq (κ k) + rq (κ k) • Hv = Z := by
      rw [hHvdef, smul_smul, mul_inv_cancel₀ (ne_of_gt hrk), one_smul]
      abel
    have hinner : rq (κ k) * (inner ℝ P Hv : ℝ) = (inner ℝ P (Z - zq (κ k)) : ℝ) := by
      rw [hHvdef, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt hrk),
        one_mul]
    have h := hfinal Hv hHvmem
    rw [hZeq, hinner] at h
    have hεr : ε * rq (κ k) ≤ lamq (κ k) * rq (κ k) :=
      mul_le_mul_of_nonneg_right (le_of_lt hlamε) (le_of_lt hrk)
    linarith only [h, hεr]
  refine ⟨s₀, hs₀pos, hs₀le, ?_⟩
  intro s hs hss₀
  rw [FlatnessModulus]
  refine Real.sSup_le ?_ (le_of_lt hε)
  rintro b ⟨U, z, r, hU, hz, hr, hrle, rfl⟩
  exact hbd s hs hss₀ U z r hU hz hr hrle
