import InfHarmonic.PowerDecay
import InfHarmonic.DyadicFitTaylorEstimate
import InfHarmonic.NormalizedFamilyLipschitz
import InfHarmonic.CylinderFitSlopeBounds
import InfHarmonic.TaylorToHolderGradient
import InfHarmonic.HolderSeminormOn
import InfHarmonic.InfHarmonicNormalize
open Metric Set WithLp

/-- Theorem 1.1 (uniform interior estimate): for every `d ≥ 3` there are
`α ∈ (0, 1/3]` and `C < ∞`, depending only on `d`, such that every bounded
infinity-harmonic function on the unit ball has a gradient on the half ball
whose supremum and `α`-Hölder seminorm add up to at most `C` times the
oscillation of the function on the unit ball. The existence of the gradient
field together with the boundedness of its Hölder quotients is the
`C^{1,α}(B_{1/2})` membership; the `BddAbove` hypotheses are the guards the two
`sSup`-valued quantities need. -/
theorem MainEstimate (d : ℕ) (hd : 3 ≤ d) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 3 ∧ 0 < C ∧
      ∀ u : EuclideanSpace ℝ (Fin d) → ℝ,
        IsInfHarmonicOn (ball 0 1) u →
        BddAbove (u '' ball 0 1) → BddBelow (u '' ball 0 1) →
        ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), HasGradientAt u (g x) x) ∧
          BddAbove ((fun x => ‖g x‖) '' ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ∧
          BddAbove (HolderQuotSet g α (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))) ∧
          sSup ((fun x => ‖g x‖) '' ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
              + HolderSeminormOn g α (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
            ≤ C * OscOn u (ball 0 1) := by
  classical
  -- ===================================================================
  -- PROOF MAP (burst 605).  THE NODE IS CLOSED: zero `sorry`, and
  -- `#print axioms MainEstimate` = `[propext, Classical.choice, Quot.sound]`.
  -- Measured heartbeats: passes at 100000, fails at 50000, so the DEFAULT 200000 budget is
  -- already about twice the bracket and no `set_option` is carried.
  -- The paper's ten steps, and where each one lives.
  --
  -- CITED, not proved here:
  --   Step 1 (part)  `PowerDecay` and `NormalizedFamilyLipschitz` supply `B, γ, s₀` and
  --                  `L`; the constants `A₀, r₀, α, ρ₀` are then definitions.
  --   Steps 5-6      LIFTED to `DyadicFitTaylorEstimate`.  That node is the
  --                  consecutive-slope comparison, the geometric tail and the exponent
  --                  identity `(1 + γ/2)α = γ/2`; it is stated over `(A₀, γ, r₀)` and a
  --                  single `(U, z, P)`, with no family, no centre set and no dimension,
  --                  which is pm-0040's test on the parameter list.
  --   Step 8         `TaylorToHolderGradient`, applied ONCE before the family member is
  --                  fixed -- its `C'` is produced before `S`, `U`, `g`, which is exactly
  --                  the "one Hölder constant for the whole family" of
  --                  eq:me-family-conclusion.  ONE TRAP: it reuses the SAME `C` for the
  --                  Taylor bound and for the slope bound `∀ z ∈ S, ‖g z‖ ≤ C`, so the
  --                  two have to be MERGED into one constant (`CM`) before it is applied.
  --                  Its Hölder conclusion carries NO distance restriction, so
  --                  paper.tex:806-820's `ρ₀/2` case split and the trivial `|∇U| ≤ L` arm
  --                  for larger distances are inside THAT node, not here.
  --
  -- PROVED HERE, with what each block actually turns on:
  --   `hconst`    Step 1's elementary properties.  The only real work is `A₀ r₀^γ ≤ 1/2`,
  --               and it is ONE exponent identity -- `((2A₀)^{-1/γ})^γ = (2A₀)⁻¹`, by
  --               `← Real.rpow_mul` then `Real.rpow_neg_one` -- proved once and rewritten
  --               with, exactly as in `DyadicFitTaylorEstimate`.  `r₀ ≤ 3/8` is a real
  --               third entry in the `min`: it is what keeps `z + h` inside
  --               `closedBall 0 (7/8)`, where `NormalizedFamilyLipschitz` applies, and it
  --               does no other job.
  --   `hballfit`  Steps 2, 3, 4 and 7 together, in the exact shape Steps 5-6 consume.
  --               Four things worth keeping:
  --                 * eq:me-dist needs only the LOWER bound `D(z) ≥ 1/4`, not
  --                   `BadScales`' equality `D = 3/4 - ‖z‖`: `frontier (ball 0 (3/4))` is
  --                   the sphere, nonempty because the space is nontrivial, and
  --                   `le_infDist` plus `norm_sub_norm_le` finish it in four lines.
  --                 * Step 3 is a CONTRADICTION on goodness, and its spine is two
  --                   `le_csSup`s whose `BddAbove` witnesses are inline (`⟨1, …⟩` from
  --                   `BetaFlatness ≤ 1`) -- so no nonemptiness anywhere (pm-0026).  The
  --                   admissible triple is at `s = r_j / D(z)`, where `r_j ≤ s·D(z)` holds
  --                   with EQUALITY, which is why `D(z) ≠ 0` has to come first.  `s ≤ s₀`
  --                   is what the first entry `(1/4)·min(s₀,1/8)` of `r₀` is for.
  --                 * Step 4 turns on the EXACT identity `ρ_j = √λ_j · r_j`: one rpow
  --                   step, `√(r^γ) = r^{γ/2}`, and then `FitCylinder` membership is the
  --                   axial bound (Cauchy-Schwarz plus `√λ_j ≤ 1`) and the transverse
  --                   bound (the projection shrinks), both from `‖h‖ ≤ √λ_j r_j`.
  --                 * `CylinderFitSlopeBounds`' Lipschitz slot is the INCREMENT form, and
  --                   `NormalizedFamilyLipschitz`' two-point bound supplies it at
  --                   `a = z+h`, `b = z`.
  --   `hgrad`     Steps 5-7 packaged per family member.  Step 7's `‖P_∞(z)‖ ≤ L+1` is the
  --               `j → ∞` LIMIT of `‖P_j‖ ≤ L+1` against the tail bound, and the only way
  --               to take that limit cheaply is to put the dyadic factor into NATURAL
  --               powers first: `((1/2)^j r₀)^{γ/2} = ((1/2)^{γ/2})^j · r₀^{γ/2}`, the
  --               `hpowbase`/`hsplit` pair copied from `DyadicFitTaylorEstimate`, and then
  --               `tendsto_pow_atTop_nhds_zero_of_lt_one` with `ge_of_tendsto'`.  Keeping
  --               `L+1` rather than the cheaper `L+1+CT r₀^{γ/2}` is what makes `CM` and
  --               the final `C = L+1+C'` match Step 8 and Step 10 of the `.tex` exactly.
  --   `hslice`    Steps 9 and 10 -- eq:me-final-bounds.  Three parts, each with its own
  --               pivot:
  --                 * THE SLICE TRANSFER.  `ι y = (y,0)` is built as a CONTINUOUS LINEAR
  --                   MAP (`prodContinuousLinearEquiv 2 ℝ _ _`.symm composed with
  --                   `ContinuousLinearMap.inl`), because `HasFDerivAt.comp` needs that and
  --                   so does the inner-product computation.  The chain is
  --                   `HasGradientAt U (G w) w` at `w = ι y`
  --                     → `HasFDerivAt U (toDual (G w)) w`   (`hasGradientAt_iff_hasFDerivAt`,
  --                       which is `Iff.rfl`)
  --                     → `HasFDerivAt (U ∘ ι) ((toDual (G w)).comp ι) y`
  --                     → `HasFDerivAt v …` by `congr_of_eventuallyEq`, since
  --                       `U (ι y') = v y'`
  --                     → recognize `(toDual (G w)).comp ι = toDual ((ofLp (G w)).1)`.
  --                   That last step is eq:me-slice-inner and it is PURE DEFEQ:
  --                   `WithLp.prod_inner_apply` is `rfl` and its second summand dies at
  --                   the time-zero point, so `ext h; exact hinner …` closes it -- pm-0035
  --                   says do NOT reach for `simpa` here.
  --                 * THE TWO sSup TERMS.  Do NOT pull `M` out of either `sSup`:
  --                   `sSup (M • A) = M · sSup A` needs `A` nonempty and that is avoidable
  --                   work.  Bound each `sSup` DIRECTLY at the already-scaled constant --
  --                   `‖g x‖ = M‖q x‖ ≤ M(L+1)` and
  --                   `‖g x - g y‖ / dist x y ^ α ≤ M C'` -- with `Real.sSup_le`, whose
  --                   hypotheses are `(∀ x ∈ s, x ≤ a)` and `0 ≤ a` and which takes NO
  --                   nonemptiness witness, the junk value `sSup ∅ = 0` satisfying the
  --                   goal (pm-0026).  The quotient bound needs `dist x y ^ α > 0`, which
  --                   is available because `HolderQuotSet` only admits `x ≠ y`.
  --                 * THE `M = 0` BRANCH, separate and with no paper sentence behind it
  --                   (paper.tex:822 treats `M > 0` only).  `OscOn u = 0` with the two
  --                   `Bdd` hypotheses makes `u` constant on the unit ball, `g ≡ 0` is
  --                   differentiable there because `ball 0 1` is a NEIGHBOURHOOD of each
  --                   `x ∈ ball 0 (1/2)` (`isOpen_ball.mem_nhds` plus
  --                   `hasFDerivAt_const … |>.congr_of_eventuallyEq`), and both `sSup`s
  --                   are `≤ 0` by the same `Real.sSup_le` at `a = 0`.
  --                 * THE DESCENT for `M > 0`.  `InfHarmonicNormalize Ω u hu c M hM` gives
  --                   `IsInfHarmonicOn Ω ((u · - c)/M)` with no reshaping.  The two `Bdd`
  --                   guards and `OscOn v ≤ 1` all come from the single monotonicity fact
  --                   `a ≤ b → (a-c)/M ≤ (b-c)/M`, used with `le_csSup`/`csInf_le` for the
  --                   guards and with `csSup_le`/`le_csInf` for the oscillation; the
  --                   oscillation is then `(sSup u - sInf u)/M = M/M = 1`, so the `v`-side
  --                   `sSup`/`sInf` are only ever BOUNDED, never computed.
  -- ===================================================================
  -- Step 1: the constants.  `PowerDecay` and `NormalizedFamilyLipschitz` are citations.
  have hd1 : 1 ≤ d := by omega
  obtain ⟨B, gam, s₀, hB0, hgam0, hgam1, hs₀0, hs₀1, hpower⟩ := PowerDecay d hd1
  obtain ⟨L, hL0, hLip⟩ := NormalizedFamilyLipschitz d hd1
  obtain ⟨A₀, hA₀def⟩ : ∃ A₀ : ℝ, A₀ = B * (4 : ℝ) ^ gam + 1 := ⟨_, rfl⟩
  obtain ⟨al, haldef⟩ : ∃ al : ℝ, al = gam / (2 + gam) := ⟨_, rfl⟩
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀ : ℝ,
      r₀ = min (min (1 / 4 * min s₀ (1 / 8)) ((2 * A₀) ^ (-(1 / gam)))) (3 / 8) := ⟨_, rfl⟩
  obtain ⟨rho₀, hrho₀def⟩ : ∃ rho₀ : ℝ,
      rho₀ = Real.sqrt A₀ * r₀ ^ (1 + gam / 2) := ⟨_, rfl⟩
  -- eq:me-lambda-small and the elementary bounds, all depending only on `d`.  The one
  -- piece of real rpow work is `A₀ r₀^γ ≤ 1/2`, and it is ONE exponent identity --
  -- `((2A₀)^{-1/γ})^γ = (2A₀)⁻¹` -- proved once and then rewritten with.
  obtain ⟨hA₀0, hA₀1, hr₀0, hr₀38, hlamsmall, hal0, hal3⟩ :
      0 < A₀ ∧ 1 ≤ A₀ ∧ 0 < r₀ ∧ r₀ ≤ 3 / 8 ∧ A₀ * r₀ ^ gam ≤ 1 / 2 ∧
        0 < al ∧ al ≤ 1 / 3 := by
    have h4pos : (0 : ℝ) < (4 : ℝ) ^ gam := Real.rpow_pos_of_pos (by norm_num) gam
    have hBA : (0 : ℝ) < B * (4 : ℝ) ^ gam := mul_pos hB0 h4pos
    have hA₀0 : 0 < A₀ := by rw [hA₀def]; linarith only [hBA]
    have hA₀1 : (1 : ℝ) ≤ A₀ := by rw [hA₀def]; linarith only [hBA]
    have h2A0 : (0 : ℝ) < 2 * A₀ := by linarith only [hA₀0]
    have hc0 : (0 : ℝ) < (2 * A₀) ^ (-(1 / gam)) := Real.rpow_pos_of_pos h2A0 _
    have hr₀0 : 0 < r₀ := by
      rw [hr₀def]
      refine lt_min (lt_min ?_ hc0) (by norm_num)
      have hm := lt_min hs₀0 (show (0 : ℝ) < 1 / 8 by norm_num)
      linarith only [hm]
    have hr₀38 : r₀ ≤ 3 / 8 := by rw [hr₀def]; exact min_le_right _ _
    have hr₀c : r₀ ≤ (2 * A₀) ^ (-(1 / gam)) := by
      rw [hr₀def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
    have hkey : ((2 * A₀) ^ (-(1 / gam))) ^ gam = (2 * A₀)⁻¹ := by
      rw [← Real.rpow_mul (le_of_lt h2A0),
        show -(1 / gam) * gam = (-1 : ℝ) from by field_simp]
      exact Real.rpow_neg_one _
    have hlamsmall : A₀ * r₀ ^ gam ≤ 1 / 2 := by
      have h1 : r₀ ^ gam ≤ ((2 * A₀) ^ (-(1 / gam))) ^ gam :=
        Real.rpow_le_rpow (le_of_lt hr₀0) hr₀c (le_of_lt hgam0)
      rw [hkey] at h1
      have h2 : A₀ * r₀ ^ gam ≤ A₀ * (2 * A₀)⁻¹ :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hA₀0)
      have h3 : A₀ * (2 * A₀)⁻¹ = 1 / 2 := by field_simp
      linarith only [h2, h3]
    have hal0 : 0 < al := by
      rw [haldef]; exact div_pos hgam0 (by linarith only [hgam0])
    have hal3 : al ≤ 1 / 3 := by
      rw [haldef, div_le_iff₀ (by linarith only [hgam0] : (0 : ℝ) < 2 + gam)]
      linarith only [hgam1]
    exact ⟨hA₀0, hA₀1, hr₀0, hr₀38, hlamsmall, hal0, hal3⟩
  have hrho₀0 : 0 < rho₀ := by
    rw [hrho₀def]
    exact mul_pos (Real.sqrt_pos.mpr hA₀0) (Real.rpow_pos_of_pos hr₀0 _)
  -- ===================== STEPS 2, 3, 4 AND 7 ==================================
  -- The fit on the inscribed ball at every dyadic scale, with its slope bounded by `L+1`.
  -- This is the exact interface `DyadicFitTaylorEstimate` consumes.
  -- the orthogonal projection shrinks the norm, needed twice in Step 4
  have hprojle : ∀ nn x : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖nn‖ = 1 →
      ‖x - (inner ℝ nn x : ℝ) • nn‖ ≤ ‖x‖ := by
    intro nn x hnn
    obtain ⟨sv, hsvdef⟩ : ∃ sv : ℝ, sv = (inner ℝ nn x : ℝ) := ⟨_, rfl⟩
    rw [← hsvdef]
    have horth : (inner ℝ (x - sv • nn) (sv • nn) : ℝ) = 0 := by
      rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hnn]
      have hxe : (inner ℝ x nn : ℝ) = sv := by rw [hsvdef, real_inner_comm]
      rw [hxe]; ring
    have hsum : x = (x - sv • nn) + sv • nn := by abel
    have hpyth := norm_add_sq_real (x - sv • nn) (sv • nn)
    rw [← hsum, horth] at hpyth
    have h1 : ‖x - sv • nn‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      linarith only [hpyth, sq_nonneg ‖sv • nn‖]
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h1
  -- eq:me-dist: `D(z) ≥ d₀ = 1/4` on the half ball.  The frontier is the sphere of
  -- radius `3/4`, nonempty because the space is nontrivial, and every point of it is at
  -- distance at least `3/4 - ‖z‖ ≥ 1/4` from `z`.
  have hDz : ∀ zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖zv‖ ≤ 1 / 2 →
      (1 : ℝ) / 4 ≤ infDist zv
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) := by
    intro zv hzv
    rw [frontier_ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      (by norm_num : (3 : ℝ) / 4 ≠ 0)]
    have hne : (Metric.sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        (3 / 4)).Nonempty := by
      obtain ⟨vv, hvv⟩ := exists_ne (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      have hvn : ‖vv‖ ≠ 0 := norm_ne_zero_iff.mpr hvv
      refine ⟨(3 / 4 * ‖vv‖⁻¹) • vv, ?_⟩
      rw [mem_sphere_iff_norm, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ hvn, mul_one]
    rw [le_infDist hne]
    intro w hw
    rw [mem_sphere_iff_norm, sub_zero] at hw
    rw [dist_eq_norm, norm_sub_rev]
    have h := norm_sub_norm_le w zv
    rw [hw] at h
    linarith only [h, hzv]
  -- the defining set of `b_d(s)` is bounded above by `1`, which is all the `≤ b_d(s)`
  -- comparison needs (pm-0026: no nonemptiness)
  have hbeta1 : ∀ (u : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
      BetaFlatness u zv rv ≤ 1 := by
    intro u zv rv
    rw [BetaFlatness]
    exact Real.sSup_le (fun x hx => le_of_lt hx.1.2) zero_le_one
  have hbdd : ∀ s : ℝ, BddAbove {b : ℝ |
      ∃ (U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
        (zv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rv : ℝ),
      NormalizedInfFamily d U ∧
      zv ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
      0 < rv ∧
      rv ≤ s * infDist zv
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
      b = BetaFlatness U zv rv} := by
    intro s
    refine ⟨1, fun x hx => ?_⟩
    obtain ⟨U, zv, rv, -, -, -, -, rfl⟩ := hx
    exact hbeta1 U zv rv
  have hballfit : ∀ U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      NormalizedInfFamily d U →
      ∀ z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2),
      ∀ j : ℕ, ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        (∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          ‖h‖ ≤ Real.sqrt A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam / 2) →
          |U (z + h) - U z - (inner ℝ P h : ℝ)|
            ≤ A₀ * ((1 / 2 : ℝ) ^ j * r₀) ^ (1 + gam)) ∧
        ‖P‖ ≤ L + 1 := by
    intro U hU z hz j
    rw [mem_closedBall, dist_zero_right] at hz
    obtain ⟨rj, hrjdef⟩ : ∃ rj : ℝ, rj = (1 / 2 : ℝ) ^ j * r₀ := ⟨_, rfl⟩
    have hrj0 : 0 < rj := by
      rw [hrjdef]; exact mul_pos (by positivity) hr₀0
    have hrjle : rj ≤ r₀ := by
      rw [hrjdef]
      have h1 : ((1 : ℝ) / 2) ^ j ≤ 1 :=
        pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 ≤ 1)
      nlinarith only [h1, hr₀0]
    obtain ⟨lamj, hlamjdef⟩ : ∃ lamj : ℝ, lamj = A₀ * rj ^ gam := ⟨_, rfl⟩
    have hlamj0 : 0 < lamj := by
      rw [hlamjdef]; exact mul_pos hA₀0 (Real.rpow_pos_of_pos hrj0 gam)
    have hlamjhalf : lamj ≤ 1 / 2 := by
      rw [hlamjdef]
      have h1 : rj ^ gam ≤ r₀ ^ gam :=
        Real.rpow_le_rpow (le_of_lt hrj0) hrjle (le_of_lt hgam0)
      have h2 : A₀ * rj ^ gam ≤ A₀ * r₀ ^ gam :=
        mul_le_mul_of_nonneg_left h1 (le_of_lt hA₀0)
      linarith only [h2, hlamsmall]
    have hsqlam1 : Real.sqrt lamj ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith only [hlamjhalf])
    have hsqlam0 : 0 < Real.sqrt lamj := Real.sqrt_pos.mpr hlamj0
    -- STEP 3: `λ_j = A₀ r_j^γ` is GOOD at `(z, r_j)`.  Contradiction on goodness: if not,
    -- `λ_j` sits in `β`'s defining set, so `λ_j ≤ β ≤ b_d(s) ≤ B s^γ ≤ B 4^γ r_j^γ < λ_j`.
    have hzG : z ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) := by
      rw [mem_ball, dist_zero_right]; linarith only [hz]
    have hDzv := hDz z hz
    obtain ⟨sv, hsvdef⟩ : ∃ sv : ℝ, sv = rj / infDist z
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) :=
      ⟨_, rfl⟩
    have hDpos : (0 : ℝ) < infDist z
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) := by
      linarith only [hDzv]
    have hsv0 : 0 < sv := by rw [hsvdef]; exact div_pos hrj0 hDpos
    have hsv4 : sv ≤ 4 * rj := by
      rw [hsvdef, div_le_iff₀ hDpos]
      nlinarith only [hDzv, hrj0]
    have hsvs₀ : sv ≤ s₀ := by
      have h1 : 4 * rj ≤ 4 * r₀ := by linarith only [hrjle]
      have h2 : r₀ ≤ 1 / 4 * min s₀ (1 / 8) := by
        rw [hr₀def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
      have h3 : min s₀ (1 / 8) ≤ s₀ := min_le_left _ _
      linarith only [hsv4, h1, h2, h3]
    have hgoodj : ∃ P, IsCylinderFit U z rj lamj P := by
      by_contra hno
      have hmem : lamj ∈ {lam : ℝ | lam ∈ Set.Ioo (0 : ℝ) 1 ∧
          ¬ ∃ P : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit U z rj lam P} :=
        ⟨⟨hlamj0, by linarith only [hlamjhalf]⟩, hno⟩
      have hle1 : lamj ≤ BetaFlatness U z rj := by
        rw [BetaFlatness]
        exact le_csSup ⟨1, fun x hx => le_of_lt hx.1.2⟩ hmem
      have hle2 : BetaFlatness U z rj ≤ FlatnessModulus d hd1 sv := by
        rw [FlatnessModulus]
        refine le_csSup (hbdd sv) ⟨U, z, rj, hU, hzG, hrj0, ?_, rfl⟩
        rw [hsvdef]
        refine le_of_eq ?_
        field_simp
      have hle3 : FlatnessModulus d hd1 sv ≤ B * sv ^ gam := hpower sv hsv0 hsvs₀
      have hle4 : B * sv ^ gam ≤ B * (4 * rj) ^ gam := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hB0)
        exact Real.rpow_le_rpow (le_of_lt hsv0) hsv4 (le_of_lt hgam0)
      have hle5 : B * (4 * rj) ^ gam = B * (4 : ℝ) ^ gam * rj ^ gam := by
        rw [Real.mul_rpow (by norm_num) (le_of_lt hrj0)]; ring
      have hlt : B * (4 : ℝ) ^ gam * rj ^ gam < lamj := by
        rw [hlamjdef, hA₀def]
        have hrp : (0 : ℝ) < rj ^ gam := Real.rpow_pos_of_pos hrj0 gam
        nlinarith only [hrp]
      linarith only [hle1, hle2, hle3, hle4, hle5, hlt]
    obtain ⟨P, hP0, hPfit⟩ := hgoodj
    have hPn : (0 : ℝ) < ‖P‖ := norm_pos_iff.mpr hP0
    have hnn : ‖‖P‖⁻¹ • P‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hPn)), inv_mul_cancel₀ (ne_of_gt hPn)]
    -- STEP 4: `ρ_j = √A₀ r_j^{1+γ/2}` is EXACTLY `√λ_j r_j`, the cylinder's transverse
    -- radius.  The one rpow step is `√(r^γ) = r^{γ/2}`, proved once here.
    have hsqrj : Real.sqrt (rj ^ gam) = rj ^ (gam / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hrj0)]
      congr 1
      ring
    have hrhoid : Real.sqrt A₀ * rj ^ (1 + gam / 2) = Real.sqrt lamj * rj := by
      rw [hlamjdef, Real.sqrt_mul (le_of_lt hA₀0), hsqrj,
        show (1 : ℝ) + gam / 2 = gam / 2 + 1 from by ring, Real.rpow_add hrj0,
        Real.rpow_one]
      ring
    have hlamrj : lamj * rj = A₀ * rj ^ (1 + gam) := by
      rw [hlamjdef, show (1 : ℝ) + gam = gam + 1 from by ring, Real.rpow_add hrj0,
        Real.rpow_one]
      ring
    -- STEP 7: `‖P‖ ≤ L + √λ_j ≤ L + 1`, via `CylinderFitSlopeBounds`.  Its Lipschitz slot
    -- is the INCREMENT form, and `r₀ ≤ 3/8` is exactly what keeps `z + h` inside
    -- `closedBall 0 (7/8)` where `NormalizedFamilyLipschitz` applies.
    have hLipU := hLip U hU
    have hLinc : ∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖h‖ ≤ rj →
        |U (z + h) - U z| ≤ L * ‖h‖ := by
      intro h hh
      have hzb : z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
        rw [mem_closedBall, dist_zero_right]; linarith only [hz]
      have hzhb : z + h ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          (7 / 8) := by
        rw [mem_closedBall, dist_zero_right]
        have h1 := norm_add_le z h
        linarith only [h1, hz, hh, hrjle, hr₀38]
      have h2 := hLipU.2 (z + h) hzhb z hzb
      rw [show z + h - z = h from by abel] at h2
      exact h2
    have hslope := CylinderFitSlopeBounds d hd1 U hU L z rj lamj hrj0 hlamj0
      (by linarith only [hlamjhalf]) hLinc P ⟨hP0, hPfit⟩
    refine ⟨P, ?_, by linarith only [hslope.1, hsqlam1]⟩
    -- the ball fit: membership in `FitCylinder` is two bounds, both from `‖h‖ ≤ √λ_j r_j`
    intro h hh
    rw [← hrjdef] at hh
    rw [hrhoid] at hh
    have hmemcyl : z + h ∈ FitCylinder z rj lamj P := by
      rw [FitCylinder, Set.mem_ofPred_eq, show z + h - z = h from by abel]
      refine ⟨?_, ?_⟩
      · have hcs := abs_real_inner_le_norm (‖P‖⁻¹ • P) h
        rw [hnn, one_mul] at hcs
        nlinarith only [hcs, hh, hsqlam1, hsqlam0, hrj0]
      · refine le_trans (hprojle (‖P‖⁻¹ • P) h hnn) ?_
        exact hh
    have hb := hPfit (z + h) hmemcyl
    rw [show z + h - z = h from by abel, hlamrj, hrjdef] at hb
    exact hb
  -- ===================== STEPS 5 AND 6: THE CITATION ==========================
  obtain ⟨CT, hCT0, hdyadic⟩ := DyadicFitTaylorEstimate
    (E := WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) A₀ gam r₀ hA₀0 hgam0 hr₀0
  -- the limiting slope field, for each family member.  Step 7's `‖P_∞(z)‖ ≤ L+1` is the
  -- `j → ∞` limit of `‖P_j‖ ≤ L+1` against the tail bound, so the dyadic factor is first
  -- put into NATURAL powers -- the `DyadicFitTaylorEstimate` idiom, reused verbatim.
  have hhalf0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hpowbase : ∀ (p : ℝ) (j : ℕ), ((1 / 2 : ℝ) ^ j) ^ p = ((1 / 2 : ℝ) ^ p) ^ j := by
    intro p j
    rw [← Real.rpow_natCast ((1 / 2 : ℝ)) j, ← Real.rpow_natCast ((1 / 2 : ℝ) ^ p) j,
      ← Real.rpow_mul hhalf0, ← Real.rpow_mul hhalf0, mul_comm (j : ℝ) p]
  have hsplit : ∀ (p : ℝ) (j : ℕ),
      ((1 / 2 : ℝ) ^ j * r₀) ^ p = ((1 / 2 : ℝ) ^ p) ^ j * r₀ ^ p := by
    intro p j
    rw [Real.mul_rpow (by positivity) (le_of_lt hr₀0), hpowbase p j]
  have hq0 : (0 : ℝ) < (1 / 2 : ℝ) ^ (gam / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : (1 / 2 : ℝ) ^ (gam / 2) < 1 :=
    Real.rpow_lt_one hhalf0 (by norm_num) (by linarith only [hgam0])
  have hgrad : ∀ U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      NormalizedInfFamily d U →
      ∃ G : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)
          → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        (∀ z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2),
          ∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖h‖ ≤ rho₀ →
            |U (z + h) - U z - (inner ℝ (G z) h : ℝ)| ≤ CT * ‖h‖ ^ (1 + al)) ∧
        (∀ z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2),
          ‖G z‖ ≤ L + 1) := by
    intro U hU
    have hex : ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        ∃ Pz : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2) →
          (∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖h‖ ≤ rho₀ →
            |U (z + h) - U z - (inner ℝ Pz h : ℝ)| ≤ CT * ‖h‖ ^ (1 + al)) ∧
          ‖Pz‖ ≤ L + 1 := by
      intro z
      by_cases hz : z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2)
      · -- choose a fitted slope at every dyadic scale, then pass to the limit
        choose P hPfit hPbd using fun j => hballfit U hU z hz j
        obtain ⟨Pinf, htail, htaylor⟩ := hdyadic U z P hPfit
        refine ⟨Pinf, fun _ => ⟨?_, ?_⟩⟩
        · intro h hh
          have h1 := htaylor h (by rw [hrho₀def] at hh; exact hh)
          rw [haldef]
          exact h1
        · -- `‖P_j‖ ≤ L+1` at every `j`, and `‖P_j - P_∞‖ ≤ CT r₀^{γ/2} q^j → 0`
          have hbdj : ∀ j : ℕ,
              ‖Pinf‖ ≤ L + 1 + CT * r₀ ^ (gam / 2) * ((1 / 2 : ℝ) ^ (gam / 2)) ^ j := by
            intro j
            have h0 := htail j
            rw [hsplit (gam / 2) j] at h0
            have hb := hPbd j
            have htri : ‖Pinf‖ ≤ ‖P j‖ + ‖P j - Pinf‖ := by
              have h := norm_sub_le (P j) (P j - Pinf)
              rw [sub_sub_cancel] at h
              linarith only [h]
            nlinarith only [htri, hb, h0]
          have hlim : Filter.Tendsto
              (fun j : ℕ => L + 1 + CT * r₀ ^ (gam / 2) * ((1 / 2 : ℝ) ^ (gam / 2)) ^ j)
              Filter.atTop (nhds (L + 1)) := by
            have ht := tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hq0) hq1
            have h3 := (ht.const_mul (CT * r₀ ^ (gam / 2))).const_add (L + 1)
            rw [show L + 1 + CT * r₀ ^ (gam / 2) * 0 = L + 1 from by ring] at h3
            exact h3
          exact ge_of_tendsto' hlim hbdj
      · exact ⟨0, fun h => absurd h hz⟩
    choose G hG using hex
    exact ⟨G, fun z hz => (hG z hz).1, fun z hz => (hG z hz).2⟩
  -- ===================== STEP 8: ONE HÖLDER CONSTANT FOR THE FAMILY ===========
  -- `TaylorToHolderGradient` produces `C'` BEFORE `S`, `U` and `g`, so it is applied once
  -- here, outside the family quantifier.  Its single `C` slot has to cover BOTH the
  -- Taylor constant `CT` and the slope bound `L + 1`, so they are merged.
  obtain ⟨CM, hCMdef⟩ : ∃ CM : ℝ, CM = max CT (L + 1) := ⟨_, rfl⟩
  have hCM0 : 0 < CM := by
    rw [hCMdef]; exact lt_of_lt_of_le hCT0 (le_max_left _ _)
  obtain ⟨C', hC'0, hholder⟩ := TaylorToHolderGradient
    (E := WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) al CM rho₀ hal0
    (by linarith only [hal3]) hCM0 hrho₀0
  -- ===================== STEP 9: THE TIME-ZERO SLICE ==========================
  -- `ι y = (y, 0)` as a CONTINUOUS LINEAR MAP: that is what the chain rule needs, and it
  -- also carries the Riesz identification `⟪P, ι h⟫ = ⟪P_x, h⟫`.
  obtain ⟨iota, hiota⟩ : ∃ iota : EuclideanSpace ℝ (Fin d) →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      ∀ y : EuclideanSpace ℝ (Fin d), iota y = toLp 2 (y, (0 : ℝ)) :=
    ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin d))
          ℝ).symm.toContinuousLinearMap.comp
        (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ),
      fun _ => rfl⟩
  -- eq:me-slice-inner.  `WithLp.prod_inner_apply` is `rfl`, and its second summand dies at
  -- the time-zero point, so this is a pure defeq bridge (pm-0035: `exact`, not `simpa`).
  have hinner : ∀ (Pv : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      (h : EuclideanSpace ℝ (Fin d)),
      (inner ℝ Pv (iota h) : ℝ) = (inner ℝ (ofLp Pv).1 h : ℝ) := by
    intro Pv h
    rw [hiota h, WithLp.prod_inner_apply]
    simp
  -- the spatial projection never increases the space-time norm
  have hfstle : ∀ Z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖(ofLp Z).1‖ ≤ ‖Z‖ := by
    intro Z
    have h : ‖Z‖ ^ 2 = ‖(ofLp Z).1‖ ^ 2 + ‖(ofLp Z).2‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 Z
    have h1 : ‖(ofLp Z).1‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
      nlinarith only [h, sq_nonneg ‖(ofLp Z).2‖]
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h1
  have hmem : ∀ y : EuclideanSpace ℝ (Fin d),
      y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) →
      iota y ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2) := by
    intro y hy
    rw [mem_ball, dist_zero_right] at hy
    rw [mem_closedBall, dist_zero_right, hiota y, WithLp.norm_toLp_fst]
    exact le_of_lt hy
  -- eq:me-normalized-conclusion: the slice of the space-time statement at `(y,0)`.
  have hslice : ∀ v : EuclideanSpace ℝ (Fin d) → ℝ,
      IsInfHarmonicOn (ball 0 1) v → v 0 = 0 →
      BddAbove (v '' ball 0 1) → BddBelow (v '' ball 0 1) →
      OscOn v (ball 0 1) ≤ 1 →
      ∃ q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), HasGradientAt v (q y) y) ∧
        (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), ‖q y‖ ≤ L + 1) ∧
        (∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2),
          ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2),
            ‖q y - q y'‖ ≤ C' * ‖y - y'‖ ^ al) := by
    intro v hv hv0 hvba hvbb hvosc
    -- `U(y,b) = v y + b` is a member of the normalized family
    obtain ⟨U, hUdef⟩ : ∃ U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
        ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), U z = v (ofLp z).1 + (ofLp z).2 :=
      ⟨_, fun _ => rfl⟩
    have hU : NormalizedInfFamily d U := ⟨v, hv, hv0, hvba, hvbb, hvosc, hUdef⟩
    obtain ⟨G, hGtay, hGbd⟩ := hgrad U hU
    obtain ⟨hGgrad, hGhol⟩ := hholder
      (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2)) U G
      (fun z hz h hh => le_trans (hGtay z hz h hh)
        (mul_le_mul_of_nonneg_right (by rw [hCMdef]; exact le_max_left _ _)
          (Real.rpow_nonneg (norm_nonneg h) _)))
      (fun z hz => le_trans (hGbd z hz) (by rw [hCMdef]; exact le_max_right _ _))
    obtain ⟨q, hqdef⟩ : ∃ q : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        ∀ y, q y = (ofLp (G (iota y))).1 := ⟨_, fun _ => rfl⟩
    refine ⟨q, ?_, ?_, ?_⟩
    · -- differentiability of the slice: chain rule along `ι`, then the Riesz bridge back
      intro y hy
      have hgU := (hGgrad (iota y) (hmem y hy)).hasFDerivAt
      have hcomp := HasFDerivAt.comp y hgU iota.hasFDerivAt
      have hvd := hcomp.congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun y' : EuclideanSpace ℝ (Fin d) =>
          show v y' = U (iota y') by rw [hUdef, hiota y']; simp))
      have hmap : ((InnerProductSpace.toDual ℝ
              (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (G (iota y))).comp
            (iota : EuclideanSpace ℝ (Fin d) →L[ℝ]
              WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
          = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
              ((ofLp (G (iota y))).1) := by
        ext h
        exact hinner (G (iota y)) h
      rw [hmap] at hvd
      rw [hqdef y]
      exact hasGradientAt_iff_hasFDerivAt.mpr hvd
    · intro y hy
      rw [hqdef y]
      exact le_trans (hfstle (G (iota y))) (hGbd (iota y) (hmem y hy))
    · intro y hy y' hy'
      have h1 := hGhol (iota y) (hmem y hy) (iota y') (hmem y' hy')
      have h2 : ‖iota y - iota y'‖ = ‖y - y'‖ := by
        rw [← map_sub iota y y', hiota, WithLp.norm_toLp_fst]
      rw [h2] at h1
      refine le_trans ?_ h1
      rw [hqdef y, hqdef y']
      exact hfstle (G (iota y) - G (iota y'))
  -- ===================== STEP 10: THE THEOREM =================================
  refine ⟨al, L + 1 + C', hal0, hal3, by linarith only [hL0, hC'0], ?_⟩
  intro u hu hba hbb
  have hne : (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty := by
    refine ⟨u 0, 0, ?_, rfl⟩
    rw [mem_ball, dist_self]; norm_num
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ,
      M = OscOn u (ball (0 : EuclideanSpace ℝ (Fin d)) 1) := ⟨_, rfl⟩
  have hMval : sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      - sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) = M := by
    rw [hMdef, OscOn]
  have hM0 : 0 ≤ M := by
    have h := csInf_le_csSup hne hbb hba
    linarith only [h, hMval]
  rcases eq_or_lt_of_le hM0 with hM | hM
  · -- THE CASE `M = 0`: `u` is constant on `B₁` and `g ≡ 0` works.  No paper sentence
    -- stands behind this branch; paper.tex:822 treats `M > 0` only.
    obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ,
        ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1, u x = c₀ := by
      refine ⟨sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1), fun x hx => ?_⟩
      have h1 : u x ≤ sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
        le_csSup hba ⟨x, hx, rfl⟩
      have h2 : sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ u x :=
        csInf_le hbb ⟨x, hx, rfl⟩
      linarith only [h1, h2, hMval, hM]
    obtain ⟨g, hgdef⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        ∀ x, g x = 0 := ⟨_, fun _ => rfl⟩
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · intro x hx
      have hx1 : x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
        rw [mem_ball, dist_zero_right] at hx ⊢
        linarith only [hx]
      rw [hgdef x]
      refine hasGradientAt_iff_hasFDerivAt.mpr ?_
      rw [show InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) 0 = 0 from by simp]
      refine (hasFDerivAt_const c₀ x).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_ball.mem_nhds hx1] with x' hx' using hc₀ x' hx'
    · refine ⟨0, fun t ht => ?_⟩
      obtain ⟨x, -, rfl⟩ := ht
      show ‖g x‖ ≤ 0
      rw [hgdef x, norm_zero]
    · refine ⟨0, fun t ht => ?_⟩
      rw [HolderQuotSet, Set.mem_ofPred_eq] at ht
      obtain ⟨x, -, y, -, -, rfl⟩ := ht
      rw [hgdef x, hgdef y, sub_zero, norm_zero, zero_div]
    · have h1 : sSup ((fun x => ‖g x‖) '' ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
          ≤ 0 := by
        refine Real.sSup_le (fun t ht => ?_) le_rfl
        obtain ⟨x, -, rfl⟩ := ht
        show ‖g x‖ ≤ 0
        rw [hgdef x, norm_zero]
      have h2 : HolderSeminormOn g al (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
          ≤ 0 := by
        rw [HolderSeminormOn]
        refine Real.sSup_le (fun t ht => ?_) le_rfl
        rw [HolderQuotSet, Set.mem_ofPred_eq] at ht
        obtain ⟨x, -, y, -, -, rfl⟩ := ht
        rw [hgdef x, hgdef y, sub_zero, norm_zero, zero_div]
      rw [← hMdef, ← hM]
      linarith only [h1, h2]
  · -- THE CASE `M > 0`: descend through the normalized solution `v = (u - u 0)/M`.
    obtain ⟨cc, hccdef⟩ : ∃ cc : ℝ, cc = u 0 := ⟨_, rfl⟩
    obtain ⟨v, hvdef⟩ : ∃ v : EuclideanSpace ℝ (Fin d) → ℝ,
        v = fun y => (u y - cc) / M := ⟨_, rfl⟩
    have hvapp : ∀ y : EuclideanSpace ℝ (Fin d), v y = (u y - cc) / M := by
      intro y; rw [hvdef]
    have hvharm : IsInfHarmonicOn (ball (0 : EuclideanSpace ℝ (Fin d)) 1) v := by
      rw [hvdef]
      exact InfHarmonicNormalize (ball (0 : EuclideanSpace ℝ (Fin d)) 1) u hu cc M hM
    have hv0 : v 0 = 0 := by rw [hvapp 0, hccdef, sub_self, zero_div]
    -- `t ↦ (t - cc)/M` is increasing, which is all the two `Bdd` guards and the
    -- oscillation computation need
    have hmono : ∀ a b : ℝ, a ≤ b → (a - cc) / M ≤ (b - cc) / M := by
      intro a b hab
      have hMi : (0 : ℝ) < M⁻¹ := inv_pos.mpr hM
      rw [div_eq_mul_inv, div_eq_mul_inv]
      nlinarith only [hab, hMi]
    have hvba : BddAbove (v '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
      refine ⟨(sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc) / M, fun t ht => ?_⟩
      obtain ⟨x, hx, rfl⟩ := ht
      rw [hvapp x]
      exact hmono _ _ (le_csSup hba ⟨x, hx, rfl⟩)
    have hvbb : BddBelow (v '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
      refine ⟨(sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc) / M, fun t ht => ?_⟩
      obtain ⟨x, hx, rfl⟩ := ht
      rw [hvapp x]
      exact hmono _ _ (csInf_le hbb ⟨x, hx, rfl⟩)
    have hvne : (v '' ball (0 : EuclideanSpace ℝ (Fin d)) 1).Nonempty := by
      refine ⟨v 0, 0, ?_, rfl⟩
      rw [mem_ball, dist_self]; norm_num
    have hvosc : OscOn v (ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ 1 := by
      rw [OscOn]
      have hsup : sSup (v '' ball (0 : EuclideanSpace ℝ (Fin d)) 1)
          ≤ (sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc) / M := by
        refine csSup_le hvne (fun t ht => ?_)
        obtain ⟨x, hx, rfl⟩ := ht
        rw [hvapp x]
        exact hmono _ _ (le_csSup hba ⟨x, hx, rfl⟩)
      have hinf : (sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc) / M
          ≤ sInf (v '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) := by
        refine le_csInf hvne (fun t ht => ?_)
        obtain ⟨x, hx, rfl⟩ := ht
        rw [hvapp x]
        exact hmono _ _ (csInf_le hbb ⟨x, hx, rfl⟩)
      have hdiff : (sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc) / M
          - (sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc) / M = 1 := by
        rw [div_sub_div_same,
          show sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc
              - (sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) - cc)
            = M from by linarith only [hMval]]
        exact div_self (ne_of_gt hM)
      linarith only [hsup, hinf, hdiff]
    obtain ⟨q, hq1, hq2, hq3⟩ := hslice v hvharm hv0 hvba hvbb hvosc
    obtain ⟨g, hgdef⟩ : ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
        ∀ x, g x = M • q x := ⟨_, fun _ => rfl⟩
    -- eq:me-final-bounds, the two scaled estimates
    have hgn : ∀ x : EuclideanSpace ℝ (Fin d), ‖g x‖ = M * ‖q x‖ := by
      intro x
      rw [hgdef x, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
    have hgb : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), ‖g x‖ ≤ M * (L + 1) := by
      intro x hx
      rw [hgn x]
      have h5 := mul_le_mul_of_nonneg_left (hq2 x hx) (le_of_lt hM)
      linarith only [h5]
    have hquot : ∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2),
        ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), x ≠ y →
        ‖g x - g y‖ / dist x y ^ al ≤ M * C' := by
      intro x hx y hy hxy
      have hdpos : 0 < dist x y := dist_pos.mpr hxy
      have hdap : (0 : ℝ) < dist x y ^ al := Real.rpow_pos_of_pos hdpos al
      have h2 : ‖g x - g y‖ = M * ‖q x - q y‖ := by
        rw [hgdef x, hgdef y, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hM]
      have h3 := hq3 x hx y hy
      rw [show ‖x - y‖ = dist x y from (dist_eq_norm x y).symm] at h3
      rw [div_le_iff₀ hdap, h2]
      have h5 := mul_le_mul_of_nonneg_left h3 (le_of_lt hM)
      linarith only [h5]
    refine ⟨g, ?_, ?_, ?_, ?_⟩
    · -- `u = M v + cc`, so the gradient scales
      intro x hx
      rw [hgdef x]
      refine hasGradientAt_iff_hasFDerivAt.mpr ?_
      have h1 : HasFDerivAt v
          (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (q x)) x :=
        (hq1 x hx).hasFDerivAt
      have h2 := (h1.const_smul M).add_const cc
      have hmap : (M • InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (q x))
          = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d)) (M • q x) := by
        ext h
        show M * (inner ℝ (q x) h : ℝ) = (inner ℝ (M • q x) h : ℝ)
        rw [real_inner_smul_left]
      rw [hmap] at h2
      refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => ?_))
      show u y = M • v y + cc
      rw [hvapp y, smul_eq_mul]
      field_simp
      ring
    · exact ⟨M * (L + 1), fun t ht => by
        obtain ⟨x, hx, rfl⟩ := ht
        exact hgb x hx⟩
    · refine ⟨M * C', fun t ht => ?_⟩
      rw [HolderQuotSet, Set.mem_ofPred_eq] at ht
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := ht
      exact hquot x hx y hy hxy
    · have h1 : sSup ((fun x => ‖g x‖) '' ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
          ≤ M * (L + 1) := by
        refine Real.sSup_le (fun t ht => ?_) (by nlinarith only [hM, hL0])
        obtain ⟨x, hx, rfl⟩ := ht
        exact hgb x hx
      have h2 : HolderSeminormOn g al (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
          ≤ M * C' := by
        rw [HolderSeminormOn]
        refine Real.sSup_le (fun t ht => ?_) (by nlinarith only [hM, hC'0])
        rw [HolderQuotSet, Set.mem_ofPred_eq] at ht
        obtain ⟨x, hx, y, hy, hxy, rfl⟩ := ht
        exact hquot x hx y hy hxy
      rw [← hMdef]
      linarith only [h1, h2]
