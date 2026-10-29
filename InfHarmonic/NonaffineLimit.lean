import InfHarmonic.IsBadScaleData
import InfHarmonic.CylinderFitSlopeBounds
import InfHarmonic.CylinderComparisonSameCenter
import InfHarmonic.CylinderComparisonShifted
import InfHarmonic.NormalizedFamilyLipschitz
import InfHarmonic.IsFitClass
import InfHarmonic.IsSpaceTimeAffine
import InfHarmonic.AsymptEquicontLocalUniformLimit
import InfHarmonic.CylinderFitDoublingChain
import InfHarmonic.NormalizedSlopeCoefficients
import InfHarmonic.AnisotropicBoxOffsets
import InfHarmonic.NonaffineLimitEquicontinuousSubsequence
import InfHarmonic.ShearedBoxInFitCylinder
import InfHarmonic.EnclosingAndNearbyFits
import InfHarmonic.LimitIsFitAtEveryScale
import InfHarmonic.FitCylinderToNormalizedBox
import InfHarmonic.NormalizedLimitNotAffine
import InfHarmonic.NonaffineLimitIsLimitSolution
set_option maxHeartbeats 500000
open Metric Set Filter Topology WithLp

/-- Proposition 3.6: for the bad-scale data of Lemma 3.4 and the anisotropic
normalization (3.6), a subsequence of the normalized solutions `v i` converges
locally uniformly to a nonaffine member of the class `A_{d,C₀}` for one finite
constant `C₀`. -/
theorem NonaffineLimit (d : ℕ) (hd : 1 ≤ d) (γ s r lam : ℕ → ℝ)
    (U : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (z : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (hdata : IsBadScaleData d hd γ s r lam U z)
    (i₁ : ℕ) (P : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (hP : ∀ i ≥ i₁, IsCylinderFit (U i) (z i) (r i) (32 * lam i) (P i))
    (Φ : ℕ → (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)
                ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
    (hΦ : ∀ i ≥ i₁,
      Φ i (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) = ‖P i‖⁻¹ • P i)
    (v : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hv : ∀ i ≥ i₁, ∀ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      U i (z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))
        = U i (z i) + r i * ‖P i‖ * ((ofLp w).2 + lam i * v i w)) :
    ∃ (C₀ : ℝ) (ψ : ℕ → ℕ) (w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ),
      0 ≤ C₀ ∧ StrictMono ψ ∧ (∀ j, i₁ ≤ ψ j) ∧ Continuous w ∧
      (∀ K : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), IsCompact K →
        TendstoUniformlyOn (fun j => v (ψ j)) w atTop K) ∧
      IsFitClass C₀ w ∧ ¬ IsSpaceTimeAffine w := by
  classical
  -- ===================================================================
  -- SCAFFOLD MAP (burst 595).  THE NODE IS CLOSED.  Each conjunct of the conclusion, and the block
  -- that discharges it:
  --   0 ≤ C₀                      `by norm_num` at C₀ = 8Λ = 256 (Step 11's constant)
  --   StrictMono ψ                `hpsimono`   (Step 9)
  --   ∀ j, i₁ ≤ ψ j               `hpsige`     (Step 9)
  --   Continuous w                `hvcont`     (Step 9)
  --   locally uniform convergence `hvconv`     (Step 9, via AsymptEquicontLocalUniformLimit)
  --   IsFitClass 256 w            `hlimsol`    (Step 10, via RescaledLimitStability)
  --                           and `hfits`      (Step 11)
  --   ¬ IsSpaceTimeAffine w       `hnonaffine` (Step 12)
  --
  -- CLOSED (burst 579 and before): Step 0 (`hDle`, `horigin`, eq:nl-tail), Step 1
  -- (`hslope`, `hbasenorm`), Step 2 (`C₁`, `hcmpA`, `hcmpB`), Step 3 (`hchain`,
  -- eq:nl-base-chain), Step 6 (`hincrement`, eq:nl-increment), and ALL of Steps 4-5:
  -- eq:nl-R (`Rad`, `hRad2`, `hRad16`, `hRadR`), eq:nl-disp (`hdisp`), the enlarged
  -- scale (`Mof`, `iadm`, `hfitz`, `hfitw`), Claim 4a (`hclaim4a`), the enclosing
  -- fit (`henclR`), the nearby fits (`hnearbyN`, eq:nl-cmp) and the normalized
  -- coefficients (`hcoeff`, eq:nl-coeff + eq:nl-coeff-bound).
  --
  -- THREE OF THOSE BLOCKS HAVE BEEN LIFTED INTO Lean-CLOSED HELPER NODES, and the
  -- blocks that remain here only instantiate them:
  --   burst 572: `hchain` -> `CylinderFitDoublingChain`   (the doubling induction)
  --              `hcoeff` -> `NormalizedSlopeCoefficients` (the frame coordinates)
  --   burst 579: `hclaim4a` + `hproj` + eq:nl-disp's length bound
  --                       -> `AnisotropicBoxOffsets`       (the box geometry)
  --   burst 585: Step 9's whole package
  --                       -> `AsymptEquicontOriginNormalizedLimit`
  --              Step 10's gluing
  --                       -> `LimitSolutionLocalToGlobal`
  --              Step 8's shear geometry (Claim 8a)
  --                       -> `ShearedBoxInFitCylinder`
  --   burst 590: Step 12's cylinder-to-box inclusion
  --                       -> `FitCylinderToNormalizedBox`
  -- THE LIFT QUEUE EMPTIED AT BURST 590 and the last three blocks were written in place,
  -- which was right: each of them fails pm-0040's test on its own statement's parameter
  -- list, not merely on what its proof mentions.  `hballsol` needs `psi` and the
  -- per-member `Ω_i`; `hfits` needs `vlim`, `Cthree` and `hfit`; `hnonaffine` needs
  -- `psi`, `vlim`, `hbad`, `hincrement` and `cc`.
  -- The factorization rule, which has now worked three times: state the node over the
  -- data the block actually USES, with no index, no sequence and no bad-scale data.
  -- `AnisotropicBoxOffsets` therefore takes `Cb` where this proof passes
  -- `C₂ (1 + log R)`; the node never sees a logarithm.
  --
  -- THE NODE IS CLOSED (burst 595): zero `sorry`, and `#print axioms NonaffineLimit`
  -- reads exactly `[propext, Classical.choice, Quot.sound]`.  The last three blocks, and
  -- the one thing about each that is easy to get wrong:
  --   `hballsol`   eq:nl-domains     (Step 10).  The chain is `NormalizedInfFamily`
  --                unpack -> `LinearLift` at `ball 0 1` -> `RescaledEquation` -> RESTRICT
  --                -> tail shift -> `RescaledLimitStability`, then the already-closed
  --                gluing.  THE RESTRICTION GOES THE HARD WAY ROUND: a rescaled solution
  --                on `Ω` restricts to an OPEN `Ω' ⊆ Ω` only because `𝓝[Ω'] z = 𝓝 z`
  --                for `z ∈ Ω'` open, which upgrades a local extremum relative to `Ω'`
  --                to one relative to `Ω`.  `nhdsWithin_mono` alone runs the wrong way
  --                here, unlike in `LimitSolutionLocalToGlobal`.
  --                The TAIL INDEX exists because `r i → 0`: `r i ≤ s i * D(z i)`,
  --                `D ≤ 3/4` on `G` and `s i → 0`.
  --   `hfits`                        (Step 11).  `S = 4R'`, so `64 S = 256 R' = C₀ R'`
  --                EXACTLY -- and that is not a problem, because a NON-STRICT bound
  --                passes to a uniform limit with no loss.  The margin lives on the
  --                DOMAIN side: `|l| ≤ R' ≤ S/2` is a factor 2 outright, and
  --                `‖h - (l/A)p'‖ ≤ ‖h - l p‖ + |l|‖p - p'/A‖ ≤ R' + 2R' ≤ 4R'` once the
  --                shears are within 2 of `p`.  The further extraction is LOCAL to
  --                `(zhat, R')`, after `intro zhat R'`.
  --   `hnonaffine`                   (Step 12).  `IsCylinderFit`'s FIRST conjunct is
  --                `P ≠ 0` and it is a real obligation: `‖P̃_i‖² = c_i²N_i² ≥ 1/16`.
  --                The tolerance is `λ_i r_i` EXACTLY, not `32 λ_i r_i`, so the threshold
  --                is `c_i |v_i - v| ≤ 1`, i.e. `|v_i - v| < 1/(L+1)` by `c_i ≤ L+1`.
  --                The residual is an IDENTITY, not an estimate, because `Φ i` is an
  --                isometry: `hincrement` at `(p',q') = (p,q)` leaves nothing over.
  --                `hbad` holds for ALL `i`, so ONE index along `psi` suffices.
  --
  -- HOW STEPS 4-5 WERE FINISHED (burst 579), because the route is not the .tex's:
  -- the .tex passes from `(Z_i(w), R r_i)` to `(Z_i(w), S r_i)` through a chain of
  -- radii with consecutive ratios in [1,2], built by doublings or halvings according
  -- to whether S ≤ R.  Here that is TWO instances of `CylinderFitDoublingChain` run
  -- OUT of the common base radius `m r_i`, m = min(S, R(K)), one reaching S r_i and
  -- one reaching R(K) r_i, plus one Step 2(a) per leg.  Both target radii are ≥ m r_i,
  -- so the two legs are literally the same argument and there is NO case split on
  -- S ≤ R(K).  The cited node insists on ratio ≥ 2, which an arbitrary S/R violates;
  -- `hratio` clamps each ratio at 2, overshooting by at most one doubling, and the
  -- per-leg Step 2(a) repairs the overshoot.  Because `r i` cancels out of
  -- `max 2 (a/m)`, both ratios -- hence C₃(K,S) -- are independent of `i`, which is
  -- what Steps 7 and 8 need.  `hgood` is invoked at the ENLARGED scale
  -- `Sb = 2 max(S, R(K))` so that fits exist at every radius the clamped ratios reach.
  --
  -- WHAT STEP 9 ACTUALLY NEEDED, because the scaffold comment used to hide it: the cited
  -- Arzelà--Ascoli node returns local uniform convergence and NOTHING ELSE.  The three
  -- further conjuncts -- `∀ j, i₁ ≤ ψ j`, `Continuous w`, `w 0 = 0` -- are not in its
  -- conclusion, and it does not even take continuity of the `v i` as a hypothesis.  All
  -- three now live in `AsymptEquicontOriginNormalizedLimit`; continuity is the
  -- substantive one (the asymptotic modulus passes to the limit).  What is left here is
  -- the two INTERFACE derivations, `hbd` from Step 7 through `closedBall ⊆ Box`, and
  -- `hequi` from Step 8 through the ε/2 + ε/2 split.
  --
  -- HEARTBEATS, the running measurement.  938 lines before the burst-572 lift: passed at
  -- 200000, failed at 100000.  After lifting `hchain` and `hcoeff` into nodes: 691 lines,
  -- passed at 100000, failed at 50000 -- cost HALVED.  After burst 577 added `Mof`/`iadm`,
  -- `hproj`, `hclaim4a` and `henclR`: 1046 lines, passed at 200000, FAILED at 100000.
  -- Burst 579 lifted `hclaim4a` (1046 -> 954 lines): passed at 100000, failed at 75000 --
  -- cost halved AGAIN, same mechanism.  Closing `hnearbyN` then spent that headroom in
  -- one block: 1121 lines, passes at 125000 and FAILS at 100000, so the default 200000
  -- is down to a 1.6x margin with six holes left.  Burst 585 then closed Step 9 and
  -- restructured Step 10 around two lifts: 1340 lines, passes at 150000 and FAILS at
  -- 100000, so the cost per line fell again.  Burst 590 closed Steps 7 and 8 and added
  -- the last lift: 1551 lines, passes at 150000 and FAILS at 125000 -- the bracket did
  -- not move at all under +211 lines.  Burst 595 closed the last three: 2087 lines,
  -- passes at 250000 and FAILS at 200000, so `set_option maxHeartbeats 500000`, twice the
  -- measured bracket.  That is the FINAL figure: the node will not grow again.
  --
  -- MEMORY, measured rather than asserted, because the cycle-179 audit flagged it: peak
  -- RSS of `lake env lean Tablet/NonaffineLimit.lean` went 3.72 GB at 1188 lines to
  -- 3.80 GB at 1551 lines to 3.99 GB at 2087 lines, with wall clock 10.7 s -> 13.2 s ->
  -- 24.6 s.  So RSS tracks elaboration work and not line count, exactly as the heartbeat
  -- bracket does: +899 lines cost +0.27 GB.  The 3.7 GB reading flagged at cycle 179 was
  -- not the start of a trend, and the growth-pattern argument that pointed past
  -- `ThreePointFlatness` is retired by measurement.
  --
  -- THE LIFT TEST IS ON THE LIFTED STATEMENT'S PARAMETER LIST, NOT ON THE CURRENT
  -- PROOF'S SCOPE (pm-0040).  Burst 579 declined to lift Steps 8-12 because those blocks
  -- "read `hfitw`, `henclR`, `hcmpA`, `hcmpB`, `hcoeff` and `Rad` from this context".
  -- That is the WRONG test, and it is not the test that produced the three earlier lifts.
  -- Under the right one, Step 9's statement needs only `v`, `i₁` and two moduli; Step
  -- 10's gluing needs only a cover and `IsLimitSolutionOn`; Step 8's geometric core needs
  -- only `(Φ, lam, p', q', S, h, l, rb)` and a coefficient bound.  All three lifted.
  -- `hnearbyN` fails the right test too -- it genuinely needs `Rad`, `henclR` and the two
  -- comparisons -- so declining to lift THAT one was correct and still stands.
  -- `as_aux_lemma =>` was measured and does NOT help here: heartbeat-neutral, 1.2 s
  -- faster, because it abstracts the whole ~30-hypothesis local context into each sealed
  -- lemma.  So LIFT rather than seal; and raise the budget only when nothing standalone
  -- remains, reporting the measured bracket rather than a round number.
  --
  -- THE PRICING MODEL, COMPLETE.  Four lifts have each either halved the bracket or left
  -- it unmoved while the line count grew: 938 -> 691 halved it, 1046 -> 954 halved it,
  -- 1340 and 1551 did not move it at all.  The mechanism is that cost tracks AUTOMATION
  -- WIDTH and CONTEXT SIZE, not length, and a citation is nearly free however much
  -- mathematics it stands for.  Line count has stopped predicting anything here.
  --
  -- THE THREE CONSTANTS TO GUARD, each with the symptom of getting it wrong:
  --   Λ = 32.  Comes from `hdata`'s last conjunct, which states the fit parameter
  --     as `32 * lam i`.  θ i = √(32 * lam i), so θ i ^ 2 = 32 * lam i exactly.
  --   (1 + log R) in eq:nl-base-chain and eq:nl-cmp.  This is the DOUBLING COUNT:
  --     the chain from r i to R * r i has about log₂ R links, each contributing
  --     O(θ i) by Step 2(a), and C₂ = 2 * C₁ absorbs log₂ R ≤ 2 log R for R ≥ 2.
  --     A bound that comes out with a bare constant in place of (1 + log R) means
  --     the chain length was dropped — and Step 4 NEEDS the log, because
  --     R / log R → ∞ is exactly what makes eq:nl-R satisfiable.
  --   p' and q' DRAW ON DIFFERENT ESTIMATES (paper.tex:680-700).  p' is transverse
  --     and comes from the O(θ i) DIRECTION estimate; q' is longitudinal and comes
  --     from the O(θ i ^ 2) NORM estimate PLUS the quadratic angular error
  --     |P_t - c i| ≤ |‖P‖ - c i| + ‖P‖ * ‖P/‖P‖ - P i / c i‖ ^ 2 / 2.  Both land at
  --     C₃ only because θ i ^ 2 = 32 * lam i.  If q' comes out carrying a stray
  --     √(lam i), the quadratic angular term has been dropped.
  -- ===================================================================
  -- ===================== NOTATION =====================
  -- `eb = (0,1)` is the added unit time direction; `th` is θ, `cc` is c = |P|,
  -- `Dd` the distance to `∂G`, `Zi` the normalizing map of eq:nl-normalization and
  -- `Box K` the box `𝓑_K` of the .tex.  Each is introduced with its defining
  -- equation so no block has to re-elaborate the underlying term.
  obtain ⟨eb, hebdef⟩ : ∃ eb : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      eb = toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨th, hthdef⟩ : ∃ th : ℕ → ℝ, th = fun i => Real.sqrt (32 * lam i) := ⟨_, rfl⟩
  obtain ⟨cc, hccdef⟩ : ∃ cc : ℕ → ℝ, cc = fun i => ‖P i‖ := ⟨_, rfl⟩
  obtain ⟨Dd, hDddef⟩ : ∃ Dd : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      Dd = fun w => infDist w
        (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) := ⟨_, rfl⟩
  obtain ⟨Zi, hZidef⟩ : ∃ Zi : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) →
        WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      Zi = fun i w =>
        z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)) := ⟨_, rfl⟩
  obtain ⟨Box, hBoxdef⟩ : ∃ Box : ℝ → Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
      Box = fun K => {w | ‖(ofLp w).1‖ ≤ K ∧ |(ofLp w).2| ≤ K} := ⟨_, rfl⟩
  -- ===================== STEP 0: THE STANDING DATA =====================
  -- The twelve conjuncts of `IsBadScaleData`, named.
  obtain ⟨hgam0, hgamlim, hs0, hslim, hlam0, hlamlim, hUnorm, hzG, hr0, hrle,
    hbad, hgood⟩ := hdata
  -- the Lipschitz constant of eq:nl-lip
  obtain ⟨L, hL0, hLb⟩ := NormalizedFamilyLipschitz d hd
  -- `c i > 0` for `i ≥ i₁`: a cylinder fit has a nonzero slope
  have hcc0 : ∀ i ≥ i₁, 0 < cc i := by
    intro i hi
    rw [hccdef]
    exact norm_pos_iff.mpr (hP i hi).1
  -- eq:nl-D, in the only form the later steps use: `D(w) ≤ 3/4` on `G`.  The frontier
  -- of `G` is the sphere of radius `3/4`, nonempty because the space-time has dimension
  -- `d + 1 ≥ 2`, and the radial projection of `w` onto it is at distance `3/4 - |w| ≤ 3/4`.
  have hDle : ∀ w ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4),
      Dd w ≤ 3 / 4 := by
    intro w hw
    rw [mem_ball, dist_zero_right] at hw
    rw [hDddef]
    show infDist w
      (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ≤ 3 / 4
    rw [frontier_ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      (by norm_num : (3 : ℝ) / 4 ≠ 0)]
    have key : ∀ y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖y‖ = 3 / 4 →
        ‖w - y‖ ≤ 3 / 4 →
        infDist w (sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))
          ≤ 3 / 4 := by
      intro y hyn hwy
      have hymem : y ∈ sphere (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) := by
        rw [mem_sphere, dist_zero_right, hyn]
      refine le_trans (infDist_le_dist_of_mem hymem) ?_
      rw [dist_eq_norm]; exact hwy
    rcases eq_or_ne w 0 with h0 | h0
    · obtain ⟨vv, hvv⟩ := exists_ne (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      have hvn : ‖vv‖ ≠ 0 := norm_ne_zero_iff.mpr hvv
      refine key ((3 / 4 * ‖vv‖⁻¹) • vv) ?_ ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_assoc,
          inv_mul_cancel₀ hvn, mul_one]
      · rw [h0, zero_sub, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (by positivity), mul_assoc, inv_mul_cancel₀ hvn, mul_one]
    · have hwn : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr h0
      refine key ((3 / 4 / ‖w‖) • w) ?_ ?_
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity),
          div_mul_cancel₀ _ (ne_of_gt hwn)]
      · have hsub : w - (3 / 4 / ‖w‖) • w = (1 - 3 / 4 / ‖w‖) • w := by
          rw [sub_smul, one_smul]
        rw [hsub, norm_smul, Real.norm_eq_abs]
        have hneg : 1 - 3 / 4 / ‖w‖ ≤ 0 := by
          rw [sub_nonpos, le_div_iff₀ hwn]; linarith only [hw]
        rw [abs_of_nonpos hneg]
        have h1 : -(1 - 3 / 4 / ‖w‖) * ‖w‖ = 3 / 4 - ‖w‖ := by
          field_simp
          ring
        rw [h1]
        linarith only [hwn]
  -- eq:nl-origin: putting `(x,t) = (0,0)` in eq:nl-normalization
  have horigin : ∀ i ≥ i₁, v i 0 = 0 := by
    intro i hi
    have h := hv i hi 0
    simp at h
    have hzero : (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (0 : ℝ)))
        = (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) := rfl
    rw [hzero, map_zero, smul_zero, add_zero] at h
    have hc := hcc0 i hi
    rw [hccdef] at hc
    have hprod : (r i * ‖P i‖ * lam i) * v i 0 = 0 := by linarith only [h]
    rcases mul_eq_zero.mp hprod with hz | hz
    · exact absurd hz (ne_of_gt (mul_pos (mul_pos (hr0 i) hc) (hlam0 i)))
    · exact hz
  -- eq:nl-tail: `Λ λ_i ≤ 1` and `θ_i ≤ 1/2` past one index, which also sits past
  -- `i₁` and past the threshold `i₀(2)` of `hgood`, so that `(z_i, r_i)` is
  -- admissible from `i₂` on
  obtain ⟨i₂, hi₂i₁, htail1, htail2, hadm0⟩ : ∃ i₂ : ℕ, i₁ ≤ i₂ ∧
      (∀ i ≥ i₂, 32 * lam i ≤ 1) ∧ (∀ i ≥ i₂, th i ≤ 1 / 2) ∧
      (∀ i ≥ i₂, z i ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
        r i ≤ 1 / 8 * Dd (z i)) := by
    obtain ⟨j₀, hj₀⟩ := hgood 2 (le_refl 2)
    have hlam32 : Tendsto (fun i => 32 * lam i) atTop (𝓝 0) := by
      have h := hlamlim.const_mul (32 : ℝ)
      rw [mul_zero] at h
      exact h
    have e1 : ∀ᶠ i in atTop, 32 * lam i ≤ 1 := by
      filter_upwards [hlam32.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with i hi
      exact le_of_lt hi
    have e2 : ∀ᶠ i in atTop, th i ≤ 1 / 2 := by
      filter_upwards [hlam32.eventually_lt_const
        (show (0 : ℝ) < (1 / 2 : ℝ) ^ 2 by norm_num)] with i hi
      rw [hthdef]
      show Real.sqrt (32 * lam i) ≤ 1 / 2
      have hb : Real.sqrt (32 * lam i) ≤ Real.sqrt ((1 / 2 : ℝ) ^ 2) :=
        Real.sqrt_le_sqrt (le_of_lt hi)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at hb
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (e1.and e2)
    refine ⟨max (max i₁ j₀) N, le_trans (le_max_left _ _) (le_max_left _ _),
      fun i hi => (hN i (le_trans (le_max_right _ _) hi)).1,
      fun i hi => (hN i (le_trans (le_max_right _ _) hi)).2, fun i hi => ⟨hzG i, ?_⟩⟩
    have hij : j₀ ≤ i := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hi
    have hd0 : ‖z i - z i‖ ≤ 2 * r i := by
      rw [sub_self, norm_zero]
      linarith only [hr0 i]
    obtain ⟨-, hrho, -⟩ := hj₀ i hij (z i) hd0 (r i) (hr0 i) (by linarith only [hr0 i])
    simp only [hDddef]
    exact hrho
  -- ===================== STEP 1: TWO-SIDED SLOPE BOUNDS =====================
  -- eq:nl-slope, at every admissible pair, and eq:nl-base-norm at `(z_i, r_i)`.
  have hslope : ∀ i ≥ i₂,
      ∀ w ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4),
      ∀ rho : ℝ, 0 < rho → rho ≤ 1 / 8 * Dd w →
      ∀ Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        IsCylinderFit (U i) w rho (32 * lam i) Q → 1 / 2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ L + 1 := by
    intro i hi w hw rho hrho hrhole Q hfitQ
    have hwn : ‖w‖ < 3 / 4 := by
      rw [mem_ball, dist_zero_right] at hw; exact hw
    -- `ρ ≤ D(w)/8 ≤ 3/32`, so the whole `ρ`-ball at `w` sits in the closed 7/8-ball
    have hrho32 : rho ≤ 3 / 32 := by linarith only [hrhole, hDle w hw]
    have hLip : ∀ h : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖h‖ ≤ rho →
        |U i (w + h) - U i w| ≤ L * ‖h‖ := by
      intro h hh
      have hA : w + h ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
        rw [mem_closedBall, dist_zero_right]
        linarith only [norm_add_le w h, hh, hrho32, hwn]
      have hB : w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
        rw [mem_closedBall, dist_zero_right]; linarith only [hwn]
      have hlip := (hLb (U i) (hUnorm i)).2 (w + h) hA w hB
      rwa [show w + h - w = h from by abel] at hlip
    obtain ⟨h1, h2⟩ := CylinderFitSlopeBounds d hd (U i) (hUnorm i) L w rho (32 * lam i)
      hrho (by linarith only [hlam0 i]) (htail1 i hi) hLip Q hfitQ
    have hthi : Real.sqrt (32 * lam i) = th i := by rw [hthdef]
    rw [hthi] at h1 h2
    have hth12 := htail2 i hi
    refine ⟨?_, by linarith only [h1, hth12]⟩
    -- the lower bound: `|Q| ≥ |⟪Q, e_b⟫| ≥ 1 - θ_i ≥ 1/2` by Cauchy--Schwarz
    have hebn : ‖(toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) :
        WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ = 1 := by
      rw [WithLp.prod_norm_eq_of_L2]
      norm_num
    have hcs : |(inner ℝ Q (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) : ℝ)| ≤ ‖Q‖ := by
      have hb := abs_real_inner_le_norm Q
        (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) :
          WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      rwa [hebn, mul_one] at hb
    have h3 := abs_le.mp h2
    have h4 := abs_le.mp hcs
    linarith only [h3.1, h4.2, hth12]
  have hbasenorm : ∀ i ≥ i₂, 1 / 2 ≤ cc i ∧ cc i ≤ L + 1 := by
    intro i hi
    simp only [hccdef]
    exact hslope i hi (z i) (hadm0 i hi).1 (r i) (hr0 i) (hadm0 i hi).2 (P i)
      (hP i (le_trans hi₂i₁ hi))
  -- ===================== STEP 2: ONE COMPARISON CONSTANT =====================
  -- `C₁` serves both the same-centre comparison (a) and the shifted one (b), at
  -- the slope window `[1/2, L+1]` of eq:nl-slope.
  obtain ⟨C₁, hC₁1, hcmpA, hcmpB⟩ : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      (∀ (i : ℕ) (w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (H H' : ℝ)
        (Q Q' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), i₂ ≤ i →
        0 < H → H ≤ H' → H' ≤ 2 * H →
        1 / 2 ≤ ‖Q‖ → ‖Q‖ ≤ L + 1 → 1 / 2 ≤ ‖Q'‖ → ‖Q'‖ ≤ L + 1 →
        IsCylinderFit (U i) w H (32 * lam i) Q →
        IsCylinderFit (U i) w H' (32 * lam i) Q' →
        ‖Q - Q'‖ + ‖‖Q‖⁻¹ • Q - ‖Q'‖⁻¹ • Q'‖ ≤ C₁ * th i ∧
        |‖Q‖ - ‖Q'‖| ≤ C₁ * th i ^ 2) ∧
      (∀ (i : ℕ) (w w' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (H : ℝ)
        (Q Q' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), i₂ ≤ i → 0 < H →
        1 / 2 ≤ ‖Q‖ → ‖Q‖ ≤ L + 1 → 1 / 2 ≤ ‖Q'‖ → ‖Q'‖ ≤ L + 1 →
        |(inner ℝ (‖Q‖⁻¹ • Q) (w' - w) : ℝ)| ≤ H / 4 →
        ‖(w' - w) - (inner ℝ (‖Q‖⁻¹ • Q) (w' - w) : ℝ) • (‖Q‖⁻¹ • Q)‖ ≤ th i * H / 4 →
        IsCylinderFit (U i) w H (32 * lam i) Q →
        IsCylinderFit (U i) w' H (32 * lam i) Q' →
        ‖Q - Q'‖ + ‖‖Q‖⁻¹ • Q - ‖Q'‖⁻¹ • Q'‖ ≤ C₁ * th i ∧
        |‖Q‖ - ‖Q'‖| ≤ C₁ * th i ^ 2) := by
    have hcC : (1 : ℝ) / 2 ≤ L + 1 := by linarith only [hL0]
    obtain ⟨Ca, hCa0, hCa⟩ := CylinderComparisonSameCenter
      (E := WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2) (L + 1) (by norm_num) hcC
    obtain ⟨Cb, hCb0, hCb⟩ := CylinderComparisonShifted
      (E := WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2) (L + 1) (by norm_num) hcC
    -- the common constant, and the two facts about `θ_i` that both applications need
    have hth0 : ∀ i, 0 < th i := by
      intro i
      rw [hthdef]
      exact Real.sqrt_pos.mpr (by linarith only [hlam0 i])
    have hthsq : ∀ i, th i ^ 2 = 32 * lam i := by
      intro i
      rw [hthdef]
      exact Real.sq_sqrt (by linarith only [hlam0 i])
    have hmaxa : Ca ≤ max 1 (max Ca Cb) :=
      le_trans (le_max_left Ca Cb) (le_max_right _ _)
    have hmaxb : Cb ≤ max 1 (max Ca Cb) :=
      le_trans (le_max_right Ca Cb) (le_max_right _ _)
    refine ⟨max 1 (max Ca Cb), le_max_left _ _, ?_, ?_⟩
    · intro i w H H' Q Q' hi hH hHH' hH'2 hQ1 hQ2 hQ'1 hQ'2 hfit hfit'
      have hth1 : th i < 1 := by linarith only [htail2 i hi]
      obtain ⟨g1, g2⟩ := hCa (U i) w (th i) H H' Q Q' (hth0 i) hth1 hH hHH' hH'2
        hQ1 hQ2 hQ'1 hQ'2 (by rw [hthsq i]; exact hfit) (by rw [hthsq i]; exact hfit')
      refine ⟨le_trans g1 ?_, le_trans g2 ?_⟩
      · exact mul_le_mul_of_nonneg_right hmaxa (le_of_lt (hth0 i))
      · exact mul_le_mul_of_nonneg_right hmaxa (by positivity)
    · intro i w w' H Q Q' hi hH hQ1 hQ2 hQ'1 hQ'2 hax htr hfit hfit'
      have hth1 : th i < 1 := by linarith only [htail2 i hi]
      obtain ⟨g1, g2⟩ := hCb (U i) w w' (th i) H Q Q' (hth0 i) hth1 hH
        hQ1 hQ2 hQ'1 hQ'2 hax htr (by rw [hthsq i]; exact hfit)
        (by rw [hthsq i]; exact hfit')
      refine ⟨le_trans g1 ?_, le_trans g2 ?_⟩
      · exact mul_le_mul_of_nonneg_right hmaxb (le_of_lt (hth0 i))
      · exact mul_le_mul_of_nonneg_right hmaxb (by positivity)
  -- ===================== STEP 3: THE CHAIN OF DOUBLINGS AT `z_i` ==============
  -- eq:nl-base-chain.  `C₂ = 2 C₁` absorbs `log₂ R ≤ 2 log R` for `R ≥ 2`; the
  -- `(1 + log R)` is the number of links in the chain and must not degrade to a
  -- constant.
  obtain ⟨C₂, hC₂0, hchain⟩ : ∃ C₂ : ℝ, 0 ≤ C₂ ∧
      ∀ R : ℝ, 2 ≤ R → ∀ M : ℝ, 2 ≤ M → R ≤ M → ∃ i₀ : ℕ, i₂ ≤ i₀ ∧ ∀ i ≥ i₀,
        ∃ PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (z i) (R * r i) (32 * lam i) PR ∧
          1 / 2 ≤ ‖PR‖ ∧ ‖PR‖ ≤ L + 1 ∧
          ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log R) * th i ∧
          |‖PR‖ - cc i| ≤ C₂ * (1 + Real.log R) * th i ^ 2 := by
    -- the whole chain argument is `CylinderFitDoublingChain` at the slope window
    -- `[1/2, L+1]` of eq:nl-slope; what is supplied here is the family of fits at every
    -- radius up to `R r_i`, which is `hgood` at `M ≥ R` together with eq:nl-slope.
    obtain ⟨Cd, hCd0, hdchain⟩ := CylinderFitDoublingChain
      (E := WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2) (L + 1) (by norm_num)
      (by linarith only [hL0])
    refine ⟨Cd, hCd0, ?_⟩
    intro R hR2 M hM2 hRM
    obtain ⟨j₀, hj₀⟩ := hgood M hM2
    refine ⟨max i₂ j₀, le_max_left _ _, ?_⟩
    intro i hi
    have hi2 : i₂ ≤ i := le_trans (le_max_left _ _) hi
    have hij : j₀ ≤ i := le_trans (le_max_right _ _) hi
    have hth0 : 0 < th i := by
      rw [hthdef]; exact Real.sqrt_pos.mpr (by linarith only [hlam0 i])
    have hth1 : th i < 1 := by linarith only [htail2 i hi2]
    have hthsq : th i ^ 2 = 32 * lam i := by
      rw [hthdef]; exact Real.sq_sqrt (by linarith only [hlam0 i])
    have hPl : 1 / 2 ≤ ‖P i‖ := by
      have h := (hbasenorm i hi2).1; rwa [hccdef] at h
    have hPu : ‖P i‖ ≤ L + 1 := by
      have h := (hbasenorm i hi2).2; rwa [hccdef] at h
    have hd0 : ‖z i - z i‖ ≤ M * r i := by
      rw [sub_self, norm_zero]
      nlinarith only [hM2, hr0 i]
    have hfits : ∀ rho : ℝ, 0 < rho → rho ≤ R * r i →
        ∃ Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (z i) rho (th i ^ 2) Q ∧ 1 / 2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ L + 1 := by
      intro rho hrho hrhole
      have hrhoM : rho ≤ M * r i := by
        have h := mul_le_mul_of_nonneg_right hRM (le_of_lt (hr0 i))
        linarith only [hrhole, h]
      obtain ⟨hzmem, hrhoD, Q, hQfit⟩ := hj₀ i hij (z i) hd0 rho hrho hrhoM
      refine ⟨Q, by rw [hthsq]; exact hQfit,
        hslope i hi2 (z i) hzmem rho hrho ?_ Q hQfit⟩
      simp only [hDddef]
      exact hrhoD
    obtain ⟨PR, h1, h2, h3, h4, h5⟩ := hdchain (U i) (z i) (r i) (th i) R (P i)
      (hr0 i) hth0 hth1 hR2 hPl hPu (by rw [hthsq]; exact hP i (le_trans hi₂i₁ hi2)) hfits
    refine ⟨PR, ?_, h2, h3, ?_, ?_⟩
    · rw [← hthsq]; exact h1
    · simp only [hccdef]; exact h4
    · simp only [hccdef]; exact h5
  -- ===================== STEP 6: THE EXACT INCREMENT IDENTITY ==================
  -- eq:nl-increment.  Pure algebra from `hv`: for any vector `Q` with normalized
  -- coefficients `(p', q')` in the frame `Φ i`, the fit defect of `Q` at the pair
  -- `(Z_i(w), ·)` is `r_i c_i λ_i` times the affine defect of `v_i`.  Stated here
  -- because Steps 7, 8 and 12 all consume it.
  have hincrement : ∀ i ≥ i₁,
      ∀ (w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        (h : EuclideanSpace ℝ (Fin d)) (l : ℝ)
        (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ)
        (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
        Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p', cc i * (1 + lam i * q'))) →
        U i (Zi i (w + toLp 2 (h, l))) - U i (Zi i w)
            - (inner ℝ Q (Zi i (w + toLp 2 (h, l)) - Zi i w) : ℝ)
          = r i * cc i * lam i *
            (v i (w + toLp 2 (h, l)) - v i w - (inner ℝ p' h : ℝ) - q' * l) := by
    intro i hi w h l p' q' Q hQ
    have hsq : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i :=
      Real.mul_self_sqrt (le_of_lt (hlam0 i))
    -- eq:nl-normalization, read along `Z_i`
    have hvZ : ∀ x : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        U i (Zi i x) = U i (z i) + r i * cc i * ((ofLp x).2 + lam i * v i x) := by
      intro x
      simp only [hZidef, hccdef]
      exact hv i hi x
    have e2 : (ofLp (w + toLp 2 (h, l))).2 = (ofLp w).2 + l := rfl
    -- the increment of `Z_i` is LINEAR in `(h, l)`, by linearity of `Φ i` and of `toLp`
    have hdiff : Zi i (w + toLp 2 (h, l)) - Zi i w
        = r i • Φ i (toLp 2 (Real.sqrt (lam i) • h, l)) := by
      simp only [hZidef]
      have e3 : (toLp 2 (Real.sqrt (lam i) • (ofLp (w + toLp 2 (h, l))).1,
              (ofLp (w + toLp 2 (h, l))).2) : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          = toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            + toLp 2 (Real.sqrt (lam i) • h, l) := by
        show (toLp 2 (Real.sqrt (lam i) • ((ofLp w).1 + h), (ofLp w).2 + l)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) = _
        rw [smul_add]
        rfl
      rw [e3, map_add, smul_add]
      abel
    -- the slope pairs against that increment through the isometry `Φ i`
    have hinner : (inner ℝ Q (Zi i (w + toLp 2 (h, l)) - Zi i w) : ℝ)
        = r i * (cc i * lam i * (inner ℝ p' h : ℝ) + cc i * l
          + cc i * lam i * q' * l) := by
      rw [hdiff, hQ, real_inner_smul_right, LinearIsometryEquiv.inner_map_map,
        WithLp.prod_inner_apply]
      simp only [real_inner_smul_left, real_inner_smul_right, RCLike.inner_apply,
        starRingEnd_apply, star_trivial]
      linear_combination (r i * cc i * (inner ℝ p' h : ℝ)) * hsq
    rw [hvZ (w + toLp 2 (h, l)), hvZ w, hinner, e2]
    ring
  -- ===================== STEPS 4 AND 5: THE BOX AND THE NEARBY FITS ===========
  -- eq:nl-R, eq:nl-disp, Claim 4a, eq:nl-cmp, eq:nl-coeff and eq:nl-coeff-bound,
  -- in one block because Step 5 consumes `R`, `M`, `i₃` and Claim 4a from Step 4.
  -- The block delivers, for each box radius `K` and each fit radius `S`:
  --   (i)  the ENCLOSING fit at `(z_i, R r_i)` whose cylinder contains `Z_i(Box K)`,
  --        with its normalized coefficients bounded by `C₃`;
  --   (ii) a fit at `(Z_i(w), S r_i)` for every `w ∈ Box K`, likewise bounded.
  -- ===================== STEP 4: THE RADIUS, THE BOX AND CLAIM 4a ============
  -- eq:nl-R.  The radius is chosen from `K` ALONE -- that is what makes Step 7's bound
  -- independent of `S`.  The choice is possible because `R / log R → ∞`; in Lean the
  -- asymptotics are replaced by the elementary `log x ≤ 2 √x`, which is all the
  -- inequality needs, and the `(1 + log R)` is the doubling count of eq:nl-base-chain.
  obtain ⟨Rad, hRad2, hRad16, hRadR⟩ : ∃ Rad : ℝ → ℝ,
      (∀ K : ℝ, 1 ≤ K → 2 ≤ Rad K) ∧
      (∀ K : ℝ, 1 ≤ K → 16 * K < Rad K) ∧
      (∀ K : ℝ, 1 ≤ K →
        K * ((Real.sqrt 32)⁻¹ + C₂ * (1 + Real.log (Rad K))) < Rad K / 4) := by
    have hlogle : ∀ x : ℝ, 1 ≤ x → Real.log x ≤ 2 * Real.sqrt x := by
      intro x hx
      have hx0 : (0 : ℝ) < x := by linarith only [hx]
      have hs : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
        Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx0)
      rw [Real.log_sqrt (le_of_lt hx0)] at hs
      linarith only [hs]
    have hs32 : (0 : ℝ) ≤ (Real.sqrt 32)⁻¹ := by positivity
    have key : ∀ K : ℝ, ∃ R : ℝ, 1 ≤ K → (2 ≤ R ∧ 16 * K < R ∧
        K * ((Real.sqrt 32)⁻¹ + C₂ * (1 + Real.log R)) < R / 4) := by
      intro K
      by_cases hK : 1 ≤ K
      · obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = 4 * K * ((Real.sqrt 32)⁻¹ + C₂) := ⟨_, rfl⟩
        obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 8 * K * C₂ := ⟨_, rfl⟩
        have hA0 : 0 ≤ A := by rw [hAdef]; nlinarith only [hK, hC₂0]
        obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = max (max 2 (16 * K + 1))
          (max (2 * B + 1) (4 * A ^ 2 + 1)) := ⟨_, rfl⟩
        have hR2 : 2 ≤ R := by
          rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
        have hR16 : 16 * K + 1 ≤ R := by
          rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
        have hRB : 2 * B + 1 ≤ R := by
          rw [hRdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
        have hRA : 4 * A ^ 2 + 1 ≤ R := by
          rw [hRdef]; exact le_trans (le_max_right _ _) (le_max_right _ _)
        have hR0 : (0 : ℝ) < R := by linarith only [hR2]
        refine ⟨R, fun _ => ⟨hR2, by linarith only [hR16], ?_⟩⟩
        -- `√R > 2A`, hence `A √R < R/2`
        have hsq : Real.sqrt (4 * A ^ 2) = 2 * A := by
          rw [show 4 * A ^ 2 = (2 * A) ^ 2 by ring]
          exact Real.sqrt_sq (by linarith only [hA0])
        have hsR : 2 * A < Real.sqrt R := by
          rw [← hsq]
          exact Real.sqrt_lt_sqrt (by positivity) (by linarith only [hRA])
        have hsR0 : 0 < Real.sqrt R := by linarith only [hsR, hA0]
        have hsRsq : Real.sqrt R * Real.sqrt R = R := Real.mul_self_sqrt (le_of_lt hR0)
        have hAsR : A * Real.sqrt R < R / 2 := by
          nlinarith only [hsR, hsR0, hsRsq, hA0]
        -- `log R ≤ 2 √R` is the elementary stand-in for `R / log R → ∞`
        have hlR := hlogle R (by linarith only [hR2])
        have h4KC : (0 : ℝ) ≤ 4 * K * C₂ := by nlinarith only [hK, hC₂0]
        have hKC : 4 * K * C₂ * Real.log R ≤ A * Real.sqrt R := by
          have h := mul_le_mul_of_nonneg_left hlR h4KC
          rw [hAdef]
          nlinarith only [h]
        linarith only [hKC, hAsR, hRB, hBdef]
      · exact ⟨2, fun h => absurd h hK⟩
    choose Rad hRad using key
    exact ⟨Rad, fun K hK => (hRad K hK).1, fun K hK => (hRad K hK).2.1,
      fun K hK => (hRad K hK).2.2⟩
  -- eq:nl-disp: `|Z_i(x,t) - z_i| = r_i |(√λ_i x, t)| ≤ r_i(√λ_i|x| + |t|) ≤ 2 K r_i`,
  -- using `λ_i ≤ 1` from eq:nl-tail and the fact that `Φ i` is an isometry.
  have hdisp : ∀ K : ℝ, 1 ≤ K → ∀ i ≥ i₂, ∀ w ∈ Box K,
      ‖Zi i w - z i‖ ≤ 2 * K * r i := by
    intro K hK i hi w hw
    rw [hBoxdef] at hw
    obtain ⟨hwx, hwt⟩ := hw
    have hlam1 : lam i ≤ 1 := by linarith only [htail1 i hi, hlam0 i]
    have hsl : Real.sqrt (lam i) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hlam1
    have hsl0 : 0 ≤ Real.sqrt (lam i) := Real.sqrt_nonneg _
    have hZ : Zi i w - z i
        = r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)) := by
      rw [hZidef]
      show z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)) - z i = _
      abel
    rw [hZ, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hr0 i)),
      LinearIsometryEquiv.norm_map]
    -- `‖(a, s)‖ ≤ ‖a‖ + |s|` in the `L²` product
    have hn : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ ≤ 2 * K := by
      have hsqn := WithLp.prod_norm_sq_eq_of_L2
        (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
      have he1 : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).fst‖
          = Real.sqrt (lam i) * ‖(ofLp w).1‖ := by
        show ‖Real.sqrt (lam i) • (ofLp w).1‖ = _
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsl0]
      have he2 : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).snd‖ = |(ofLp w).2| := rfl
      rw [he1, he2] at hsqn
      have hb1 : Real.sqrt (lam i) * ‖(ofLp w).1‖ ≤ K := by
        nlinarith only [hsl, hsl0, hwx, norm_nonneg (ofLp w).1, hK]
      have hb2 : |(ofLp w).2| ≤ K := hwt
      nlinarith only [hsqn, hb1, hb2, hK, abs_nonneg (ofLp w).2,
        mul_nonneg hsl0 (norm_nonneg (ofLp w).1),
        norm_nonneg (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))]
    calc r i * ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖
        ≤ r i * (2 * K) := mul_le_mul_of_nonneg_left hn (le_of_lt (hr0 i))
      _ = 2 * K * r i := by ring
  -- ===================== STEP 5: THE NORMALIZED COEFFICIENTS =================
  -- eq:nl-coeff and eq:nl-coeff-bound for ONE slope, which is where the two
  -- coefficients draw on DIFFERENT estimates: `p'` is transverse and uses only the
  -- `O(δ θ_i)` DIRECTION bound, while `q'` is longitudinal and uses the
  -- `O(δ θ_i²)` NORM bound PLUS the quadratic angular error `‖Q‖‖p - e‖²/2`.  Both
  -- land at a `θ`-free constant only because `θ_i² = 32 λ_i`.
  have hcoeff : ∀ i ≥ i₂, ∀ (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (δ : ℝ),
      0 ≤ δ → 1 / 2 ≤ ‖Q‖ → ‖Q‖ ≤ L + 1 →
      ‖‖Q‖⁻¹ • Q - (cc i)⁻¹ • P i‖ ≤ δ * th i → |‖Q‖ - cc i| ≤ δ * th i ^ 2 →
      ∃ (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
        Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p', cc i * (1 + lam i * q'))) ∧
        ‖p'‖ + |q'| ≤ 100 * (1 + L) * (δ + δ ^ 2) := by
    intro i hi Q δ hδ0 hQl hQu hdir hnorm
    have hi1 : i₁ ≤ i := le_trans hi₂i₁ hi
    have hQ0 : (0 : ℝ) < ‖Q‖ := by linarith only [hQl]
    have hccb := hbasenorm i hi
    have hcc0 : (0 : ℝ) < cc i := by linarith only [hccb.1]
    have hlam := hlam0 i
    have hsl0 : (0 : ℝ) < Real.sqrt (lam i) := Real.sqrt_pos.mpr hlam
    have hprod0 : (0 : ℝ) < cc i * Real.sqrt (lam i) := mul_pos hcc0 hsl0
    have hth0 : 0 ≤ th i := by rw [hthdef]; exact Real.sqrt_nonneg _
    have hthsq : th i ^ 2 = 32 * lam i := by
      rw [hthdef]; exact Real.sq_sqrt (by linarith only [hlam])
    have hth32 : th i = Real.sqrt 32 * Real.sqrt (lam i) := by
      rw [hthdef]; exact Real.sqrt_mul (by norm_num) (lam i)
    -- `Φ i (e_b) = (c_i)⁻¹ • P i` by `hΦ`, so the direction bound of eq:nl-cmp is
    -- exactly the hypothesis `NormalizedSlopeCoefficients` wants
    have hedir : ‖‖Q‖⁻¹ • Q
        - Φ i (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)))‖ ≤ δ * th i := by
      rw [hΦ i hi1]
      simp only [hccdef] at hdir
      exact hdir
    obtain ⟨p', q', heq, hpx, hqt⟩ := NormalizedSlopeCoefficients (Φ i) (cc i) (lam i)
      (δ * th i) (δ * th i ^ 2) Q hcc0 hlam hQ0 hedir hnorm
    refine ⟨p', q', heq, ?_⟩
    -- divide the two undivided estimates by `c_i √λ_i` and `c_i λ_i`, absorbing
    -- `√32 ≤ 6` and `c_i ≥ 1/2` into one constant
    have hs326 : Real.sqrt 32 ≤ 6 := by
      rw [show (6 : ℝ) = Real.sqrt 36 from by
        rw [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hX0 : (0 : ℝ) ≤ (1 + L) * δ * Real.sqrt (lam i) :=
      mul_nonneg (mul_nonneg (by linarith only [hL0]) hδ0) (le_of_lt hsl0)
    have hpb : ‖p'‖ ≤ 12 * (1 + L) * δ := by
      refine le_of_mul_le_mul_left ?_ hprod0
      have h1 : ‖Q‖ * (δ * th i)
          ≤ (L + 1) * (δ * (Real.sqrt 32 * Real.sqrt (lam i))) := by
        rw [← hth32]
        exact mul_le_mul_of_nonneg_right hQu (mul_nonneg hδ0 hth0)
      have hfac : (0 : ℝ) ≤ ((1 + L) * δ * Real.sqrt (lam i))
          * (12 * cc i - Real.sqrt 32) :=
        mul_nonneg hX0 (by linarith only [hccb.1, hs326])
      linarith only [hpx, h1, hfac]
    have hqb : |q'| ≤ 64 * δ + 32 * (1 + L) * δ ^ 2 := by
      refine le_of_mul_le_mul_left ?_ (mul_pos hcc0 hlam)
      have h1 : δ * th i ^ 2 + ‖Q‖ * (δ * th i) ^ 2 / 2
          ≤ 32 * lam i * δ + (L + 1) * (δ ^ 2 * (32 * lam i)) / 2 := by
        have h3 : (δ * th i) ^ 2 = δ ^ 2 * (32 * lam i) := by
          rw [show (δ * th i) ^ 2 = δ ^ 2 * th i ^ 2 from by ring, hthsq]
        rw [h3, hthsq]
        have h4 : ‖Q‖ * (δ ^ 2 * (32 * lam i)) ≤ (L + 1) * (δ ^ 2 * (32 * lam i)) :=
          mul_le_mul_of_nonneg_right hQu
            (mul_nonneg (sq_nonneg δ) (by linarith only [hlam]))
        linarith only [h4]
      have hfac : (0 : ℝ) ≤ (lam i * δ) * (64 * cc i - 32) :=
        mul_nonneg (mul_nonneg (le_of_lt hlam) hδ0) (by linarith only [hccb.1])
      have hfac2 : (0 : ℝ) ≤ (lam i * δ ^ 2) * ((1 + L) * (32 * cc i) - 16 * (L + 1)) :=
        mul_nonneg (mul_nonneg (le_of_lt hlam) (sq_nonneg δ))
          (by nlinarith only [hccb.1, hL0])
      linarith only [hqt, h1, hfac, hfac2]
    have hfin : 12 * (1 + L) * δ + (64 * δ + 32 * (1 + L) * δ ^ 2)
        ≤ 100 * (1 + L) * (δ + δ ^ 2) := by
      have h1 : (0 : ℝ) ≤ L * δ := mul_nonneg hL0 hδ0
      have h2 : (0 : ℝ) ≤ (1 + L) * δ ^ 2 :=
        mul_nonneg (by linarith only [hL0]) (sq_nonneg δ)
      nlinarith only [h1, h2, hδ0, hL0, sq_nonneg δ]
    linarith only [hpb, hqb, hfin]
  -- ===================== STEP 4, PART 3: THE ENLARGED SCALE AND THRESHOLD ====
  -- `M(K,S)` is chosen past `2K`, past `R(K)` and past `S`, so that `hgood` supplies a
  -- fit at EVERY radius up to `M(K,S) r_i`, both at `z_i` and at any `Z_i(w)` with
  -- `w ∈ Box K` (the latter because eq:nl-disp puts `Z_i(w)` within `2K r_i` of `z_i`).
  obtain ⟨Mof, iadm, hMofK, hMofR, hMofS, hiadm, hfitz, hfitw⟩ :
      ∃ (Mof : ℝ → ℝ → ℝ) (iadm : ℝ → ℝ → ℕ),
        (∀ K S : ℝ, 1 ≤ K → 0 < S → 2 * K ≤ Mof K S) ∧
        (∀ K S : ℝ, 1 ≤ K → 0 < S → Rad K ≤ Mof K S) ∧
        (∀ K S : ℝ, 1 ≤ K → 0 < S → S ≤ Mof K S) ∧
        (∀ K S : ℝ, i₂ ≤ iadm K S) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ iadm K S,
          ∀ rho : ℝ, 0 < rho → rho ≤ Mof K S * r i →
          ∃ Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit (U i) (z i) rho (32 * lam i) Q ∧
            1 / 2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ L + 1) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ iadm K S, ∀ w ∈ Box K,
          ∀ rho : ℝ, 0 < rho → rho ≤ Mof K S * r i →
          ∃ Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
            IsCylinderFit (U i) (Zi i w) rho (32 * lam i) Q ∧
            1 / 2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ L + 1) := by
    -- `hgood` as a total function of `M`
    have hgood' : ∀ M : ℝ, ∃ j : ℕ, 2 ≤ M → ∀ i ≥ j,
        ∀ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖w - z i‖ ≤ M * r i →
        ∀ rho : ℝ, 0 < rho → rho ≤ M * r i →
          w ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4) ∧
          rho ≤ 1 / 8 * infDist w
            (frontier (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))) ∧
          ∃ Q, IsCylinderFit (U i) w rho (32 * lam i) Q := by
      intro M
      by_cases hM : 2 ≤ M
      · obtain ⟨j, hj⟩ := hgood M hM
        exact ⟨j, fun _ => hj⟩
      · exact ⟨0, fun h => absurd h hM⟩
    choose jof hjof using hgood'
    obtain ⟨Mof, hMofdef⟩ : ∃ Mof : ℝ → ℝ → ℝ,
        Mof = fun K S => max (max 2 (2 * K)) (max (Rad K) S) + 1 := ⟨_, rfl⟩
    have hbig : ∀ K S : ℝ, max 2 (2 * K) ≤ max (max 2 (2 * K)) (max (Rad K) S) ∧
        max (Rad K) S ≤ max (max 2 (2 * K)) (max (Rad K) S) :=
      fun K S => ⟨le_max_left _ _, le_max_right _ _⟩
    have hMof2 : ∀ K S : ℝ, 2 ≤ Mof K S := by
      intro K S
      rw [hMofdef]
      show (2 : ℝ) ≤ max (max 2 (2 * K)) (max (Rad K) S) + 1
      linarith only [(hbig K S).1, le_max_left (2 : ℝ) (2 * K)]
    have hMofKk : ∀ K S : ℝ, 1 ≤ K → 0 < S → 2 * K ≤ Mof K S := by
      intro K S _ _
      rw [hMofdef]
      show 2 * K ≤ max (max 2 (2 * K)) (max (Rad K) S) + 1
      linarith only [(hbig K S).1, le_max_right (2 : ℝ) (2 * K)]
    have hMofRr : ∀ K S : ℝ, 1 ≤ K → 0 < S → Rad K ≤ Mof K S := by
      intro K S _ _
      rw [hMofdef]
      show Rad K ≤ max (max 2 (2 * K)) (max (Rad K) S) + 1
      linarith only [(hbig K S).2, le_max_left (Rad K) S]
    have hMofSs : ∀ K S : ℝ, 1 ≤ K → 0 < S → S ≤ Mof K S := by
      intro K S _ _
      rw [hMofdef]
      show S ≤ max (max 2 (2 * K)) (max (Rad K) S) + 1
      linarith only [(hbig K S).2, le_max_right (Rad K) S]
    refine ⟨Mof, fun K S => max i₂ (jof (Mof K S)), hMofKk, hMofRr, hMofSs,
      fun K S => le_max_left _ _, ?_, ?_⟩
    · intro K hK S hS i hi rho hrho hrhole
      have hi2 : i₂ ≤ i := le_trans (le_max_left _ _) hi
      have hij : jof (Mof K S) ≤ i := le_trans (le_max_right _ _) hi
      have hd0 : ‖z i - z i‖ ≤ Mof K S * r i := by
        rw [sub_self, norm_zero]
        nlinarith only [hMof2 K S, hr0 i]
      obtain ⟨hzmem, hrhoD, Q, hQfit⟩ :=
        hjof (Mof K S) (hMof2 K S) i hij (z i) hd0 rho hrho hrhole
      refine ⟨Q, hQfit, hslope i hi2 (z i) hzmem rho hrho ?_ Q hQfit⟩
      simp only [hDddef]
      exact hrhoD
    · intro K hK S hS i hi w hw rho hrho hrhole
      have hi2 : i₂ ≤ i := le_trans (le_max_left _ _) hi
      have hij : jof (Mof K S) ≤ i := le_trans (le_max_right _ _) hi
      have hdw : ‖Zi i w - z i‖ ≤ Mof K S * r i := by
        refine le_trans (hdisp K hK i hi2 w hw) ?_
        exact mul_le_mul_of_nonneg_right (hMofKk K S hK hS) (le_of_lt (hr0 i))
      obtain ⟨hzmem, hrhoD, Q, hQfit⟩ :=
        hjof (Mof K S) (hMof2 K S) i hij (Zi i w) hdw rho hrho hrhole
      refine ⟨Q, hQfit, hslope i hi2 (Zi i w) hzmem rho hrho ?_ Q hQfit⟩
      simp only [hDddef]
      exact hrhoD
  -- ===================== CLAIM 4a ===========================================
  -- The box lands in the QUARTER cylinder of the enclosing fit, which is both what
  -- `FitCylinder` membership needs (a fortiori) and what Step 2(b)'s two centre-offset
  -- hypotheses need (exactly).  This is the one place eq:nl-R is consumed, and the whole
  -- geometric content -- the length bound eq:nl-disp, the projection inequality and the
  -- frame splitting -- is `AnisotropicBoxOffsets`.  Here we only instantiate it, with
  -- `Cb = C₂(1 + log R)` absorbing the chain factor so the node never sees a logarithm.
  have hclaim4a : ∀ K : ℝ, 1 ≤ K → ∀ i ≥ i₂,
      ∀ PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), 1 / 2 ≤ ‖PR‖ →
      ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log (Rad K)) * th i →
      ∀ w ∈ Box K,
        |(inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ)| ≤ Rad K * r i / 4 ∧
        ‖(Zi i w - z i)
            - (inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ) • (‖PR‖⁻¹ • PR)‖
          ≤ th i * (Rad K * r i) / 4 := by
    intro K hK i hi PR hPRl hPRdir w hw
    have hi1 : i₁ ≤ i := le_trans hi₂i₁ hi
    have hPR0 : (0 : ℝ) < ‖PR‖ := by linarith only [hPRl]
    have hnRn : ‖‖PR‖⁻¹ • PR‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hPR0)), inv_mul_cancel₀ (ne_of_gt hPR0)]
    rw [hBoxdef] at hw
    obtain ⟨hwx, hwt⟩ := hw
    have hlam1 : lam i ≤ 1 := by linarith only [htail1 i hi, hlam0 i]
    have hsl1 : Real.sqrt (lam i) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hlam1
    have hth0 : (0 : ℝ) ≤ th i := by rw [hthdef]; exact Real.sqrt_nonneg _
    have hslth : Real.sqrt (lam i) * Real.sqrt 32 = th i := by
      rw [hthdef]
      show Real.sqrt (lam i) * Real.sqrt 32 = Real.sqrt (32 * lam i)
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32) (lam i)]
      ring
    have hlogR : (0 : ℝ) ≤ Real.log (Rad K) :=
      Real.log_nonneg (by linarith only [hRad2 K hK])
    have hCb0 : (0 : ℝ) ≤ C₂ * (1 + Real.log (Rad K)) :=
      mul_nonneg hC₂0 (by linarith only [hlogR])
    -- `Φ i (e_b) = (cc i)⁻¹ • P i`, so eq:nl-base-chain's direction bound is the node's
    have hdirn : ‖Φ i (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)))
        - ‖PR‖⁻¹ • PR‖ ≤ C₂ * (1 + Real.log (Rad K)) * th i := by
      have hcc : Φ i (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)))
          = (cc i)⁻¹ • P i := by rw [hΦ i hi1]; simp only [hccdef]
      rw [hcc, norm_sub_rev]
      exact hPRdir
    have hZ : Zi i w - z i
        = r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)) := by
      rw [hZidef]
      show z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)) - z i = _
      abel
    rw [hZ]
    exact AnisotropicBoxOffsets (Φ i) (r i) (Real.sqrt (lam i)) (th i) K (Rad K)
      (C₂ * (1 + Real.log (Rad K))) (‖PR‖⁻¹ • PR) (ofLp w).1 (ofLp w).2
      (hr0 i) hth0 (Real.sqrt_nonneg _) hsl1 hslth hK hCb0 hnRn hdirn
      (hRad16 K hK) (hRadR K hK) hwx hwt
  -- ===================== STEP 5: THE ENCLOSING AND NEARBY FITS =============
  obtain ⟨CR, ifitR, CN, ifitN, hCR0, hifitR, henclR, hCN0, hifitN, hnearbyN⟩ :=
    EnclosingAndNearbyFits d r lam U z P Φ th cc Zi Box Rad Mof iadm L C₁ C₂ i₂
      hr0 hlam0 hL0 hthdef htail2 hC₁1 hcmpA hcmpB hC₂0 hchain hRad2 hMofK hMofR
      hMofS hiadm hfitw hcoeff hclaim4a
  -- ===================== STEPS 4/5: THE TWO FAMILIES, ONE CONSTANT ===========
  -- eq:nl-cmp, eq:nl-coeff and eq:nl-coeff-bound in the form Steps 7 and 8 consume: one
  -- constant `C₃(K,S)` and one threshold serving both families.
  obtain ⟨Cthree, ifit, hCthree0, hifit, henclose, hnearby⟩ :
      ∃ (Cthree : ℝ → ℝ → ℝ) (ifit : ℝ → ℝ → ℕ),
        (∀ K S : ℝ, 0 ≤ Cthree K S) ∧
        (∀ K S : ℝ, iadm K S ≤ ifit K S) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifit K S,
          ∃ (PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
            (pR : EuclideanSpace ℝ (Fin d)) (qR : ℝ),
            IsCylinderFit (U i) (z i) (Rad K * r i) (32 * lam i) PR ∧
            PR = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • pR,
              cc i * (1 + lam i * qR))) ∧
            ‖pR‖ + |qR| ≤ Cthree K S ∧
            ∀ w ∈ Box K, Zi i w ∈ FitCylinder (z i) (Rad K * r i) (32 * lam i) PR) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifit K S, ∀ w ∈ Box K,
          ∃ (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
            (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
            IsCylinderFit (U i) (Zi i w) (S * r i) (32 * lam i) Q ∧
            Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p',
              cc i * (1 + lam i * q'))) ∧
            ‖p'‖ + |q'| ≤ Cthree K S) := by
    refine ⟨fun K S => max (CR K S) (CN K S), ifitN,
      fun K S => le_trans (hCR0 K S) (le_max_left _ _),
      fun K S => le_trans (hifitR K S) (hifitN K S), ?_, ?_⟩
    · intro K hK S hS i hi
      obtain ⟨PR, pR, qR, hfit, -, -, heq, hbd, hcyl, -, -, -⟩ :=
        henclR K hK S hS i (le_trans (hifitN K S) hi)
      exact ⟨PR, pR, qR, hfit, heq, le_trans hbd (le_max_left _ _), hcyl⟩
    · intro K hK S hS i hi w hw
      obtain ⟨Q, p', q', hfit, heq, hbd⟩ := hnearbyN K hK S hS i hi w hw
      exact ⟨Q, p', q', hfit, heq, le_trans hbd (le_max_right _ _)⟩
  -- ===================== STEP 7: A UNIFORM BOUND ON EACH BOX ==================
  -- eq:nl-bound, from the enclosing fit at `S = R(K)` through eq:nl-increment at
  -- `(x,t) = (0,0)` and eq:nl-origin.  The bound depends on `K` alone, because `R` was
  -- fixed from `K` alone in Step 4.  Three lines of paper, three blocks here: the
  -- increment identity at the base point `0`, the cylinder fit's own bound at the point
  -- `Z_i(w)` that Claim 4a put in the cylinder, and the division by `r_i c_i λ_i`.
  obtain ⟨Abd, ifour, hifour, hbound⟩ : ∃ (Abd : ℝ → ℝ) (ifour : ℝ → ℕ),
      (∀ K : ℝ, i₂ ≤ ifour K) ∧
      (∀ K : ℝ, 1 ≤ K → ∀ i ≥ ifour K, ∀ w ∈ Box K, |v i w| ≤ Abd K) := by
    refine ⟨fun K => 64 * Rad K + Cthree K (Rad K) * K,
      fun K => max i₂ (ifit K (Rad K)), fun K => le_max_left _ _, ?_⟩
    intro K hK i hi y hy
    have hi2 : i₂ ≤ i := le_trans (le_max_left _ _) hi
    have hi1 : i₁ ≤ i := le_trans hi₂i₁ hi2
    have hifitle : ifit K (Rad K) ≤ i := le_trans (le_max_right _ _) hi
    have hRad0 : (0 : ℝ) < Rad K := by linarith only [hRad2 K hK]
    have hr := hr0 i
    have hlam := hlam0 i
    have hccb := hbasenorm i hi2
    obtain ⟨PR, pR, qR, hfit, heq, hbd, hcyl⟩ := henclose K hK (Rad K) hRad0 i hifitle
    -- the base point of the increment identity is `0`, where `Z_i(0) = z_i`
    have hy0 : (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        + toLp 2 ((ofLp y).1, (ofLp y).2) = y := by
      rw [show (toLp 2 ((ofLp y).1, (ofLp y).2) : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        = y from rfl, zero_add]
    have hZ0 : Zi i 0 = z i := by
      rw [hZidef]
      show z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (0 : EuclideanSpace ℝ (Fin d)),
        (0 : ℝ))) = z i
      rw [smul_zero,
        show (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (0 : ℝ))
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) = 0 from rfl,
        map_zero, smul_zero, add_zero]
    have hinc := hincrement i hi1 0 (ofLp y).1 (ofLp y).2 pR qR PR heq
    rw [hy0, hZ0, horigin i hi1] at hinc
    -- the cylinder fit's bound at `Z_i(y)`, which Claim 4a put in the cylinder
    have hmem := hcyl y hy
    have hbnd := hfit.2 (Zi i y) hmem
    rw [hinc] at hbnd
    -- the division by `r_i c_i λ_i`
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ,
        E = v i y - 0 - (inner ℝ pR (ofLp y).1 : ℝ) - qR * (ofLp y).2 := ⟨_, rfl⟩
    rw [← hEdef] at hbnd
    have habs : r i * cc i * lam i * |E| ≤ 32 * lam i * (Rad K * r i) := by
      have hco : (0 : ℝ) ≤ r i * cc i * lam i := by
        have h := hccb.1
        positivity
      rw [← abs_of_nonneg hco, ← abs_mul]
      exact hbnd
    have hrl : (0 : ℝ) < r i * lam i := mul_pos hr hlam
    have hkey : |E| ≤ 64 * Rad K := by
      have h1 : r i * (1 / 2) * lam i * |E| ≤ r i * cc i * lam i * |E| := by
        have hc := hccb.1
        have hnn : (0 : ℝ) ≤ r i * lam i * |E| := by positivity
        nlinarith only [hc, hnn]
      have h3 : r i * lam i * |E| ≤ r i * lam i * (64 * Rad K) := by
        nlinarith only [h1, habs]
      exact le_of_mul_le_mul_left h3 hrl
    -- and the two coefficient terms on the box
    rw [hBoxdef] at hy
    obtain ⟨hyx, hyt⟩ := hy
    have hK0 : (0 : ℝ) ≤ K := by linarith only [hK]
    have hpn : ‖pR‖ + |qR| ≤ Cthree K (Rad K) := hbd
    have hinn : |(inner ℝ pR (ofLp y).1 : ℝ)| ≤ ‖pR‖ * K := by
      have hcs := abs_real_inner_le_norm pR (ofLp y).1
      have h1 : ‖pR‖ * ‖(ofLp y).1‖ ≤ ‖pR‖ * K :=
        mul_le_mul_of_nonneg_left hyx (norm_nonneg pR)
      linarith only [hcs, h1]
    have hql : |qR * (ofLp y).2| ≤ |qR| * K := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hyt (abs_nonneg qR)
    have hsum : ‖pR‖ * K + |qR| * K ≤ Cthree K (Rad K) * K := by
      nlinarith only [hpn, hK0]
    have hEy : v i y = E + (inner ℝ pR (ofLp y).1 : ℝ) + qR * (ofLp y).2 := by
      rw [hEdef]; ring
    have he1 := abs_le.mp hkey
    have he2 := abs_le.mp hinn
    have he3 := abs_le.mp hql
    rw [hEy, abs_le]
    constructor
    · linarith only [he1.1, he2.1, he3.1, hsum]
    · linarith only [he1.2, he2.2, he3.2, hsum]
  -- ===================== STEP 8: THE INCREMENT ESTIMATE =======================
  -- eq:nl-small, Claim 8a and eq:nl-fit.  Claim 8a is now a CITATION of
  -- `ShearedBoxInFitCylinder` -- this is the first consumption of that node -- and what
  -- is left here is eq:nl-small (the λ-smallness threshold, from `lam i → 0`), the
  -- `1/2 ≤ 1 + λ_i q'` threshold it implies, the identification of
  -- `Z_i(w + (h,l))` with `Z_i(w) + r_i Φ_i(√λ_i h, l)`, and the division of
  -- eq:physical-fit by `r_i c_i λ_i` through `hincrement`.
  -- The coefficient `2Λ = 64` of `S` does not depend on `K` or `S`; that independence is
  -- what Step 9's ε/2 + ε/2 split consumes.
  obtain ⟨ifive, hifive, hfit⟩ : ∃ ifive : ℝ → ℝ → ℕ,
      (∀ K S : ℝ, ifit K S ≤ ifive K S) ∧
      (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifive K S, ∀ w ∈ Box K,
        ∃ (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
          ‖p'‖ + |q'| ≤ Cthree K S ∧ 1 / 2 ≤ 1 + lam i * q' ∧
          ∀ (h : EuclideanSpace ℝ (Fin d)) (l : ℝ), |l| ≤ S / 2 →
            ‖h - (l / (1 + lam i * q')) • p'‖ ≤ S →
            |v i (w + toLp 2 (h, l)) - v i w - (inner ℝ p' h : ℝ) - q' * l|
              ≤ 64 * S) := by
    -- eq:nl-small, as a total function of `(K, S)`: `λ_i → 0` and `C₃(K,S)` is fixed
    have hsm : ∀ K S : ℝ, ∃ j : ℕ, ∀ i ≥ j,
        lam i * (Cthree K S ^ 2 + Cthree K S + 1) ≤ 1 / 100 := by
      intro K S
      obtain ⟨B, hBdef⟩ : ∃ B : ℝ, B = Cthree K S ^ 2 + Cthree K S + 1 := ⟨_, rfl⟩
      have hB0 : (0 : ℝ) < B := by
        rw [hBdef]; nlinarith only [hCthree0 K S]
      have hev : ∀ᶠ i in atTop, lam i < 1 / (100 * B) :=
        hlamlim.eventually_lt_const (by positivity)
      obtain ⟨j, hj⟩ := Filter.eventually_atTop.mp hev
      refine ⟨j, fun i hi => ?_⟩
      rw [← hBdef]
      have h2 : lam i * B < 1 / (100 * B) * B :=
        mul_lt_mul_of_pos_right (hj i hi) hB0
      have h3 : 1 / (100 * B) * B = 1 / 100 := by field_simp
      rw [h3] at h2
      exact le_of_lt h2
    choose jsm hjsm using hsm
    refine ⟨fun K S => max (ifit K S) (jsm K S), fun K S => le_max_left _ _, ?_⟩
    intro K hK S hS i hi w hw
    have hifitle : ifit K S ≤ i := le_trans (le_max_left _ _) hi
    have hjle : jsm K S ≤ i := le_trans (le_max_right _ _) hi
    have hi2 : i₂ ≤ i := le_trans (hiadm K S) (le_trans (hifit K S) hifitle)
    have hi1 : i₁ ≤ i := le_trans hi₂i₁ hi2
    have hr := hr0 i
    have hlam := hlam0 i
    have hccb := hbasenorm i hi2
    have hsmi := hjsm K S i hjle
    obtain ⟨Q, p', q', hQfit, hQeq, hQbd⟩ := hnearby K hK S hS i hifitle w hw
    -- `1/2 ≤ 1 + λ_i q'`, from eq:nl-small and `|q'| ≤ C₃(K,S)`
    have hC0 : (0 : ℝ) ≤ Cthree K S := hCthree0 K S
    have hq'C : |q'| ≤ Cthree K S := by linarith only [hQbd, norm_nonneg p']
    have habsq : |lam i * q'| ≤ 1 / 100 := by
      rw [abs_mul, abs_of_pos hlam]
      have h1 : lam i * |q'| ≤ lam i * Cthree K S :=
        mul_le_mul_of_nonneg_left hq'C (le_of_lt hlam)
      nlinarith only [h1, hsmi, hlam, hC0]
    have hA : 1 / 2 ≤ 1 + lam i * q' := by
      have h := abs_le.mp habsq
      linarith only [h.1]
    refine ⟨p', q', hQbd, hA, ?_⟩
    intro h l hl hh
    -- `Z_i` is affine in the normalized coordinates, so the increment splits off
    have hZadd : Zi i (w + toLp 2 (h, l))
        = Zi i w + r i • Φ i (toLp 2 (Real.sqrt (lam i) • h, l)) := by
      have h1 : ofLp ((toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          + toLp 2 (Real.sqrt (lam i) • h, l))
          = (Real.sqrt (lam i) • ((ofLp w).1 + h), (ofLp w).2 + l) := by
        refine Prod.ext ?_ ?_
        · show Real.sqrt (lam i) • (ofLp w).1 + Real.sqrt (lam i) • h
              = Real.sqrt (lam i) • ((ofLp w).1 + h)
          rw [smul_add]
        · rfl
      have hsum : (toLp 2 (Real.sqrt (lam i) • ((ofLp w).1 + h), (ofLp w).2 + l)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          = toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            + toLp 2 (Real.sqrt (lam i) • h, l) := by
        calc (toLp 2 (Real.sqrt (lam i) • ((ofLp w).1 + h), (ofLp w).2 + l)
              : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
            = toLp 2 (ofLp ((toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
                : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
              + toLp 2 (Real.sqrt (lam i) • h, l))) := by rw [h1]
          _ = _ := rfl
      rw [hZidef]
      show z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • ((ofLp w).1 + h),
            (ofLp w).2 + l))
          = z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2))
            + r i • Φ i (toLp 2 (Real.sqrt (lam i) • h, l))
      rw [hsum, map_add, smul_add]
      abel
    -- CLAIM 8a, as a citation
    have hmem : Zi i (w + toLp 2 (h, l))
        ∈ FitCylinder (Zi i w) (S * r i) (32 * lam i) Q := by
      rw [hZadd, hQeq]
      exact ShearedBoxInFitCylinder (Φ i) (Zi i w) (cc i) (lam i) S (Cthree K S) (r i)
        p' h q' l (by linarith only [hccb.1]) hlam hS hr hQbd hA hsmi hl hh
    -- eq:physical-fit, then the division by `r_i c_i λ_i`
    have hbnd := hQfit.2 _ hmem
    have hinc := hincrement i hi1 w h l p' q' Q hQeq
    rw [hinc] at hbnd
    obtain ⟨E, hEdef⟩ : ∃ E : ℝ,
        E = v i (w + toLp 2 (h, l)) - v i w - (inner ℝ p' h : ℝ) - q' * l := ⟨_, rfl⟩
    rw [← hEdef] at hbnd
    have habs : r i * cc i * lam i * |E| ≤ 32 * lam i * (S * r i) := by
      have hco : (0 : ℝ) ≤ r i * cc i * lam i := by
        have hc := hccb.1
        positivity
      rw [← abs_of_nonneg hco, ← abs_mul]
      exact hbnd
    have hrl : (0 : ℝ) < r i * lam i := mul_pos hr hlam
    rw [← hEdef]
    have h1 : r i * (1 / 2) * lam i * |E| ≤ r i * cc i * lam i * |E| := by
      have hc := hccb.1
      have hnn : (0 : ℝ) ≤ r i * lam i * |E| := by positivity
      nlinarith only [hc, hnn]
    have h3 : r i * lam i * |E| ≤ r i * lam i * (64 * S) := by
      nlinarith only [h1, habs]
    exact le_of_mul_le_mul_left h3 hrl
  -- ===================== STEP 9: EQUICONTINUITY AND THE SUBSEQUENCE ===========
  -- eq:nl-equicont and eq:nl-v0.  The whole extraction PACKAGE -- the subsequence past
  -- `i₁`, the CONTINUITY of the limit (which local uniform convergence does not give)
  -- and `w(0) = 0` -- comes from `AsymptEquicontOriginNormalizedLimit`, and the two
  -- interface derivations that feed it -- Step 7's bound on `Box K` transported to a
  -- Euclidean ball, and Step 8's increment estimate turned into an asymptotic modulus
  -- by the ε/2 + ε/2 split -- are inside
  -- `NonaffineLimitEquicontinuousSubsequence`.
  obtain ⟨psi, vlim, hpsimono, hpsige, hvcont, hvconv, hv0⟩ :=
    NonaffineLimitEquicontinuousSubsequence d lam v i₁ Box Abd ifour Cthree ifive
      hBoxdef horigin hbound hCthree0 hfit
  -- ===================== STEP 10: THE LIMITING EQUATION =======================
  -- `RescaledEquation` after `NormalizedInfFamily` and `LinearLift`, then
  -- `RescaledLimitStability` on each bounded open ball after the TAIL SHIFT, then the
  -- gluing by `LimitSolutionLocalToGlobal`.  All three live inside
  -- `NonaffineLimitIsLimitSolution`; what is prepared here is only the degeneration of
  -- the radii, which is what makes that node's tail shift possible.
  -- `r_i → 0`, from `r i ≤ s i * D(z i)`, `D ≤ 3/4` on `G` and `s i → 0`.
  have hrlim : Tendsto r atTop (𝓝 0) := by
    refine squeeze_zero (g := fun i => 3 / 4 * s i) (fun i => le_of_lt (hr0 i))
      (fun i => ?_) ?_
    · have h1 := hrle i
      have h2 := hDle (z i) (hzG i)
      rw [hDddef] at h2
      nlinarith only [h1, h2, hs0 i]
    · have h := hslim.const_mul (3 / 4 : ℝ)
      rw [mul_zero] at h
      exact h
  have hlimsol := NonaffineLimitIsLimitSolution d r lam cc U z Φ v i₁ i₂ psi vlim
    hr0 hrlim hlam0 hlamlim (fun i hi => by linarith only [htail1 i hi, hlam0 i])
    hzG hUnorm hcc0 (fun i hi w => by simp only [hccdef]; exact hv i hi w)
    hpsimono hpsige hvcont hvconv
  -- ===================== STEP 11: THE FITS ====================================
  -- eq:nl-fit at `S = 4R'`, a Bolzano--Weierstrass extraction of the coefficients
  -- along a further subsequence, and the passage to the limit on the compact
  -- sheared box.  `C₀ = 8Λ = 256`.
  have hfits := LimitIsFitAtEveryScale d lam v Box Cthree ifive psi vlim hlam0
    hlamlim hBoxdef hCthree0 hpsimono hvconv hfit
  -- ===================== STEP 12: `v` IS NOT AFFINE ===========================
  -- If it were, `P̃_i = c_i Φ_i(√λ_i p, 1 + λ_i q)` would realize a cylinder fit of
  -- parameter `λ_i` -- not `32 λ_i` -- at `(z_i, r_i)` for large `i`, contradicting
  -- `hbad`.  eq:nl-v0 forces the constant to vanish, and every point of every such
  -- cylinder has normalized coordinates in one fixed box.
  have hnonaffine := NormalizedLimitNotAffine d r lam U z Φ v Zi cc L hL0 i₁ i₂ hi₂i₁
    psi vlim hlam0 hlamlim hr0 hbad hZidef hbasenorm htail1 horigin hincrement
    hpsimono hvconv hv0
  -- ===================== THE CONCLUSION =======================================
  refine ⟨256, psi, vlim, by norm_num, hpsimono, hpsige, hvcont, hvconv, ?_, hnonaffine⟩
  rw [IsFitClass]
  exact ⟨hlimsol, fun zhat R' hR' => hfits zhat R' hR'⟩
