import InfHarmonic.MainEstimate
import InfHarmonic.InfHarmonicRescale
open Metric Set

/-- Corollary 1.2 (interior `C¹` regularity): a continuous infinity-harmonic
function on a nonempty connected open subset of `ℝ^d`, `d ≥ 3`, is
continuously differentiable there. -/
theorem InteriorC1 (d : ℕ) (hd : 3 ≤ d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hconn : IsConnected Ω) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : IsInfHarmonicOn Ω u) : ContDiffOn ℝ 1 u Ω := by
  classical
  -- ===================================================================
  -- PROOF MAP.  paper.tex:102-107 is five lines; four of the five pieces below are ours.
  --
  --   `hrestrict`  Infinity-harmonicity restricts to OPEN subsets.  THE nhdsWithin TRAP:
  --                the sub/supersolution clauses quantify over `IsLocalMaxOn … Ω z`, which
  --                is `∀ᶠ x in 𝓝[Ω] z`.  We are HANDED the SMALL set's clause and NEED the
  --                BIG set's, which is the direction `nhdsWithin_mono` does NOT give.  It
  --                is legal only because `W` is open: `IsOpen.nhdsWithin_eq` turns
  --                `𝓝[W] z` into the full `𝓝 z`, and `nhdsWithin_le_nhds` then descends to
  --                `𝓝[Ω'] z`.  Same mechanism, same direction as `NonaffineLimit` Step 10.
  --   Step 1-2     `InfHarmonicRescale` at `A = 2r`, then `hrestrict` down to `ball 0 1`.
  --   Step 3       `MainEstimate`'s two `Bdd` hypotheses come from continuity on the
  --                COMPACT `closedBall x₀ (2r) ⊆ Ω` -- which is why the paper's ball is
  --                CLOSED and of radius `2r` rather than open of radius `r`.
  --   Step 4       The gradient field's continuity on `ball 0 (1/2)` is its Hölder bound.
  --                `le_csSup` needs only `BddAbove`, so the `.tex`'s nonemptiness remark
  --                (two distinct points in `B_{1/2}`) is not needed in Lean (pm-0026).
  --                `max K 1` avoids ever having to prove `K ≥ 0`.
  --   Step 5       THE UNSCALING RADIUS IS `r`, NOT `2r`: `‖(x-x₀)/(2r)‖ < 1/2` iff
  --                `‖x-x₀‖ < r`.  This is the one place an off-by-a-factor would typecheck.
  --   ASSEMBLY     No paper sentence, and no gluing needed either: `IsOpen.contDiffOn_iff`
  --                reduces to `ContDiffAt ℝ 1 u x₀`, and `contDiffAt_one_iff` asks for SOME
  --                `f' : E → E →L[ℝ] ℝ` continuous on SOME neighbourhood with
  --                `HasFDerivAt u (f' x) x` there -- `f'` need not be `fderiv ℝ u`, so the
  --                per-centre fields never have to be reconciled and uniqueness of the
  --                derivative is never invoked.
  -- ===================================================================
  -- `IsConnected Ω` and the nonemptiness it carries are not used; they are carried because
  -- the paper's corollary carries them.
  have _unused_hconn := hconn
  have hΩopen : IsOpen Ω := hu.1.1
  have hucont : ContinuousOn u Ω := hu.1.2.1
  -- infinity-harmonicity restricts to OPEN subsets (see the map above)
  have hrestrict : ∀ (Ω' W : Set (EuclideanSpace ℝ (Fin d)))
      (f : EuclideanSpace ℝ (Fin d) → ℝ),
      IsOpen W → W ⊆ Ω' → IsInfHarmonicOn Ω' f → IsInfHarmonicOn W f := by
    intro Ω' W f hW hsub hf
    obtain ⟨⟨-, hcf, hsubs⟩, ⟨-, -, hsups⟩⟩ := hf
    refine ⟨⟨hW, hcf.mono hsub, ?_⟩, ⟨hW, hcf.mono hsub, ?_⟩⟩
    · intro z hz φ hφ hmax
      refine hsubs z (hsub hz) φ hφ ?_
      have h1 : ∀ᶠ x in nhds z, (fun x => f x - φ x) x ≤ (fun x => f x - φ x) z := by
        rw [← hW.nhdsWithin_eq hz]
        exact hmax
      exact h1.filter_mono nhdsWithin_le_nhds
    · intro z hz φ hφ hmin
      refine hsups z (hsub hz) φ hφ ?_
      have h1 : ∀ᶠ x in nhds z, (fun x => f x - φ x) z ≤ (fun x => f x - φ x) x := by
        rw [← hW.nhdsWithin_eq hz]
        exact hmin
      exact h1.filter_mono nhdsWithin_le_nhds
  -- the constants of Theorem 1.1, produced once and depending only on `d`
  obtain ⟨al, C, hal0, hal3, hC0, hME⟩ := MainEstimate d hd
  have _unused_hal3 := hal3
  have _unused_hC0 := hC0
  -- `Ω` is open, so `C¹` on `Ω` is `C¹` at each of its points
  rw [hΩopen.contDiffOn_iff]
  intro x₀ hx₀
  -- ===================== STEP 1: A GOOD BALL ==================================
  obtain ⟨R, hR0, hRsub⟩ := Metric.isOpen_iff.mp hΩopen x₀ hx₀
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = R / 4 := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; linarith only [hR0]
  have hrne : r ≠ 0 := ne_of_gt hr0
  have hA0 : (0 : ℝ) < 2 * r := by linarith only [hr0]
  have hAne : (2 * r : ℝ) ≠ 0 := ne_of_gt hA0
  have hcb : closedBall x₀ (2 * r) ⊆ Ω := by
    intro x hx
    rw [mem_closedBall, hrdef] at hx
    exact hRsub (by rw [mem_ball]; linarith only [hx, hR0])
  -- the rescaled function `v y = u (x₀ + 2r y)`, infinity-harmonic on `T ⁻¹' Ω`
  have hvbig : IsInfHarmonicOn ((fun y : EuclideanSpace ℝ (Fin d) => x₀ + (2 * r) • y) ⁻¹' Ω)
      (fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y)) :=
    InfHarmonicRescale Ω u hu x₀ (2 * r) hA0
  -- ===================== STEP 2: HARMONIC ON THE UNIT BALL ====================
  have hTmem : ∀ y : EuclideanSpace ℝ (Fin d), ‖y‖ ≤ 1 →
      x₀ + (2 * r) • y ∈ closedBall x₀ (2 * r) := by
    intro y hy
    rw [mem_closedBall, dist_eq_norm,
      show x₀ + (2 * r) • y - x₀ = (2 * r) • y from by abel,
      norm_smul, Real.norm_eq_abs, abs_of_pos hA0]
    nlinarith only [hy, hA0]
  have hball1 : ball (0 : EuclideanSpace ℝ (Fin d)) 1
      ⊆ (fun y : EuclideanSpace ℝ (Fin d) => x₀ + (2 * r) • y) ⁻¹' Ω := by
    intro y hy
    rw [mem_ball, dist_zero_right] at hy
    exact hcb (hTmem y (le_of_lt hy))
  have hvharm : IsInfHarmonicOn (ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      (fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y)) :=
    hrestrict _ _ _ isOpen_ball hball1 hvbig
  -- ===================== STEP 3: BOUNDED ON THE UNIT BALL =====================
  have himg : (fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y)) ''
      ball (0 : EuclideanSpace ℝ (Fin d)) 1 ⊆ u '' closedBall x₀ (2 * r) := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := ht
    rw [mem_ball, dist_zero_right] at hy
    exact ⟨x₀ + (2 * r) • y, hTmem y (le_of_lt hy), rfl⟩
  have hcptball : IsCompact (closedBall x₀ (2 * r)) := ProperSpace.isCompact_closedBall _ _
  have hvba : BddAbove ((fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y)) ''
      ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    BddAbove.mono himg (hcptball.bddAbove_image (hucont.mono hcb))
  have hvbb : BddBelow ((fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y)) ''
      ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    BddBelow.mono himg (hcptball.bddBelow_image (hucont.mono hcb))
  -- ===================== STEP 4: THE ESTIMATE AND ITS CONTINUITY ==============
  obtain ⟨gv, hgv1, -, hgv3, -⟩ :=
    hME (fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y)) hvharm hvba hvbb
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ,
      K = max (HolderSeminormOn gv al (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))) 1 :=
    ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hhold : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2),
      ∀ y' ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2),
      ‖gv y - gv y'‖ ≤ K * dist y y' ^ al := by
    intro y hy y' hy'
    have hKge : HolderSeminormOn gv al (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ≤ K := by
      rw [hKdef]; exact le_max_left _ _
    by_cases hyy : y = y'
    · rw [hyy, sub_self, norm_zero]
      have h0 : (0 : ℝ) ≤ dist y' y' ^ al := Real.rpow_nonneg dist_nonneg _
      nlinarith only [h0, hK0]
    · have hmem : ‖gv y - gv y'‖ / dist y y' ^ al
          ∈ HolderQuotSet gv al (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
        rw [HolderQuotSet, Set.mem_ofPred_eq]
        exact ⟨y, hy, y', hy', hyy, rfl⟩
      have hle : ‖gv y - gv y'‖ / dist y y' ^ al
          ≤ HolderSeminormOn gv al (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
        rw [HolderSeminormOn]
        exact le_csSup hgv3 hmem
      have hdap : (0 : ℝ) < dist y y' ^ al :=
        Real.rpow_pos_of_pos (dist_pos.mpr hyy) al
      rw [div_le_iff₀ hdap] at hle
      nlinarith only [hle, hKge, hdap]
  have hgvcont : ContinuousOn gv (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) := by
    rw [Metric.continuousOn_iff]
    intro b hb eps heps
    refine ⟨(eps / K) ^ (1 / al), Real.rpow_pos_of_pos (div_pos heps hK0) _, ?_⟩
    intro a ha hdab
    rw [dist_eq_norm]
    have h1 : dist a b ^ al < ((eps / K) ^ (1 / al)) ^ al :=
      Real.rpow_lt_rpow dist_nonneg hdab hal0
    have h2 : ((eps / K) ^ (1 / al)) ^ al = eps / K := by
      rw [← Real.rpow_mul (le_of_lt (div_pos heps hK0)), one_div,
        inv_mul_cancel₀ (ne_of_gt hal0), Real.rpow_one]
    rw [h2] at h1
    have h3 := hhold a ha b hb
    have h4 : K * dist a b ^ al < K * (eps / K) := mul_lt_mul_of_pos_left h1 hK0
    have h5 : K * (eps / K) = eps := by field_simp
    linarith only [h3, h4, h5]
  -- ===================== STEP 5: UNSCALING ====================================
  -- `S x = (x - x₀)/(2r)` carries `ball x₀ r` into `ball 0 (1/2)` -- radius `r`, not `2r`.
  have hSmem : ∀ x ∈ ball x₀ r,
      (2 * r)⁻¹ • (x - x₀) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2) := by
    intro x hx
    rw [mem_ball] at hx
    rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hA0), ← dist_eq_norm]
    have h1 : (2 * r)⁻¹ * dist x x₀ < (2 * r)⁻¹ * r :=
      mul_lt_mul_of_pos_left hx (inv_pos.mpr hA0)
    have h2 : (2 * r)⁻¹ * r = 1 / 2 := by field_simp
    linarith only [h1, h2]
  rw [contDiffAt_one_iff]
  refine ⟨fun x => InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
      ((2 * r)⁻¹ • gv ((2 * r)⁻¹ • (x - x₀))), ball x₀ r,
    isOpen_ball.mem_nhds (mem_ball_self hr0), ?_, ?_⟩
  · -- the unscaled gradient is continuous on `ball x₀ r`
    have hScont : Continuous
        (fun x : EuclideanSpace ℝ (Fin d) => (2 * r)⁻¹ • (x - x₀)) := by fun_prop
    have h1 : ContinuousOn (fun x : EuclideanSpace ℝ (Fin d) => gv ((2 * r)⁻¹ • (x - x₀)))
        (ball x₀ r) :=
      hgvcont.comp hScont.continuousOn (fun x hx => hSmem x hx)
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))).continuous.comp_continuousOn
      (h1.const_smul ((2 * r)⁻¹))
  · -- and it is the derivative of `u` there
    intro x hx
    have hSd : HasFDerivAt (fun x' : EuclideanSpace ℝ (Fin d) => (2 * r)⁻¹ • (x' - x₀))
        ((2 * r)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))) x :=
      ((hasFDerivAt_id x).sub_const x₀).const_smul ((2 * r)⁻¹)
    have hvd : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin d) => u (x₀ + (2 * r) • y))
        (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
          (gv ((2 * r)⁻¹ • (x - x₀)))) ((2 * r)⁻¹ • (x - x₀)) :=
      (hgv1 _ (hSmem x hx)).hasFDerivAt
    have hcomp := HasFDerivAt.comp x hvd hSd
    have hmap : ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
            (gv ((2 * r)⁻¹ • (x - x₀)))).comp
          ((2 * r)⁻¹ • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d))))
        = InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin d))
            ((2 * r)⁻¹ • gv ((2 * r)⁻¹ • (x - x₀))) := by
      ext h
      show (inner ℝ (gv ((2 * r)⁻¹ • (x - x₀))) ((2 * r)⁻¹ • h) : ℝ)
        = (inner ℝ ((2 * r)⁻¹ • gv ((2 * r)⁻¹ • (x - x₀))) h : ℝ)
      rw [real_inner_smul_left, real_inner_smul_right]
    rw [hmap] at hcomp
    refine hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x' => ?_))
    show u x' = u (x₀ + (2 * r) • ((2 * r)⁻¹ • (x' - x₀)))
    rw [smul_smul, mul_inv_cancel₀ hAne, one_smul,
      show x₀ + (x' - x₀) = x' from by abel]
