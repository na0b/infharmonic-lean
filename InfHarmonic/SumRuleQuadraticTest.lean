module

public import InfHarmonic.ContDiffAtSecondOrderPeano
public import InfHarmonic.Preamble

@[expose] public section
open Set Metric
open scoped Gradient
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Part II of the theorem of sums: at a local maximum of `∑ g j - Ψ` the
second-order Taylor expansion of `Ψ` turns the maximum into a quadratic majorant
for the normalized functions `ĝ j (w) = g j (z j + w) - g j (z j) - ⟪D j Ψ, w⟫`,
and that local majorant can be globalized.  For every `τ > 0` the conclusion
produces a radius `a`, a bound `C` and globally defined continuous functions
`G j` that agree with `ĝ j - ‖·‖⁴` on the closed ball of radius `a`, are bounded
above by `C`, and for which the quadratic test
`W ↦ ∑ G j (w j) - (D²Ψ [W] + τ ‖W‖²) / 2` is at most `-∑ ‖w j‖⁴` away from `0`,
hence has a strict global maximum at `0`. -/
theorem SumRuleQuadraticTest (N : ℕ) (hN : 0 < N) (O : Fin N → Set E)
    (hO : ∀ j, IsOpen (O j)) (g : Fin N → E → ℝ) (hg : ∀ j, ContinuousOn (g j) (O j))
    (Ψ : PiLp 2 (fun _ : Fin N => E) → ℝ) (Z : PiLp 2 (fun _ : Fin N => E))
    (hZ : ∀ j, ofLp Z j ∈ O j) (hΨ : ContDiffAt ℝ 2 Ψ Z)
    (hmax : IsLocalMax (fun Y : PiLp 2 (fun _ : Fin N => E) =>
      (∑ j, g j (ofLp Y j)) - Ψ Y) Z)
    (τ : ℝ) (hτ : 0 < τ) :
    ∃ (a C : ℝ) (G : Fin N → E → ℝ), 0 < a ∧ 0 ≤ C ∧
      (∀ j, Continuous (G j)) ∧
      (∀ j, ∀ w : E, G j w ≤ C) ∧
      (∀ j, ∀ w : E, ‖w‖ ≤ a → G j w =
        g j (ofLp Z j + w) - g j (ofLp Z j) - inner ℝ (ofLp (∇ Ψ Z) j) w - ‖w‖ ^ 4) ∧
      (∀ W : PiLp 2 (fun _ : Fin N => E), W ≠ 0 →
        (∑ j, G j (ofLp W j))
            - ((fderiv ℝ (fderiv ℝ Ψ) Z) W W + τ * ‖W‖ ^ 2) / 2
          ≤ -∑ j, ‖ofLp W j‖ ^ 4) := by
  have hne : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  obtain ⟨A, hAdef⟩ : ∃ A : PiLp 2 (fun _ : Fin N => E) →L[ℝ]
      PiLp 2 (fun _ : Fin N => E) →L[ℝ] ℝ, A = fderiv ℝ (fderiv ℝ Ψ) Z := ⟨_, rfl⟩
  have hAsym : ∀ ξ ζ : PiLp 2 (fun _ : Fin N => E), A ξ ζ = A ζ ξ := by
    rw [hAdef]
    exact hΨ.isSymmSndFDerivAt (by norm_num)
  -- A BOUND FOR THE HESSIAN FORM.  The operator norm of `A` itself has no instance on this
  -- space, but `A.isBoundedBilinearMap.bound` gives the bilinear bound directly and does NOT
  -- time out (unlike `isBoundedLinearMap.bound`, which does -- see burst 370).
  obtain ⟨M, hM0, hMb⟩ : ∃ M : ℝ, 0 < M ∧
      ∀ ξ ζ : PiLp 2 (fun _ : Fin N => E), |A ξ ζ| ≤ M * ‖ξ‖ * ‖ζ‖ := by
    as_aux_lemma =>
    obtain ⟨M, hM, hb⟩ := A.isBoundedBilinearMap.bound
    refine ⟨M, hM, fun ξ ζ => ?_⟩
    have h1 := hb ξ ζ
    rwa [Real.norm_eq_abs] at h1
  -- the ℓ²-product splittings
  have hinner : ∀ W : PiLp 2 (fun _ : Fin N => E),
      (inner ℝ (∇ Ψ Z) W : ℝ) = ∑ j, inner ℝ (ofLp (∇ Ψ Z) j) (ofLp W j) :=
    fun W => PiLp.inner_apply _ _
  have hnormsq : ∀ W : PiLp 2 (fun _ : Fin N => E), ‖W‖ ^ 2 = ∑ j, ‖ofLp W j‖ ^ 2 := by
    intro W
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun j _ => real_inner_self_eq_norm_sq _)
  -- the normalized summands
  obtain ⟨gh, hghdef⟩ : ∃ gh : Fin N → E → ℝ, gh = fun j w =>
      g j (ofLp Z j + w) - g j (ofLp Z j) - inner ℝ (ofLp (∇ Ψ Z) j) w := ⟨_, rfl⟩
  have hgh0 : ∀ j : Fin N, gh j 0 = 0 := by
    intro j
    rw [hghdef]
    simp
  -- STEP 1: THE QUADRATIC MAJORANT, from the local maximum and the Peano expansion
  obtain ⟨rt, hrt, hmaj⟩ : ∃ r > 0, ∀ W : PiLp 2 (fun _ : Fin N => E), ‖W‖ ≤ r →
      (∑ j, gh j (ofLp W j)) ≤ (A W W + τ * ‖W‖ ^ 2) / 2 := by
    obtain ⟨r1, hr1, hmb⟩ := Metric.eventually_nhds_iff.mp hmax
    obtain ⟨r2, hr2, hpe⟩ := ContDiffAtSecondOrderPeano Ψ Z hΨ (τ / 2) (by positivity)
    refine ⟨min (r1 / 2) (r2 / 2), by positivity, fun W hW => ?_⟩
    have hW1 : ‖W‖ < r1 := by
      have h := le_trans hW (min_le_left _ _)
      linarith
    have hW2 : ‖W‖ < r2 := by
      have h := le_trans hW (min_le_right _ _)
      linarith
    have hd : dist (Z + W) Z < r1 := by
      rw [dist_eq_norm, show Z + W - Z = W from by abel]
      exact hW1
    have hmx := hmb hd
    have hpb := abs_le.mp (hpe W hW2)
    have hcomp : ∀ j : Fin N, ofLp (Z + W) j = ofLp Z j + ofLp W j := by
      intro j
      simp
    have hgsum : (∑ j, gh j (ofLp W j))
        = (∑ j, g j (ofLp (Z + W) j)) - (∑ j, g j (ofLp Z j))
          - inner ℝ (∇ Ψ Z) W := by
      rw [hghdef, hinner W, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by rw [hcomp j])
    rw [hgsum, hAdef]
    linarith [hmx, hpb.1, hpb.2]
  -- STEP 2: LOCALIZATION
  obtain ⟨rr, hrr0, hrrsub⟩ : ∃ rr : Fin N → ℝ, (∀ j, 0 < rr j) ∧
      ∀ j, Metric.closedBall (ofLp Z j) (rr j) ⊆ O j := by
    have hex : ∀ j : Fin N, ∃ r : ℝ, 0 < r ∧ Metric.closedBall (ofLp Z j) r ⊆ O j := by
      intro j
      obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (hO j) (ofLp Z j) (hZ j)
      refine ⟨ε / 2, by positivity, fun y hy => hsub ?_⟩
      rw [Metric.mem_closedBall] at hy
      rw [Metric.mem_ball]
      linarith
    choose rr h1 h2 using hex
    exact ⟨rr, h1, h2⟩
  obtain ⟨rp, hrp0, hrple⟩ : ∃ r : ℝ, 0 < r ∧ ∀ j, r ≤ rr j := by
    refine ⟨Finset.univ.inf' Finset.univ_nonempty rr, ?_,
      fun j => Finset.inf'_le _ (Finset.mem_univ j)⟩
    rw [Finset.lt_inf'_iff]
    exact fun j _ => hrr0 j
  have hsq0 : (0:ℝ) ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hden : (0:ℝ) < 1 + Real.sqrt (N : ℝ) := by linarith
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = min rt rp / (1 + Real.sqrt (N : ℝ)) := ⟨_, rfl⟩
  have ha : 0 < a := by
    rw [hadef]
    exact div_pos (lt_min hrt hrp0) hden
  have hart : a * Real.sqrt (N : ℝ) ≤ rt := by
    rw [hadef, div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith [hsq0, hrt.le, min_le_left rt rp]
  have harp : a ≤ rp := by
    rw [hadef, div_le_iff₀ hden]
    nlinarith [hsq0, hrp0.le, min_le_right rt rp]
  -- a tuple with all components of norm at most `a` has norm at most `a √N ≤ rt`
  have hWbound : ∀ W : PiLp 2 (fun _ : Fin N => E), (∀ j, ‖ofLp W j‖ ≤ a) →
      ‖W‖ ≤ a * Real.sqrt (N : ℝ) := by
    intro W hb
    have h1 : ‖W‖ ^ 2 ≤ (a * Real.sqrt (N : ℝ)) ^ 2 := by
      rw [hnormsq W]
      have h2 : ∀ j : Fin N, ‖ofLp W j‖ ^ 2 ≤ a ^ 2 := by
        intro j
        nlinarith [norm_nonneg (ofLp W j), hb j, ha.le]
      calc ∑ j, ‖ofLp W j‖ ^ 2 ≤ ∑ _j : Fin N, a ^ 2 := Finset.sum_le_sum (fun j _ => h2 j)
        _ = (N : ℝ) * a ^ 2 := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (a * Real.sqrt (N : ℝ)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ (N:ℝ) by positivity)]
            ring
    nlinarith [h1, norm_nonneg W, mul_nonneg ha.le hsq0]
  -- each normalized summand is continuous on the closed ball of radius `a`
  have hghc : ∀ j : Fin N, ContinuousOn (gh j) (Metric.closedBall (0:E) a) := by
    intro j
    rw [hghdef]
    have hin : ∀ w ∈ Metric.closedBall (0:E) a, ofLp Z j + w ∈ O j := by
      intro w hw
      refine hrrsub j ?_
      rw [Metric.mem_closedBall, dist_eq_norm, show ofLp Z j + w - ofLp Z j = w from by abel]
      rw [Metric.mem_closedBall, dist_zero_right w] at hw
      exact le_trans (le_trans hw harp) (hrple j)
    refine ContinuousOn.sub (ContinuousOn.sub ?_ continuousOn_const) ?_
    · exact (hg j).comp (continuousOn_const.add continuousOn_id) hin
    · exact (continuous_const.inner continuous_id).continuousOn
  -- a uniform bound for the normalized summands on that ball
  obtain ⟨C, hC0, hCb⟩ : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin N) (w : E), ‖w‖ ≤ a → |gh j w| ≤ C := by
    have hmj : ∀ j : Fin N, ∃ Mj : ℝ, 0 ≤ Mj ∧
        ∀ w ∈ Metric.closedBall (0:E) a, |gh j w| ≤ Mj := by
      intro j
      obtain ⟨w₀, -, hw₀⟩ := (isCompact_closedBall (0:E) a).exists_isMaxOn
        ⟨0, Metric.mem_closedBall_self ha.le⟩ (hghc j).abs
      exact ⟨|gh j w₀|, abs_nonneg _, fun w hw => hw₀ hw⟩
    choose Mj hMj0 hMjb using hmj
    refine ⟨Finset.univ.sup' Finset.univ_nonempty Mj, ?_, fun j w hw => ?_⟩
    · exact le_trans (hMj0 (Classical.arbitrary (Fin N)))
        (Finset.le_sup' Mj (Finset.mem_univ _))
    · refine le_trans (hMjb j w ?_) (Finset.le_sup' Mj (Finset.mem_univ j))
      rw [Metric.mem_closedBall, dist_zero_right w]
      exact hw
  -- THE RADIAL RETRACTION, in the division-free form `(a / max a ‖w‖) • w`, which is
  -- continuous everywhere (the denominator is at least `a > 0`) and needs no case split.
  obtain ⟨pr, hprdef⟩ : ∃ pr : E → E, pr = fun w : E => (a / max a ‖w‖) • w := ⟨_, rfl⟩
  have hmaxpos : ∀ w : E, (0:ℝ) < max a ‖w‖ := fun w => lt_of_lt_of_le ha (le_max_left _ _)
  have hprc : Continuous pr := by
    rw [hprdef]
    refine Continuous.smul ?_ continuous_id
    exact continuous_const.div (continuous_const.max continuous_norm)
      (fun w => (hmaxpos w).ne')
  have hprn : ∀ w : E, ‖pr w‖ ≤ a := by
    intro w
    have h3 := hmaxpos w
    have h2 : ‖w‖ ≤ max a ‖w‖ := le_max_right _ _
    rw [hprdef]
    show ‖(a / max a ‖w‖) • w‖ ≤ a
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ha h3), div_mul_eq_mul_div,
      div_le_iff₀ h3]
    nlinarith [h2, ha.le, h3]
  have hpreq : ∀ w : E, ‖w‖ ≤ a → pr w = w := by
    intro w hw
    rw [hprdef]
    show (a / max a ‖w‖) • w = w
    rw [max_eq_left hw, div_self ha.ne', one_smul]
  have hprsub : ∀ w : E, ‖w - pr w‖ = max (‖w‖ - a) 0 := by
    intro w
    rcases le_or_gt ‖w‖ a with hle | hgt
    · rw [hpreq w hle, sub_self, norm_zero, max_eq_right (by linarith)]
    · have h3 : max a ‖w‖ = ‖w‖ := max_eq_right hgt.le
      have hwpos : (0:ℝ) < ‖w‖ := lt_trans ha hgt
      have he : w - pr w = (1 - a / ‖w‖) • w := by
        rw [hprdef]
        show w - (a / max a ‖w‖) • w = (1 - a / ‖w‖) • w
        rw [h3, sub_smul, one_smul]
      rw [he, norm_smul, Real.norm_eq_abs,
        abs_of_pos (by rw [sub_pos, div_lt_one hwpos]; exact hgt),
        max_eq_left (by linarith)]
      field_simp
  -- the constant K and the globalized summands
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = (M + τ) * (N : ℝ) * (a + 1) + 1 := ⟨_, rfl⟩
  obtain ⟨G, hGdef⟩ : ∃ G : Fin N → E → ℝ, G = fun j w =>
      gh j (pr w) - K * max (‖w‖ - a) 0 - K * max (‖w‖ - a) 0 ^ 2 - ‖w‖ ^ 4 := ⟨_, rfl⟩
  have hGapp : ∀ (j : Fin N) (w : E), G j w
      = gh j (pr w) - K * max (‖w‖ - a) 0 - K * max (‖w‖ - a) 0 ^ 2 - ‖w‖ ^ 4 := by
    intro j w
    rw [hGdef]
  have hKpos : 0 < K := by
    rw [hKdef]
    have : (0:ℝ) ≤ (M + τ) * (N : ℝ) * (a + 1) := by positivity
    linarith
  -- the symmetric bilinear identity behind the m > 0 branch
  have hbil : ∀ X Y : PiLp 2 (fun _ : Fin N => E),
      (A X X + τ * ‖X‖ ^ 2) - (A Y Y + τ * ‖Y‖ ^ 2)
        = A (X - Y) (X + Y) + τ * inner ℝ (X - Y) (X + Y) := by
    intro X Y
    have e1 : A (X - Y) (X + Y) = A X X - A Y Y := by
      simp only [map_sub, sub_apply, map_add]
      rw [hAsym X Y]
      ring
    have e2 : (inner ℝ (X - Y) (X + Y) : ℝ) = ‖X‖ ^ 2 - ‖Y‖ ^ 2 := by
      rw [inner_sub_left, inner_add_right, inner_add_right,
        real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, real_inner_comm Y X]
      ring
    rw [e1, e2]
    ring
  refine ⟨a, C, G, ha, hC0, ?_, ?_, ?_, ?_⟩
  · -- (G1a) continuity
    intro j
    rw [hGdef]
    refine Continuous.sub (Continuous.sub (Continuous.sub ?_ ?_) ?_) ?_
    · -- gh j ∘ pr is continuous because pr lands in the ball where gh j is continuous
      refine ContinuousOn.comp_continuous (hghc j) hprc (fun w => ?_)
      rw [Metric.mem_closedBall, dist_zero_right (pr w)]
      exact hprn w
    · exact continuous_const.mul ((continuous_norm.sub continuous_const).max continuous_const)
    · exact continuous_const.mul
        (((continuous_norm.sub continuous_const).max continuous_const).pow 2)
    · exact continuous_norm.pow 4
  · -- (G1b) the uniform upper bound
    intro j w
    rw [hGapp j w]
    have h1 : |gh j (pr w)| ≤ C := hCb j (pr w) (hprn w)
    have h2 : (0:ℝ) ≤ max (‖w‖ - a) 0 := le_max_right _ _
    have h3 : (0:ℝ) ≤ ‖w‖ ^ 4 := by positivity
    nlinarith [abs_le.mp h1, h2, h3, hKpos.le, sq_nonneg (max (‖w‖ - a) 0)]
  · -- (G2) the identity on the ball of radius a
    intro j w hw
    rw [hGapp j w, hpreq w hw, max_eq_right (by linarith), hghdef]
    simp
  · -- (G3) the strict quadratic test
    intro W hW
    rw [← hAdef]
    obtain ⟨PW, hPWdef⟩ : ∃ PW : PiLp 2 (fun _ : Fin N => E),
        PW = toLp 2 (fun j => pr (ofLp W j)) := ⟨_, rfl⟩
    have hPWc : ∀ j : Fin N, ofLp PW j = pr (ofLp W j) := by
      intro j
      rw [hPWdef]
    obtain ⟨m, hmdef⟩ : ∃ m : ℝ,
        m = Finset.univ.sup' Finset.univ_nonempty
          (fun j : Fin N => max (‖ofLp W j‖ - a) 0) := ⟨_, rfl⟩
    have hm0 : 0 ≤ m := by
      rw [hmdef]
      exact le_trans (le_max_right (‖ofLp W (Classical.arbitrary (Fin N))‖ - a) 0)
        (Finset.le_sup' (fun j : Fin N => max (‖ofLp W j‖ - a) 0) (Finset.mem_univ _))
    have hmle : ∀ j : Fin N, max (‖ofLp W j‖ - a) 0 ≤ m := by
      intro j
      rw [hmdef]
      exact Finset.le_sup' (fun j : Fin N => max (‖ofLp W j‖ - a) 0) (Finset.mem_univ j)
    have hwj : ∀ j : Fin N, ‖ofLp W j‖ ≤ a + m := by
      intro j
      have h1 := hmle j
      have h2 : ‖ofLp W j‖ - a ≤ max (‖ofLp W j‖ - a) 0 := le_max_left _ _
      linarith
    have hPWn : ‖PW‖ ≤ a * Real.sqrt (N : ℝ) :=
      hWbound PW (fun j => by rw [hPWc j]; exact hprn (ofLp W j))
    have hWn : ‖W‖ ≤ (a + m) * Real.sqrt (N : ℝ) := by
      have h1 : ‖W‖ ^ 2 ≤ ((a + m) * Real.sqrt (N : ℝ)) ^ 2 := by
        rw [hnormsq W]
        have h2 : ∀ j : Fin N, ‖ofLp W j‖ ^ 2 ≤ (a + m) ^ 2 := by
          intro j
          nlinarith only [norm_nonneg (ofLp W j), hwj j, ha.le, hm0]
        calc ∑ j, ‖ofLp W j‖ ^ 2 ≤ ∑ _j : Fin N, (a + m) ^ 2 :=
              Finset.sum_le_sum (fun j _ => h2 j)
          _ = (N : ℝ) * (a + m) ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = ((a + m) * Real.sqrt (N : ℝ)) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ (N:ℝ) by positivity)]
              ring
      nlinarith only [h1, norm_nonneg W, mul_nonneg (show (0:ℝ) ≤ a + m by linarith only [ha.le, hm0]) hsq0]
    have hdiffn : ‖W - PW‖ ≤ Real.sqrt (N : ℝ) * m := by
      have h1 : ‖W - PW‖ ^ 2 ≤ (Real.sqrt (N : ℝ) * m) ^ 2 := by
        rw [hnormsq (W - PW)]
        have h2 : ∀ j : Fin N, ‖ofLp (W - PW) j‖ ^ 2 ≤ m ^ 2 := by
          intro j
          have h3 : ofLp (W - PW) j = ofLp W j - pr (ofLp W j) := by
            rw [show ofLp (W - PW) j = ofLp W j - ofLp PW j from by simp, hPWc j]
          rw [h3, hprsub (ofLp W j)]
          nlinarith only [hmle j, le_max_right (‖ofLp W j‖ - a) 0, hm0]
        calc ∑ j, ‖ofLp (W - PW) j‖ ^ 2 ≤ ∑ _j : Fin N, m ^ 2 :=
              Finset.sum_le_sum (fun j _ => h2 j)
          _ = (N : ℝ) * m ^ 2 := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ = (Real.sqrt (N : ℝ) * m) ^ 2 := by
              rw [mul_pow, Real.sq_sqrt (show (0:ℝ) ≤ (N:ℝ) by positivity)]
      nlinarith only [h1, norm_nonneg (W - PW), mul_nonneg hsq0 hm0]
    -- the quartic gap, which is strictly positive because W ≠ 0
    have hquart : 0 < ∑ j, ‖ofLp W j‖ ^ 4 := by
      rcases Finset.exists_ne_zero_of_sum_ne_zero
        (show ∑ j, ‖ofLp W j‖ ^ 2 ≠ 0 from by
          rw [← hnormsq W]
          exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hW)) with ⟨j₀, -, hj₀⟩
      refine Finset.sum_pos' (fun j _ => by positivity) ⟨j₀, Finset.mem_univ j₀, ?_⟩
      have h1 : ‖ofLp W j₀‖ ≠ 0 := by
        intro h0
        rw [h0] at hj₀
        simp at hj₀
      positivity
    rcases eq_or_lt_of_le hm0 with hm00 | hmpos
    · -- m = 0: every component is already in the ball, so the majorant applies directly
      have hall : ∀ j : Fin N, ‖ofLp W j‖ ≤ a := by
        intro j
        have h1 := hmle j
        have h2 : ‖ofLp W j‖ - a ≤ max (‖ofLp W j‖ - a) 0 := le_max_left _ _
        linarith [hm00.symm]
      have hzero : ∀ j : Fin N, max (‖ofLp W j‖ - a) 0 = 0 := by
        intro j
        exact max_eq_right (by linarith [hall j])
      have hWle : ‖W‖ ≤ rt := le_trans (hWbound W hall) hart
      have hmj := hmaj W hWle
      have hsum : (∑ j, G j (ofLp W j))
          = (∑ j, gh j (ofLp W j)) - ∑ j, ‖ofLp W j‖ ^ 4 := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hGapp j (ofLp W j), hpreq _ (hall j), hzero j]
        ring
      rw [hsum]
      linarith only [hmj]
    · -- m > 0: compare the test at W with the test at the retracted point
      have hPWle : ‖PW‖ ≤ rt := le_trans hPWn hart
      have hmjP := hmaj PW hPWle
      have hsumP : (∑ j, gh j (ofLp PW j)) = ∑ j, gh j (pr (ofLp W j)) :=
        Finset.sum_congr rfl (fun j _ => by rw [hPWc j])
      rw [hsumP] at hmjP
      -- the penalty terms dominate the change in the quadratic form
      have hpen1 : m ≤ ∑ j, max (‖ofLp W j‖ - a) 0 := by
        obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun j : Fin N => max (‖ofLp W j‖ - a) 0)
        rw [hmdef, hj₀]
        exact Finset.single_le_sum
          (f := fun j : Fin N => max (‖ofLp W j‖ - a) 0)
          (fun j _ => le_max_right _ _) (Finset.mem_univ j₀)
      have hpen2 : m ^ 2 ≤ ∑ j, max (‖ofLp W j‖ - a) 0 ^ 2 := by
        obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
          (fun j : Fin N => max (‖ofLp W j‖ - a) 0)
        have h1 : m ^ 2 = max (‖ofLp W j₀‖ - a) 0 ^ 2 := by rw [hmdef, hj₀]
        rw [h1]
        exact Finset.single_le_sum
          (f := fun j : Fin N => max (‖ofLp W j‖ - a) 0 ^ 2)
          (fun j _ => by positivity) (Finset.mem_univ j₀)
      -- the quadratic-form comparison
      have hNn : (0:ℝ) ≤ (N : ℝ) := by positivity
      have hNsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt hNn
      have hVn : ‖W + PW‖ ≤ 2 * a * Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ) * m := by
        refine le_trans (norm_add_le W PW) ?_
        nlinarith only [hWn, hPWn, hsq0, hm0]
      have hUV : ‖W - PW‖ * ‖W + PW‖
          ≤ (Real.sqrt (N : ℝ) * m) * (2 * a * Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ) * m) :=
        mul_le_mul hdiffn hVn (norm_nonneg _) (mul_nonneg hsq0 hm0)
      have hexp : (Real.sqrt (N : ℝ) * m)
            * (2 * a * Real.sqrt (N : ℝ) + Real.sqrt (N : ℝ) * m)
          = 2 * ((N : ℝ) * a * m) + (N : ℝ) * m ^ 2 := by
        linear_combination (2 * a * m + m ^ 2) * hNsq
      have habs : |(A W W + τ * ‖W‖ ^ 2) - (A PW PW + τ * ‖PW‖ ^ 2)|
          ≤ (M + τ) * (2 * ((N : ℝ) * a * m) + (N : ℝ) * m ^ 2) := by
        rw [hbil W PW]
        have hb1 : |A (W - PW) (W + PW)| ≤ M * ‖W - PW‖ * ‖W + PW‖ := hMb _ _
        have hb2 : |(inner ℝ (W - PW) (W + PW) : ℝ)| ≤ ‖W - PW‖ * ‖W + PW‖ :=
          abs_real_inner_le_norm _ _
        have hb3 : |A (W - PW) (W + PW) + τ * inner ℝ (W - PW) (W + PW)|
            ≤ (M + τ) * (‖W - PW‖ * ‖W + PW‖) := by
          refine le_trans (abs_add_le _ _) ?_
          rw [abs_mul, abs_of_pos hτ]
          nlinarith only [hb1, hb2, hτ.le, hM0.le, norm_nonneg (W - PW), norm_nonneg (W + PW)]
        refine le_trans hb3 ?_
        rw [← hexp]
        exact mul_le_mul_of_nonneg_left hUV (by linarith [hM0.le, hτ.le])
      -- assemble
      have hsum : (∑ j, G j (ofLp W j))
          = (∑ j, gh j (pr (ofLp W j)))
            - K * (∑ j, max (‖ofLp W j‖ - a) 0)
            - K * (∑ j, max (‖ofLp W j‖ - a) 0 ^ 2)
            - ∑ j, ‖ofLp W j‖ ^ 4 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl (fun j _ => hGapp j (ofLp W j))
      rw [hsum]
      have hMN : (0:ℝ) ≤ (M + τ) * (N : ℝ) :=
        mul_nonneg (by linarith only [hM0.le, hτ.le]) hNn
      have hMNa : (0:ℝ) ≤ (M + τ) * (N : ℝ) * (a + 1 / 2) :=
        mul_nonneg hMN (by linarith only [ha.le])
      have hKa : (M + τ) * (N : ℝ) * a ≤ K := by
        rw [hKdef]
        linarith only [hMN]
      have hKb : (M + τ) * (N : ℝ) / 2 ≤ K := by
        rw [hKdef]
        linarith only [hMNa]
      have hp1 : m * ((M + τ) * (N : ℝ) * a - K) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hm0 (by linarith only [hKa])
      have hp2 : m ^ 2 * ((M + τ) * (N : ℝ) / 2 - K) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg m) (by linarith only [hKb])
      have hKS1 : K * m ≤ K * (∑ j, max (‖ofLp W j‖ - a) 0) :=
        mul_le_mul_of_nonneg_left hpen1 hKpos.le
      have hKS2 : K * m ^ 2 ≤ K * (∑ j, max (‖ofLp W j‖ - a) 0 ^ 2) :=
        mul_le_mul_of_nonneg_left hpen2 hKpos.le
      have hb := abs_le.mp habs
      linarith only [hmjP, hb.1, hb.2, hKS1, hKS2, hp1, hp2, hquart]
