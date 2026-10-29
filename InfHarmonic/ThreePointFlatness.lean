import InfHarmonic.IsInfHarmonicOn
import InfHarmonic.SumRuleJets
import InfHarmonic.InfSubsolutionClosedSuperjet
import InfHarmonic.InfHarmonicNegScale
import InfHarmonic.SmoothPlateau
import InfHarmonic.ConcaveRadialProfile
import InfHarmonic.RadialQuotientSecondVariation
import InfHarmonic.RadialTestFirstDerivative
import InfHarmonic.ProfileProductSecondVariation
import InfHarmonic.SecondVariationAlongLine
import InfHarmonic.SecondVariationAddAffineOnLine
import InfHarmonic.ThreePointTestSecondVariation
import InfHarmonic.ConstrainedThreePointMaximizer
import InfHarmonic.ThreePointMaximizerGeometry
import InfHarmonic.ThreePointJetsAndMatrixInequality
set_option maxHeartbeats 400000
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Three-point flatness (paper Proposition 2.6): for infinity-harmonic functions
on the unit ball with a common Lipschitz bound that converge uniformly to affine
functions, the midpoint defect divided by the endpoint separation tends to zero
uniformly on `B (1/4)`. -/
theorem ThreePointFlatness (L : ℝ) (U : ℕ → E → ℝ) (q : ℕ → E) (b : ℕ → ℝ)
    (hU : ∀ i, IsInfHarmonicOn (ball (0 : E) 1) (U i))
    (hLip : ∀ i, ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
      |U i x - U i y| ≤ L * ‖x - y‖)
    (hflat : ∀ ε > 0, ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x ∈ ball (0 : E) 1,
      |U i x - (inner ℝ (q i) x + b i)| ≤ ε) :
    ∀ ε > 0, ∃ i₀ : ℕ, ∀ i ≥ i₀,
      ∀ x ∈ ball (0 : E) (1/4), ∀ y ∈ ball (0 : E) (1/4), x ≠ y →
        |U i x + U i y - 2 * U i ((2 : ℝ)⁻¹ • (x + y))| ≤ ε * ‖x - y‖ := by
  classical
  -- =====================================================================
  -- THE ONE-SIDED STATEMENT.  Steps 2-7 of the .tex only ever use a POSITIVE
  -- midpoint defect, and the .tex's "replacing `U_i, ℓ_i` by their negatives if
  -- necessary" is exactly the reduction of the two-sided violation to this one.
  -- Stating it for an arbitrary family lets that reduction be an application
  -- rather than a `wlog`, and it removes the need for the .tex's separate
  -- degenerate case `E = {0}`: the violating pair supplies `x ≠ y`, hence a
  -- nontrivial `E` and `0 ≤ L`, wherever those are needed.
  -- =====================================================================
  have key : ∀ (V : ℕ → E → ℝ) (p : ℕ → E) (a : ℕ → ℝ),
      (∀ i, IsInfHarmonicOn (ball (0 : E) 1) (V i)) →
      (∀ i, ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
        |V i x - V i y| ≤ L * ‖x - y‖) →
      (∀ ε > 0, ∃ i₀ : ℕ, ∀ i ≥ i₀, ∀ x ∈ ball (0 : E) 1,
        |V i x - (inner ℝ (p i) x + a i)| ≤ ε) →
      ∀ δ : ℝ, 0 < δ →
      ¬ (∀ i₀ : ℕ, ∃ i, i₀ ≤ i ∧ ∃ x ∈ ball (0 : E) (1/4), ∃ y ∈ ball (0 : E) (1/4),
          x ≠ y ∧ δ * ‖x - y‖ < V i x + V i y - 2 * V i ((2 : ℝ)⁻¹ • (x + y))) := by
    intro V p a hV hVLip hVflat δ hδ hviol
    have hball : ball (0 : E) (1/4) ⊆ ball (0 : E) 1 :=
      ball_subset_ball (by norm_num)
    -- the deviation from the affine part
    obtain ⟨w, hw⟩ : ∃ w : ℕ → E → ℝ,
        w = fun i x => V i x - ((inner ℝ (p i) x : ℝ) + a i) := ⟨_, rfl⟩
    have hwval : ∀ (i : ℕ) (x : E), w i x = V i x - ((inner ℝ (p i) x : ℝ) + a i) := by
      intro i x; rw [hw]
    -- the midpoint defect does not see the affine part
    have hmid : ∀ (i : ℕ) (x y : E),
        w i x + w i y - 2 * w i ((2 : ℝ)⁻¹ • (x + y))
          = V i x + V i y - 2 * V i ((2 : ℝ)⁻¹ • (x + y)) := by
      intro i x y
      rw [hwval, hwval, hwval, real_inner_smul_right, inner_add_right]
      ring
    -- ===================== STEP 0: `0 ≤ L`, the slope bound, and `C` =====================
    obtain ⟨E1, hE1⟩ := hVflat 1 one_pos
    have hE1w : ∀ i ≥ E1, ∀ x ∈ ball (0 : E) 1, |w i x| ≤ 1 := by
      intro i hi x hx; rw [hwval]; exact hE1 i hi x hx
    have hL0 : 0 ≤ L := by
      obtain ⟨i, -, x, hx, y, hy, hxy, -⟩ := hviol 0
      have h := hVLip i x (hball hx) y (hball hy)
      have hpos : 0 < ‖x - y‖ := by
        rw [norm_pos_iff, sub_ne_zero]; exact hxy
      nlinarith [abs_nonneg (V i x - V i y)]
    -- the slopes are bounded by `L + 2`
    have hslope : ∀ i ≥ E1, ‖p i‖ ≤ L + 2 := by
      intro i hi
      rcases eq_or_ne (p i) 0 with h0 | h0
      · rw [h0, norm_zero]; linarith
      · have hn0 : ‖p i‖ ≠ 0 := norm_ne_zero_iff.mpr h0
        obtain ⟨e, he⟩ : ∃ e : E, e = ‖p i‖⁻¹ • p i := ⟨_, rfl⟩
        have hen : ‖e‖ = 1 := by
          rw [he, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn0]
        have hmem : ∀ t : ℝ, |t| = (2:ℝ)⁻¹ → t • e ∈ ball (0 : E) 1 := by
          intro t ht
          rw [mem_ball, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, ht, hen]
          norm_num
        have h1 : ((2:ℝ)⁻¹ • e) ∈ ball (0 : E) 1 := hmem _ (by norm_num)
        have h2 : ((-(2:ℝ)⁻¹) • e) ∈ ball (0 : E) 1 := hmem _ (by norm_num)
        have hdiff : ((2:ℝ)⁻¹ • e) - ((-(2:ℝ)⁻¹) • e) = e := by
          rw [← sub_smul]
          norm_num
        have hlip := hVLip i ((2:ℝ)⁻¹ • e) h1 ((-(2:ℝ)⁻¹) • e) h2
        rw [hdiff, hen, mul_one] at hlip
        have hw1 := hE1w i hi ((2:ℝ)⁻¹ • e) h1
        have hw2 := hE1w i hi ((-(2:ℝ)⁻¹) • e) h2
        -- the affine part of the difference is `⟪p i, e⟫`
        have hinner : (inner ℝ (p i) e : ℝ) = ‖p i‖ := by
          rw [he, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        have hexp : (V i ((2:ℝ)⁻¹ • e) - V i ((-(2:ℝ)⁻¹) • e))
            - (w i ((2:ℝ)⁻¹ • e) - w i ((-(2:ℝ)⁻¹) • e)) = (inner ℝ (p i) e : ℝ) := by
          rw [hwval, hwval, real_inner_smul_right, real_inner_smul_right]
          ring
        rw [hinner] at hexp
        have habs1 : |V i ((2:ℝ)⁻¹ • e) - V i ((-(2:ℝ)⁻¹) • e)| ≤ L := hlip
        rw [abs_le] at habs1
        rw [abs_le] at hw1 hw2
        linarith [hexp]
    -- the common Lipschitz constant for the `w i`
    obtain ⟨C, hC⟩ : ∃ C : ℝ, C = 2 * L + 2 := ⟨_, rfl⟩
    have hC2 : 2 ≤ C := by rw [hC]; linarith
    have hCpos : 0 < C := by linarith
    have hwLip : ∀ i ≥ E1, ∀ x ∈ ball (0 : E) 1, ∀ y ∈ ball (0 : E) 1,
        |w i x - w i y| ≤ C * ‖x - y‖ := by
      intro i hi x hx y hy
      have hlip := hVLip i x hx y hy
      have hps := hslope i hi
      have hexp : w i x - w i y = (V i x - V i y) - (inner ℝ (p i) (x - y) : ℝ) := by
        rw [hwval, hwval, inner_sub_right]; ring
      have hin : |(inner ℝ (p i) (x - y) : ℝ)| ≤ ‖p i‖ * ‖x - y‖ :=
        abs_real_inner_le_norm (p i) (x - y)
      have hn : 0 ≤ ‖x - y‖ := norm_nonneg _
      rw [hexp]
      calc |(V i x - V i y) - (inner ℝ (p i) (x - y) : ℝ)|
          ≤ |V i x - V i y| + |(inner ℝ (p i) (x - y) : ℝ)| := abs_sub _ _
        _ ≤ L * ‖x - y‖ + ‖p i‖ * ‖x - y‖ := by
            exact add_le_add hlip hin
        _ ≤ L * ‖x - y‖ + (L + 2) * ‖x - y‖ := by
            nlinarith [mul_le_mul_of_nonneg_right hps hn]
        _ = C * ‖x - y‖ := by rw [hC]; ring
    -- midpoints stay in the ball, and the half-distance identity
    have hcmem : ∀ (ρ : ℝ) (x y : E), x ∈ ball (0 : E) ρ → y ∈ ball (0 : E) ρ →
        (2 : ℝ)⁻¹ • (x + y) ∈ ball (0 : E) ρ := by
      intro ρ x y hx hy
      rw [mem_ball, dist_eq_norm, sub_zero] at hx hy ⊢
      have h1 : ‖(2 : ℝ)⁻¹ • (x + y)‖ = (2 : ℝ)⁻¹ * ‖x + y‖ := by
        rw [norm_smul, Real.norm_eq_abs]; norm_num
      have h2 := norm_add_le x y
      rw [h1]
      linarith
    have hhalfx : ∀ x y : E, x - (2 : ℝ)⁻¹ • (x + y) = (2 : ℝ)⁻¹ • (x - y) := by
      intro x y; module
    have hhalfy : ∀ x y : E, y - (2 : ℝ)⁻¹ • (x + y) = -((2 : ℝ)⁻¹ • (x - y)) := by
      intro x y; module
    have hhalfn : ∀ x y : E, ‖(2 : ℝ)⁻¹ • (x - y)‖ = (2 : ℝ)⁻¹ * ‖x - y‖ := by
      intro x y; rw [norm_smul, Real.norm_eq_abs]; norm_num
    -- ===================== STEP 1: `δ ≤ C` =====================
    have hδC : δ ≤ C := by
      obtain ⟨i, hi, x, hx, y, hy, hxy, hlt⟩ := hviol E1
      rw [← hmid] at hlt
      have hccm : (2 : ℝ)⁻¹ • (x + y) ∈ ball (0 : E) 1 := hball (hcmem _ x y hx hy)
      have hx1 : x ∈ ball (0 : E) 1 := hball hx
      have hy1 : y ∈ ball (0 : E) 1 := hball hy
      have h1 := hwLip i hi x hx1 ((2 : ℝ)⁻¹ • (x + y)) hccm
      have h2 := hwLip i hi y hy1 ((2 : ℝ)⁻¹ • (x + y)) hccm
      rw [hhalfx, hhalfn] at h1
      rw [hhalfy, norm_neg, hhalfn] at h2
      rw [abs_le] at h1 h2
      have hpos : 0 < ‖x - y‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hxy
      have hkey : δ * ‖x - y‖ < C * ‖x - y‖ := by linarith [h1.2, h2.2]
      exact le_of_lt (lt_of_mul_lt_mul_right hkey hpos.le)
    -- ===================== STEP 2: the two auxiliary profiles =====================
    obtain ⟨hν, hfC2, hf1, hf2, hfbd⟩ := ConcaveRadialProfile
    obtain ⟨f, hfdef⟩ : ∃ f : ℝ → ℝ, f = fun s : ℝ => s - s * Real.sqrt s / 8 := ⟨_, rfl⟩
    obtain ⟨f₁, hf₁def⟩ : ∃ f₁ : ℝ → ℝ, f₁ = fun s : ℝ => 1 - 3 * Real.sqrt s / 16 := ⟨_, rfl⟩
    obtain ⟨ν, hνdef⟩ : ∃ ν : ℝ, ν = 1 - Real.sqrt (3 / 2) / 8 := ⟨_, rfl⟩
    have hνpos : 0 < ν := by rw [hνdef]; exact hν
    -- the upper-bound constant of (3a)
    obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = C + 3 / 2 * C ^ 2 := ⟨_, rfl⟩
    have hC'C : C ≤ C' := by rw [hC']; nlinarith
    have hC'pos : 0 < C' := lt_of_lt_of_le hCpos hC'C
    -- the localizing plateau
    obtain ⟨B_out, hBout⟩ : ∃ B_out : ℝ, B_out = C' / ν + δ / 2 + 1 := ⟨_, rfl⟩
    have hBoutpos : δ / 2 ≤ B_out := by
      rw [hBout]
      have : 0 < C' / ν := div_pos hC'pos hνpos
      linarith
    obtain ⟨Bf, hBfC2, hBfrange, hBfin, hBfout⟩ :=
      SmoothPlateau (E := E) (δ / 2) B_out (1 / 4) (1 / 2) (by norm_num) (by norm_num) hBoutpos
    -- the two derivative bounds on the closed ball of radius 3/4 (upper bounds suffice)
    have hcpt : IsCompact (closedBall (0 : E) (3 / 4)) := isCompact_closedBall _ _
    have hDBc : Continuous (fderiv ℝ Bf) := hBfC2.continuous_fderiv (by norm_num)
    have hDDBc : Continuous (fderiv ℝ (fderiv ℝ Bf)) :=
      (hBfC2.fderiv_right (m := 1) le_rfl).continuous_fderiv (by norm_num)
    obtain ⟨K₁, hK₁⟩ := hcpt.exists_bound_of_continuousOn (f := fderiv ℝ Bf) hDBc.continuousOn
    obtain ⟨K₂, hK₂⟩ := hcpt.exists_bound_of_continuousOn
      (f := fderiv ℝ (fderiv ℝ Bf)) hDDBc.continuousOn
    have hK₁0 : 0 ≤ K₁ := le_trans (norm_nonneg _) (hK₁ 0 (by simp only [mem_closedBall, dist_self]; norm_num))
    have hK₂0 : 0 ≤ K₂ := le_trans (norm_nonneg _) (hK₂ 0 (by simp only [mem_closedBall, dist_self]; norm_num))
    obtain ⟨K₃, hK₃⟩ : ∃ K₃ : ℝ, K₃ = C + 3 / 4 * K₁ + 2 * C := ⟨_, rfl⟩
    have hK₃0 : 0 ≤ K₃ := by rw [hK₃]; nlinarith
    -- the bounded part of the second variation, and the threshold radius
    obtain ⟨Mc, hMc⟩ : ∃ Mc : ℝ, Mc = K₁ ^ 2 / 2 + 16 * B_out * C * K₁
      + 96 * B_out ^ 2 * C ^ 2 + 3 / 2 * K₂ * K₃ ^ 2 + 4 * B_out * K₁ * K₃ := ⟨_, rfl⟩
    have hBoutp : 0 < B_out := lt_of_lt_of_le (by linarith) hBoutpos
    have hC2pos : (0 : ℝ) < C ^ 2 := pow_pos hCpos 2
    have hMc0 : 0 ≤ Mc := by
      have t1 : (0 : ℝ) ≤ K₁ ^ 2 / 2 := by
        have := sq_nonneg K₁; linarith
      have t2 : (0 : ℝ) ≤ 16 * B_out * C * K₁ :=
        mul_nonneg (mul_nonneg (by linarith) hCpos.le) hK₁0
      have t3 : (0 : ℝ) ≤ 96 * B_out ^ 2 * C ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg B_out)) (sq_nonneg C)
      have t4 : (0 : ℝ) ≤ 3 / 2 * K₂ * K₃ ^ 2 :=
        mul_nonneg (mul_nonneg (by norm_num) hK₂0) (sq_nonneg K₃)
      have t5 : (0 : ℝ) ≤ 4 * B_out * K₁ * K₃ :=
        mul_nonneg (mul_nonneg (by linarith) hK₁0) hK₃0
      rw [hMc]; linarith
    have ht0 : (0 : ℝ) < 3 * δ ^ 3 / (256 * (Mc + 1)) := by
      refine div_pos ?_ (by linarith)
      have := pow_pos hδ 3
      linarith
    obtain ⟨r₀, hr₀⟩ : ∃ r₀ : ℝ, r₀ = min (1 / 4) (min (1 / (16 * C))
      (min (16 / 9) (min (δ / (64 * C ^ 2)) ((3 * δ ^ 3 / (256 * (Mc + 1))) ^ 2)))) := ⟨_, rfl⟩
    have hr₀pos : 0 < r₀ := by
      rw [hr₀]
      refine lt_min (by norm_num) (lt_min (div_pos one_pos (by linarith))
        (lt_min (by norm_num) (lt_min (div_pos hδ (by linarith)) (pow_pos ht0 2))))
    -- ===================== STEP 5(a): THE TEST AND ITS FIRST DERIVATIVE =====================
    -- The three block maps of the jet product space, as continuous linear maps.  `Ld` is the
    -- endpoint difference, `Lc` the midpoint, `Lh` the deviation of the third point from it.
    obtain ⟨Lc, hLc⟩ : ∃ Lc : PiLp 2 (fun _ : Fin 3 => E) →L[ℝ] E,
        Lc = (2 : ℝ)⁻¹ • (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 0
          + PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 1) := ⟨_, rfl⟩
    obtain ⟨Ld, hLd⟩ : ∃ Ld : PiLp 2 (fun _ : Fin 3 => E) →L[ℝ] E,
        Ld = PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 0
          - PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 1 := ⟨_, rfl⟩
    obtain ⟨Lh, hLh⟩ : ∃ Lh : PiLp 2 (fun _ : Fin 3 => E) →L[ℝ] E,
        Lh = PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 2 - Lc := ⟨_, rfl⟩
    -- the affine part of the test is LINEAR: the constants `a i` cancel in `ℓ+ℓ-2ℓ`
    obtain ⟨Aff, hAff⟩ : ∃ Aff : ℕ → (PiLp 2 (fun _ : Fin 3 => E) →L[ℝ] ℝ),
        Aff = fun i => (innerSL ℝ (p i)).comp
          (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 0
            + PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 1
            - (2 : ℝ) • PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) 2) := ⟨_, rfl⟩
    have hLcv : ∀ Y : PiLp 2 (fun _ : Fin 3 => E),
        Lc Y = (2 : ℝ)⁻¹ • (WithLp.ofLp Y 0 + WithLp.ofLp Y 1) := by
      intro Y; rw [hLc]; rfl
    have hLdv : ∀ Y : PiLp 2 (fun _ : Fin 3 => E),
        Ld Y = WithLp.ofLp Y 0 - WithLp.ofLp Y 1 := by
      intro Y; rw [hLd]; rfl
    have hLhv : ∀ Y : PiLp 2 (fun _ : Fin 3 => E),
        Lh Y = WithLp.ofLp Y 2 - (2 : ℝ)⁻¹ • (WithLp.ofLp Y 0 + WithLp.ofLp Y 1) := by
      intro Y; rw [hLh]
      show WithLp.ofLp Y 2 - Lc Y = _
      rw [hLcv]
    have hAffv : ∀ (i : ℕ) (Y : PiLp 2 (fun _ : Fin 3 => E)),
        Aff i Y = (inner ℝ (p i)
          (WithLp.ofLp Y 0 + WithLp.ofLp Y 1 - (2 : ℝ) • WithLp.ofLp Y 2) : ℝ) := by
      intro i Y; rw [hAff]; rfl
    -- `Ψ i` is the paper's test.  No truncation is needed in Lean: division by zero is `0`,
    -- so the formula is already a total function on the product space, and it agrees with the
    -- paper's `Ψ₀` wherever `Ld Y ≠ 0`, which is all that the local hypotheses of
    -- `SumRuleJets` and `SecondVariationAlongLine` can see.
    obtain ⟨Ψ, hΨ⟩ : ∃ Ψ : ℕ → PiLp 2 (fun _ : Fin 3 => E) → ℝ,
        Ψ = fun i Y => Aff i Y + Bf (Lc Y) * f ‖Ld Y‖
          + ‖Lh Y‖ ^ 2 / ‖Ld Y‖ ^ 2 := ⟨_, rfl⟩
    -- eq:tpf-grads, in the form `∀ ζ, DΨ(Z)[ζ] = …`; the coefficient of the radial
    -- direction is the paper's `a = B(c) f'(r) - 2|h|²/r³`.
    have tpf_grads : ∀ (i : ℕ) (Z : PiLp 2 (fun _ : Fin 3 => E)), Ld Z ≠ 0 →
        ContDiffAt ℝ 2 (Ψ i) Z ∧
        ∀ ζ : PiLp 2 (fun _ : Fin 3 => E), fderiv ℝ (Ψ i) Z ζ
          = Aff i ζ + f ‖Ld Z‖ * fderiv ℝ Bf (Lc Z) (Lc ζ)
            + (Bf (Lc Z) * f₁ ‖Ld Z‖ - 2 * ‖Lh Z‖ ^ 2 / ‖Ld Z‖ ^ 3)
                * (inner ℝ (‖Ld Z‖⁻¹ • Ld Z) (Ld ζ))
            + 2 * (inner ℝ (Lh Z) (Lh ζ) : ℝ) / ‖Ld Z‖ ^ 2 := by
      intro i Z hZ
      have hrpos : 0 < ‖Ld Z‖ := norm_pos_iff.mpr hZ
      have hfc : ContDiffAt ℝ 2 f ‖Ld Z‖ := by rw [hfdef]; exact hfC2 _ hrpos
      have hfd : HasDerivAt f (f₁ ‖Ld Z‖) ‖Ld Z‖ := by
        rw [hfdef, hf₁def]; exact hf1 _ hrpos
      have h := RadialTestFirstDerivative (Aff i) Lc Ld Lh Bf f Z (f₁ ‖Ld Z‖) hZ
        hBfC2.contDiffAt hfc hfd
      rw [hΨ]
      exact h
    -- the three single-block test directions, through all four maps.  This is what turns
    -- `tpf_grads` into the paper's `p₁`, `p₂` and `D_zΨ = -2p₀`: in the `x`-direction the
    -- penalty term `+2⟪Lh Z, Lh ζ⟫/r²` becomes `-⟪h, v⟫/r²` because `Lh ζ = -v/2`.
    have hblk : ∀ (j : Fin 3) (v : E),
        WithLp.ofLp (WithLp.toLp 2 (Pi.single j v) : PiLp 2 (fun _ : Fin 3 => E))
          = Pi.single j v := fun _ _ => rfl
    have hdir0 : ∀ v : E,
        Lc (WithLp.toLp 2 (Pi.single (0 : Fin 3) v)) = (2 : ℝ)⁻¹ • v ∧
        Ld (WithLp.toLp 2 (Pi.single (0 : Fin 3) v)) = v ∧
        Lh (WithLp.toLp 2 (Pi.single (0 : Fin 3) v)) = -((2 : ℝ)⁻¹ • v) ∧
        ∀ i : ℕ, Aff i (WithLp.toLp 2 (Pi.single (0 : Fin 3) v))
          = (inner ℝ (p i) v : ℝ) := by
      intro v
      refine ⟨by rw [hLcv, hblk]; simp, by rw [hLdv, hblk]; simp,
        by rw [hLhv, hblk]; simp, fun i => by rw [hAffv, hblk]; simp⟩
    have hdir1 : ∀ v : E,
        Lc (WithLp.toLp 2 (Pi.single (1 : Fin 3) v)) = (2 : ℝ)⁻¹ • v ∧
        Ld (WithLp.toLp 2 (Pi.single (1 : Fin 3) v)) = -v ∧
        Lh (WithLp.toLp 2 (Pi.single (1 : Fin 3) v)) = -((2 : ℝ)⁻¹ • v) ∧
        ∀ i : ℕ, Aff i (WithLp.toLp 2 (Pi.single (1 : Fin 3) v))
          = (inner ℝ (p i) v : ℝ) := by
      intro v
      refine ⟨by rw [hLcv, hblk]; simp, by rw [hLdv, hblk]; simp,
        by rw [hLhv, hblk]; simp, fun i => by rw [hAffv, hblk]; simp⟩
    have hdir2 : ∀ v : E,
        Lc (WithLp.toLp 2 (Pi.single (2 : Fin 3) v)) = 0 ∧
        Ld (WithLp.toLp 2 (Pi.single (2 : Fin 3) v)) = 0 ∧
        Lh (WithLp.toLp 2 (Pi.single (2 : Fin 3) v)) = v ∧
        ∀ i : ℕ, Aff i (WithLp.toLp 2 (Pi.single (2 : Fin 3) v))
          = -(2 : ℝ) * (inner ℝ (p i) v : ℝ) := by
      intro v
      refine ⟨by rw [hLcv, hblk]; simp, by rw [hLdv, hblk]; simp,
        by rw [hLhv, hblk]; simp, fun i => by rw [hAffv, hblk]; simp [real_inner_smul_right]⟩
    -- ===================== STEP 3: THE MAXIMIZATION =====================
    -- the penalized functional of eq:three-point-maximum
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → E → E → E → ℝ, Φ = fun i x y z =>
        w i x + w i y - 2 * w i z - Bf ((2 : ℝ)⁻¹ • (x + y)) * f ‖x - y‖
          - ‖z - (2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / ‖x - y‖ ^ 2 := ⟨_, rfl⟩
    have hball34 : closedBall (0 : E) (3 / 4) ⊆ ball (0 : E) 1 := by
      intro t ht
      rw [mem_closedBall, dist_eq_norm, sub_zero] at ht
      rw [mem_ball, dist_eq_norm, sub_zero]
      linarith
    have hcm34 : ∀ x y : E, x ∈ closedBall (0 : E) (3 / 4) → y ∈ closedBall (0 : E) (3 / 4) →
        (2 : ℝ)⁻¹ • (x + y) ∈ closedBall (0 : E) (3 / 4) := by
      intro x y hx hy
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hx hy ⊢
      have h1 : ‖(2 : ℝ)⁻¹ • (x + y)‖ = (2 : ℝ)⁻¹ * ‖x + y‖ := by
        rw [norm_smul, Real.norm_eq_abs]; norm_num
      have h2 := norm_add_le x y
      rw [h1]; linarith
    have hr32 : ∀ x y : E, x ∈ closedBall (0 : E) (3 / 4) → y ∈ closedBall (0 : E) (3 / 4) →
        ‖x - y‖ ≤ 3 / 2 := by
      intro x y hx hy
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hx hy
      calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
        _ ≤ 3 / 2 := by linarith
    -- (3a) eq:tpf-upper, in the sharp form that Step 4c also needs
    have tpf_upper : ∀ i, E1 ≤ i → ∀ x y z : E,
        x ∈ closedBall (0 : E) (3 / 4) → y ∈ closedBall (0 : E) (3 / 4) →
        z ∈ closedBall (0 : E) (3 / 4) → x ≠ y →
        Φ i x y z ≤ C * ‖x - y‖ + C ^ 2 * ‖x - y‖ ^ 2
          - Bf ((2 : ℝ)⁻¹ • (x + y)) * f ‖x - y‖ := by
      intro i hi x y z hx hy hz hxy
      have hcc := hcm34 x y hx hy
      have hx1 := hball34 hx
      have hy1 := hball34 hy
      have hz1 := hball34 hz
      have hc1 := hball34 hcc
      have hrp : 0 < ‖x - y‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hxy
      have h1 := hwLip i hi x hx1 ((2 : ℝ)⁻¹ • (x + y)) hc1
      have h2 := hwLip i hi y hy1 ((2 : ℝ)⁻¹ • (x + y)) hc1
      have h3 := hwLip i hi ((2 : ℝ)⁻¹ • (x + y)) hc1 z hz1
      rw [hhalfx, hhalfn] at h1
      rw [hhalfy, norm_neg, hhalfn] at h2
      rw [abs_le] at h1 h2 h3
      have hnz : ‖(2 : ℝ)⁻¹ • (x + y) - z‖ = ‖z - (2 : ℝ)⁻¹ • (x + y)‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [hnz] at h3
      have hs0 : 0 ≤ ‖z - (2 : ℝ)⁻¹ • (x + y)‖ := norm_nonneg _
      -- the quadratic `2Cs - s²/r² ≤ C²r²`, i.e. `0 ≤ (s - C r²)²`
      have hr2 : (0 : ℝ) < ‖x - y‖ ^ 2 := by positivity
      have hdiv : 2 * C * ‖z - (2 : ℝ)⁻¹ • (x + y)‖ - C ^ 2 * ‖x - y‖ ^ 2
          ≤ ‖z - (2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / ‖x - y‖ ^ 2 := by
        rw [le_div_iff₀ hr2]
        nlinarith only [sq_nonneg (‖z - (2 : ℝ)⁻¹ • (x + y)‖ - C * ‖x - y‖ ^ 2)]
      have hquad : 2 * C * ‖z - (2 : ℝ)⁻¹ • (x + y)‖
          - ‖z - (2 : ℝ)⁻¹ • (x + y)‖ ^ 2 / ‖x - y‖ ^ 2 ≤ C ^ 2 * ‖x - y‖ ^ 2 := by
        linarith only [hdiv]
      rw [hΦ]
      linarith only [h1.2, h2.2, h3.2, hquad]
    -- the weak form used for the supremum bound
    have tpf_upper' : ∀ i, E1 ≤ i → ∀ x y z : E,
        x ∈ closedBall (0 : E) (3 / 4) → y ∈ closedBall (0 : E) (3 / 4) →
        z ∈ closedBall (0 : E) (3 / 4) → x ≠ y →
        Φ i x y z ≤ ‖x - y‖ * C' := by
      intro i hi x y z hx hy hz hxy
      have h := tpf_upper i hi x y z hx hy hz hxy
      have hrp : 0 < ‖x - y‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hxy
      have hrle := hr32 x y hx hy
      have hfnu : ν * ‖x - y‖ ≤ f ‖x - y‖ := by
        obtain ⟨h1, -, -, -⟩ := hfbd ‖x - y‖ hrp hrle
        rw [hfdef, hνdef]; exact h1
      have hBf : δ / 2 ≤ Bf ((2 : ℝ)⁻¹ • (x + y)) := (hBfrange _).1
      have hfpos : 0 ≤ f ‖x - y‖ := le_trans (by positivity) hfnu
      have hBfpos : 0 ≤ Bf ((2 : ℝ)⁻¹ • (x + y)) := by linarith
      have hprod : 0 ≤ Bf ((2 : ℝ)⁻¹ • (x + y)) * f ‖x - y‖ := mul_nonneg hBfpos hfpos
      have hkey : 0 ≤ C ^ 2 * ‖x - y‖ * (3 / 2 - ‖x - y‖) :=
        mul_nonneg (mul_nonneg (sq_nonneg C) hrp.le) (by linarith)
      rw [hC']
      nlinarith only [h, hprod, hkey]
    -- the index: large enough both for the Lipschitz constant and for `r < r₀`
    obtain ⟨E0, hE0⟩ := hVflat (δ * ν * r₀ / 8) (by positivity)
    obtain ⟨i, hik, xk, hxk, yk, hyk, hxyk, hviolk⟩ := hviol (max E1 E0)
    have hiE1 : E1 ≤ i := le_trans (le_max_left _ _) hik
    have hiE0 : E0 ≤ i := le_trans (le_max_right _ _) hik
    obtain ⟨βk, hβk⟩ : ∃ βk : ℝ, βk = δ * ‖xk - yk‖ / 2 := ⟨_, rfl⟩
    have hrkpos : 0 < ‖xk - yk‖ := by rw [norm_pos_iff, sub_ne_zero]; exact hxyk
    have hβkpos : 0 < βk := by rw [hβk]; exact div_pos (mul_pos hδ hrkpos) two_pos
    -- (3b) and (3c): eq:tpf-max, and the maximizer is strictly inside the constraint
    -- (3b) and (3c): eq:tpf-max, and the maximizer is strictly inside the constraint
    -- the violating triple is admissible
    have hcb : ball (0 : E) (1 / 4) ⊆ closedBall (0 : E) (3 / 4) := by
      intro t ht
      rw [mem_ball, dist_eq_norm, sub_zero] at ht
      rw [mem_closedBall, dist_eq_norm, sub_zero]
      linarith only [ht]
    have hckb : (2 : ℝ)⁻¹ • (xk + yk) ∈ ball (0 : E) (1 / 4) := hcmem _ xk yk hxk hyk
    have hlowk : βk / (2 * C') ≤ ‖xk - yk‖ := by
      rw [hβk, div_le_iff₀ (by linarith only [hC'pos])]
      have hδC' : δ ≤ C' := le_trans hδC hC'C
      nlinarith only [hδC', hrkpos, hδ]
    have hlowpos : 0 < βk / (2 * C') := div_pos hβkpos (by linarith only [hC'pos])
    -- the functional is continuous on the constrained set, which lives in `E × E × E`:
    -- compactness and continuity are topological, so the product norm is irrelevant
    -- here and `PiLp` is not needed until Step 4d.
    have hwcont : ContinuousOn (w i) (ball (0 : E) 1) := by
      have hVc : ContinuousOn (V i) (ball (0 : E) 1) := (hV i).1.2.1
      have hlin : Continuous (fun t : E => (inner ℝ (p i) t : ℝ) + a i) :=
        (innerSL ℝ (p i)).continuous.add continuous_const
      have h : ContinuousOn (fun t : E => V i t - ((inner ℝ (p i) t : ℝ) + a i))
          (ball (0 : E) 1) := hVc.sub hlin.continuousOn
      rw [hw]
      exact h
    have hfcont : Continuous f := by rw [hfdef]; fun_prop
    have hFcont : ContinuousOn (fun P : E × E × E => Φ i P.1 P.2.1 P.2.2)
        ((closedBall (0 : E) (3 / 4) ×ˢ
            (closedBall (0 : E) (3 / 4) ×ˢ closedBall (0 : E) (3 / 4)))
          ∩ {P : E × E × E | βk / (2 * C') ≤ ‖P.1 - P.2.1‖}) := by
      obtain ⟨S, hS⟩ : ∃ S : Set (E × E × E), S =
          (closedBall (0 : E) (3 / 4) ×ˢ
            (closedBall (0 : E) (3 / 4) ×ˢ closedBall (0 : E) (3 / 4)))
          ∩ {P : E × E × E | βk / (2 * C') ≤ ‖P.1 - P.2.1‖} := ⟨_, rfl⟩
      rw [← hS]
      have hSlow : ∀ P ∈ S, βk / (2 * C') ≤ ‖P.1 - P.2.1‖ := by
        intro P hP; rw [hS] at hP; exact hP.2
      have hSsub : ∀ P ∈ S, P.1 ∈ ball (0 : E) 1 ∧ P.2.1 ∈ ball (0 : E) 1 ∧
          P.2.2 ∈ ball (0 : E) 1 := by
        intro P hP
        rw [hS] at hP
        exact ⟨hball34 hP.1.1, hball34 hP.1.2.1, hball34 hP.1.2.2⟩
      have c1 : ContinuousOn (fun P : E × E × E => w i P.1) S :=
        hwcont.comp continuous_fst.continuousOn (fun P hP => (hSsub P hP).1)
      have c2 : ContinuousOn (fun P : E × E × E => w i P.2.1) S :=
        hwcont.comp (continuous_fst.comp continuous_snd).continuousOn
          (fun P hP => (hSsub P hP).2.1)
      have c3 : ContinuousOn (fun P : E × E × E => w i P.2.2) S :=
        hwcont.comp (continuous_snd.comp continuous_snd).continuousOn
          (fun P hP => (hSsub P hP).2.2)
      have c4 : ContinuousOn
          (fun P : E × E × E => Bf ((2 : ℝ)⁻¹ • (P.1 + P.2.1))) S :=
        (hBfC2.continuous.comp (by fun_prop)).continuousOn
      have c5 : ContinuousOn (fun P : E × E × E => f ‖P.1 - P.2.1‖) S :=
        (hfcont.comp (by fun_prop)).continuousOn
      have c6 : ContinuousOn
          (fun P : E × E × E => ‖P.2.2 - (2 : ℝ)⁻¹ • (P.1 + P.2.1)‖ ^ 2) S :=
        (by fun_prop : Continuous
          (fun P : E × E × E => ‖P.2.2 - (2 : ℝ)⁻¹ • (P.1 + P.2.1)‖ ^ 2)).continuousOn
      have c7 : ContinuousOn (fun P : E × E × E => ‖P.1 - P.2.1‖ ^ 2) S :=
        (by fun_prop : Continuous
          (fun P : E × E × E => ‖P.1 - P.2.1‖ ^ 2)).continuousOn
      have c7ne : ∀ P ∈ S, ‖P.1 - P.2.1‖ ^ 2 ≠ 0 := fun P hP =>
        pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hlowpos (hSlow P hP)))
      have hcomb := (((c1.add c2).sub (c3.const_smul (2 : ℝ))).sub
        (c4.mul c5)).sub (c6.div c7 c7ne)
      refine hcomb.congr ?_
      intro P _
      rw [hΦ]
      show w i P.1 + w i P.2.1 - 2 * w i P.2.2
          - Bf ((2 : ℝ)⁻¹ • (P.1 + P.2.1)) * f ‖P.1 - P.2.1‖
          - ‖P.2.2 - (2 : ℝ)⁻¹ • (P.1 + P.2.1)‖ ^ 2 / ‖P.1 - P.2.1‖ ^ 2 = _
      show _ = w i P.1 + w i P.2.1 - (2 : ℝ) • w i P.2.2
          - Bf ((2 : ℝ)⁻¹ • (P.1 + P.2.1)) * f ‖P.1 - P.2.1‖
          - ‖P.2.2 - (2 : ℝ)⁻¹ • (P.1 + P.2.1)‖ ^ 2 / ‖P.1 - P.2.1‖ ^ 2
      rw [smul_eq_mul]
    -- the maximum is attained
    have hΦk : βk ≤ Φ i xk yk ((2 : ℝ)⁻¹ • (xk + yk)) := by
      have hBfk : Bf ((2 : ℝ)⁻¹ • (xk + yk)) = δ / 2 := by
        refine hBfin _ ?_
        have := hckb
        rw [mem_ball, dist_eq_norm, sub_zero] at this
        linarith only [this]
      have hval : Φ i xk yk ((2 : ℝ)⁻¹ • (xk + yk))
          = w i xk + w i yk - 2 * w i ((2 : ℝ)⁻¹ • (xk + yk))
            - δ / 2 * f ‖xk - yk‖ := by
        rw [hΦ]
        show w i xk + w i yk - 2 * w i ((2 : ℝ)⁻¹ • (xk + yk))
            - Bf ((2 : ℝ)⁻¹ • (xk + yk)) * f ‖xk - yk‖
            - ‖(2 : ℝ)⁻¹ • (xk + yk) - (2 : ℝ)⁻¹ • (xk + yk)‖ ^ 2 / ‖xk - yk‖ ^ 2 = _
        rw [hBfk, sub_self, norm_zero]
        simp
      have hviol' : δ * ‖xk - yk‖
          < w i xk + w i yk - 2 * w i ((2 : ℝ)⁻¹ • (xk + yk)) := by
        rw [hmid]; exact hviolk
      have hfk : f ‖xk - yk‖ ≤ ‖xk - yk‖ := by
        obtain ⟨-, h2, -, -⟩ :=
          hfbd ‖xk - yk‖ hrkpos (hr32 xk yk (hcb hxk) (hcb hyk))
        rw [hfdef]; exact h2
      rw [hval, hβk]
      nlinarith only [hviol', hfk, hδ]
    obtain ⟨x, y, z, hx34, hy34, hz34, hxy, tpf_max, tpf_attain, tpf_rlow⟩ :=
      ConstrainedThreePointMaximizer (Φ i) xk yk ((2 : ℝ)⁻¹ • (xk + yk)) βk C'
        hβkpos hC'pos (hcb hxk) (hcb hyk) (hcb hckb) hlowk hΦk hFcont
        (tpf_upper' i hiE1)
    -- ===================== STEP 4: THE GEOMETRY AT THE MAXIMIZER =====================
    obtain ⟨cm, hcm⟩ : ∃ cm : E, cm = (2 : ℝ)⁻¹ • (x + y) := ⟨_, rfl⟩
    obtain ⟨hv, hhv⟩ : ∃ hv : E, hv = z - cm := ⟨_, rfl⟩
    obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = ‖x - y‖ := ⟨_, rfl⟩
    have hrpos : 0 < r := by
      rw [hrdef]
      exact lt_of_lt_of_le (div_pos hβkpos hC'pos) tpf_rlow
    have hrle : r ≤ 3 / 2 := by rw [hrdef]; exact hr32 x y hx34 hy34
    have hfnu : ν * r ≤ f r := by
      obtain ⟨h1, -, -, -⟩ := hfbd r hrpos hrle
      rw [hfdef, hνdef]; exact h1
    have hcm34 : cm ∈ closedBall (0 : E) (3 / 4) := by
      rw [hcm]; exact hcm34 x y hx34 hy34
    obtain ⟨Zm, hZm⟩ : ∃ Zm : PiLp 2 (fun _ : Fin 3 => E),
        Zm = WithLp.toLp 2 (fun j : Fin 3 =>
          if j = 0 then x else if j = 1 then y else z) := ⟨_, rfl⟩
    have hZm0 : WithLp.ofLp Zm 0 = x := by rw [hZm]; rfl
    have hZm1 : WithLp.ofLp Zm 1 = y := by rw [hZm]; rfl
    have hZm2 : WithLp.ofLp Zm 2 = z := by rw [hZm]; rfl
    obtain ⟨g, hg⟩ : ∃ g : Fin 3 → E → ℝ,
        g = fun j => if j = (2 : Fin 3) then (fun t : E => (-2 : ℝ) * V i t) else V i := ⟨_, rfl⟩
    -- (4a) the uniform smallness of the deviation and its Lipschitz bound,
    -- in the form Step 4 reads them
    have hwsmall : ∀ t ∈ closedBall (0 : E) (3 / 4), |w i t| ≤ δ * ν * r₀ / 8 := by
      intro t ht
      rw [hwval]
      exact hE0 i hiE0 t (hball34 ht)
    have hwLip' : ∀ s ∈ closedBall (0 : E) (3 / 4), ∀ t ∈ closedBall (0 : E) (3 / 4),
        |w i s - w i t| ≤ C * ‖s - t‖ :=
      fun s hs t ht => hwLip i hiE1 s (hball34 hs) t (hball34 ht)
    -- the four thresholds on `r₀` that Step 4 consumes
    have hr014 : r₀ ≤ 1 / 4 := by rw [hr₀]; exact min_le_left _ _
    have hr016 : r₀ ≤ 1 / (16 * C) := by
      rw [hr₀]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have hr0169 : r₀ ≤ 16 / 9 := by
      rw [hr₀]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hr0δ : r₀ ≤ δ / (64 * C ^ 2) := by
      rw [hr₀]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))
    have hval : ∀ Y' : PiLp 2 (fun _ : Fin 3 => E),
        (∑ j, g j (WithLp.ofLp Y' j)) - Ψ i Y'
          = Φ i (WithLp.ofLp Y' 0) (WithLp.ofLp Y' 1) (WithLp.ofLp Y' 2) := by
      intro Y'
      have hsum : (∑ j, g j (WithLp.ofLp Y' j))
          = V i (WithLp.ofLp Y' 0) + V i (WithLp.ofLp Y' 1)
            + (-2 : ℝ) * V i (WithLp.ofLp Y' 2) := by
        rw [Fin.sum_univ_three, hg]
        norm_num [Fin.ext_iff]
      rw [hsum, hΨ, hΦ]
      show V i (WithLp.ofLp Y' 0) + V i (WithLp.ofLp Y' 1)
          + (-2 : ℝ) * V i (WithLp.ofLp Y' 2)
          - (Aff i Y' + Bf (Lc Y') * f ‖Ld Y'‖ + ‖Lh Y'‖ ^ 2 / ‖Ld Y'‖ ^ 2)
        = w i (WithLp.ofLp Y' 0) + w i (WithLp.ofLp Y' 1)
          - 2 * w i (WithLp.ofLp Y' 2)
          - Bf ((2 : ℝ)⁻¹ • (WithLp.ofLp Y' 0 + WithLp.ofLp Y' 1))
              * f ‖WithLp.ofLp Y' 0 - WithLp.ofLp Y' 1‖
          - ‖WithLp.ofLp Y' 2 - (2 : ℝ)⁻¹ • (WithLp.ofLp Y' 0 + WithLp.ofLp Y' 1)‖ ^ 2
              / ‖WithLp.ofLp Y' 0 - WithLp.ofLp Y' 1‖ ^ 2
      rw [hAffv, hLcv, hLdv, hLhv, hwval, hwval, hwval, inner_sub_right,
        inner_add_right, real_inner_smul_right]
      ring
    -- (4a)-(4d): the geometry at the maximizer
    obtain ⟨tpf_rsmall, tpf_h, tpf_r2, tpf_localmax⟩ :=
      ThreePointMaximizerGeometry (Φ i) (Ψ i) g (w i) Bf f x y z cm hv Zm
        r δ ν C C' B_out βk r₀
        (fun x' y' z' => by rw [hΦ]) hcm hhv hrdef hZm0 hZm1 hZm2 hval
        hx34 hy34 hz34 hcm34 hrpos hfnu hwsmall hwLip' (hBfrange cm).1
        (fun h => hBfout cm h)
        (by rw [hcm, hrdef]; exact tpf_upper i hiE1 x y z hx34 hy34 hz34 hxy)
        tpf_max tpf_attain tpf_rlow hβkpos hC'pos hCpos hδ hνpos hC' hBout hBoutpos
        hr014 hr016 hr0169 hr0δ
    -- ===================== STEP 5(b)(c): THE JETS AND `A[σ] ≥ 0` =====================
    -- the paper's three gradients, and `a = B(c) f'(r) - 2|h|²/r³`
    obtain ⟨av, hav⟩ : ∃ av : ℝ, av = Bf cm * f₁ r - 2 * ‖hv‖ ^ 2 / r ^ 3 := ⟨_, rfl⟩
    obtain ⟨ev, hev⟩ : ∃ ev : E, ev = r⁻¹ • (x - y) := ⟨_, rfl⟩
    obtain ⟨p₁, hp₁⟩ : ∃ p₁ : E, p₁ = p i + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm
      - (r ^ 2)⁻¹ • hv + av • ev := ⟨_, rfl⟩
    obtain ⟨p₂, hp₂⟩ : ∃ p₂ : E, p₂ = p i + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm
      - (r ^ 2)⁻¹ • hv - av • ev := ⟨_, rfl⟩
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : E, p₀ = p i - (r ^ 2)⁻¹ • hv := ⟨_, rfl⟩
    obtain ⟨σ, hσ⟩ : ∃ σ : PiLp 2 (fun _ : Fin 3 => E),
        σ = WithLp.toLp 2 (fun j : Fin 3 =>
          if j = 0 then p₁ else if j = 1 then p₂ else p₀) := ⟨_, rfl⟩
    have hσ0 : WithLp.ofLp σ 0 = p₁ := by rw [hσ]; rfl
    have hσ1 : WithLp.ofLp σ 1 = p₂ := by rw [hσ]; rfl
    have hσ2 : WithLp.ofLp σ 2 = p₀ := by rw [hσ]; rfl
    have hLcZm : Lc Zm = cm := by rw [hLcv, hZm0, hZm1, hcm]
    have hLdZm : Ld Zm = x - y := by rw [hLdv, hZm0, hZm1]
    have hLhZm : Lh Zm = hv := by rw [hLhv, hZm0, hZm1, hZm2, hhv, hcm]
    have hf₁r : f₁ r = 1 - 3 * Real.sqrt r / 16 := by rw [hf₁def]
    have hf₁0 : 0 ≤ f₁ r := by
      obtain ⟨-, -, h3, -⟩ := hfbd r hrpos hrle
      rw [hf₁def]; exact le_of_lt h3
    have hf₁le : f₁ r ≤ 1 := by
      obtain ⟨-, -, -, h4⟩ := hfbd r hrpos hrle
      rw [hf₁def]; exact h4
    have hfrle : f r ≤ r := by
      obtain ⟨-, h2, -, -⟩ := hfbd r hrpos hrle
      rw [hfdef]; exact h2
    have hfr0 : 0 ≤ f r := le_trans (mul_nonneg hνpos.le hrpos.le) hfnu
    have hgn : ‖gradient Bf cm‖ = ‖fderiv ℝ Bf cm‖ :=
      (InnerProductSpace.toDual ℝ E).symm.norm_map _
    have hgK : ‖gradient Bf cm‖ ≤ K₁ := by rw [hgn]; exact hK₁ cm hcm34
    have hpq : ‖p i‖ ≤ C := le_trans (hslope i hiE1) (by rw [hC]; linarith only [hL0])
    have hLdne : Ld Zm ≠ 0 := by rw [hLdZm, sub_ne_zero]; exact hxy
    have hLdnorm : ‖Ld Zm‖ = r := by rw [hLdZm, hrdef]
    -- the first derivative of the test at the maximizer, in terms of `cm`, `hv`, `ev`, `av`
    have hgradfml : ∀ ζ : PiLp 2 (fun _ : Fin 3 => E), fderiv ℝ (Ψ i) Zm ζ
        = Aff i ζ + f r * fderiv ℝ Bf cm (Lc ζ) + av * (inner ℝ ev (Ld ζ) : ℝ)
          + 2 * (inner ℝ hv (Lh ζ) : ℝ) / r ^ 2 := by
      intro ζ
      rw [(tpf_grads i Zm hLdne).2 ζ, hLcZm, hLhZm, hLdnorm, hLdZm, ← hev, ← hav]
    -- the three gradient blocks are the paper's `p₁`, `p₂` and `-2p₀`
    have hgradblk : ∀ (j : Fin 3) (vec : E),
        (∀ v : E, fderiv ℝ (Ψ i) Zm (WithLp.toLp 2 (Pi.single j v)) = (inner ℝ vec v : ℝ)) →
        WithLp.ofLp (gradient (Ψ i) Zm) j = vec := by
      intro j vec hvv
      refine ext_inner_left ℝ (fun aa => ?_)
      have hleft : (inner ℝ aa (WithLp.ofLp (gradient (Ψ i) Zm) j) : ℝ)
          = fderiv ℝ (Ψ i) Zm (WithLp.toLp 2 (Pi.single j aa)) := by
        rw [← inner_gradient_left, PiLp.inner_apply,
          Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
        · rw [hblk]
          simp [real_inner_comm]
        · intro k _ hk
          rw [hblk]
          simp [Pi.single_apply, hk]
      rw [hleft, hvv aa]
      exact real_inner_comm aa vec
    have hq0 : WithLp.ofLp (gradient (Ψ i) Zm) 0 = p₁ := by
      refine hgradblk 0 p₁ (fun v => ?_)
      obtain ⟨d1, d2, d3, d4⟩ := hdir0 v
      rw [hgradfml, d1, d2, d3, d4 i, hp₁]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_neg_right,
        real_inner_smul_right, ContinuousLinearMap.map_smul, smul_eq_mul,
        inner_gradient_left]
      ring
    have hq1 : WithLp.ofLp (gradient (Ψ i) Zm) 1 = p₂ := by
      refine hgradblk 1 p₂ (fun v => ?_)
      obtain ⟨d1, d2, d3, d4⟩ := hdir1 v
      rw [hgradfml, d1, d2, d3, d4 i, hp₂]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_neg_right,
        real_inner_smul_right, ContinuousLinearMap.map_smul, smul_eq_mul,
        inner_gradient_left]
      ring
    have hq2 : WithLp.ofLp (gradient (Ψ i) Zm) 2 = -(2 : ℝ) • p₀ := by
      refine hgradblk 2 (-(2 : ℝ) • p₀) (fun v => ?_)
      obtain ⟨d1, d2, d3, d4⟩ := hdir2 v
      rw [hgradfml, d1, d2, d3, d4 i, hp₀]
      simp only [inner_add_left, inner_sub_left, real_inner_smul_left, inner_neg_right,
        real_inner_smul_right, inner_zero_right, map_zero, smul_eq_mul, neg_smul,
        inner_neg_left, inner_gradient_left]
      ring
    -- the three functions are infinity subsolutions on the unit ball
    -- the three functions are infinity subsolutions on the unit ball
    have hg0 : g 0 = V i := by rw [hg]; norm_num [Fin.ext_iff]
    have hg1 : g 1 = V i := by rw [hg]; norm_num [Fin.ext_iff]
    have hg2 : g 2 = fun t : E => (-2 : ℝ) * V i t := by rw [hg]; norm_num
    have hsubV : IsInfSubsolutionOn (ball (0 : E) 1) (V i) := (hV i).1
    have hsub2 : IsInfSubsolutionOn (ball (0 : E) 1) (fun t : E => (-2 : ℝ) * V i t) :=
      (InfHarmonicNegScale (ball (0 : E) 1) (V i) (hV i) (-2) (by norm_num)).1
    have hgsub : ∀ j : Fin 3, IsInfSubsolutionOn (ball (0 : E) 1) (g j) := by
      intro j
      fin_cases j
      · show IsInfSubsolutionOn (ball (0 : E) 1) (g 0)
        rw [hg0]; exact hsubV
      · show IsInfSubsolutionOn (ball (0 : E) 1) (g 1)
        rw [hg1]; exact hsubV
      · show IsInfSubsolutionOn (ball (0 : E) 1) (g 2)
        rw [hg2]; exact hsub2
    have hZmem : ∀ j : Fin 3, WithLp.ofLp Zm j ∈ ball (0 : E) 1 := by
      intro j
      fin_cases j
      · show WithLp.ofLp Zm 0 ∈ ball (0 : E) 1
        rw [hZm0]; exact hball34 hx34
      · show WithLp.ofLp Zm 1 ∈ ball (0 : E) 1
        rw [hZm1]; exact hball34 hy34
      · show WithLp.ofLp Zm 2 ∈ ball (0 : E) 1
        rw [hZm2]; exact hball34 hz34
    have hΨC2' : ContDiffAt ℝ 2 (Ψ i) Zm := (tpf_grads i Zm hLdne).1
    -- (5a)-(5c) eq:tpf-bounds, eq:tpf-jets, eq:tpf-matrix and eq:tpf-Apos
    obtain ⟨tpf_alow, tpf_aub, tpf_K₃, tpf_Apos⟩ :=
      ThreePointJetsAndMatrixInequality (Ψ i) Zm σ g p₀ p₁ p₂ (p i) ev cm hv Bf f f₁
        av r δ C K₁ K₃ B_out hav hp₁ hp₂ hσ0 hσ1 hσ2 hq0 hq1 hq2 hgsub hZmem hΨC2'
        tpf_localmax hrpos hrle hf₁r hf₁le tpf_r2 tpf_h (hBfrange cm).1 (hBfrange cm).2
        hδ hgK hfrle hfr0 hpq hK₃
    have hav0 : 0 < av := lt_of_lt_of_le (by linarith only [hδ]) tpf_alow
    -- ===================== STEP 6: THE SECOND VARIATION IS VERY NEGATIVE ===============
    -- the joint motion `(x,y,z) + τ σ`, read through the four block maps.  The paper's
    -- `ṙ = 2a`, `r̈ = 0`, `ċ = ½(p₁+p₂)` and `ḣ = p₀ - ċ = -½f(r)DB(c)` all come out as
    -- exact identities here, not as estimates, and they enter
    -- `ThreePointTestSecondVariation` as its three hypotheses on `Lc σ`, `Ld σ`, `Lh σ`.
    have hevn : ‖ev‖ = 1 := by
      rw [hev, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hrpos)),
        ← hrdef, inv_mul_cancel₀ (ne_of_gt hrpos)]
    have hxyev : x - y = r • ev := by
      rw [hev, smul_smul, mul_inv_cancel₀ (ne_of_gt hrpos), one_smul]
    have hfnear : ∀ᶠ ρ : ℝ in nhds r, HasDerivAt f (f₁ ρ) ρ := by
      filter_upwards [eventually_gt_nhds hrpos] with ρ hρ
      rw [hfdef, hf₁def]; exact hf1 ρ hρ
    have hf2r : HasDerivAt f₁ (-(3 / (32 * Real.sqrt r))) r := by
      rw [hf₁def]; exact hf2 r hrpos
    -- eq:tpf-neg
    have tpf_neg : fderiv ℝ (fderiv ℝ (Ψ i)) Zm σ σ
        ≤ Mc - 3 * δ ^ 3 / (256 * Real.sqrt r) :=
      ThreePointTestSecondVariation Lc Ld Lh (Aff i) (Ψ i) Zm σ Bf f f₁ cm hv ev p₁ p₂
        r av δ C B_out K₁ K₂ K₃ Mc (fun Y => by rw [hΨ]) hΨC2' hLcZm
        (by rw [hLdZm, hxyev]) hLhZm (by rw [hLcv, hσ0, hσ1])
        (by rw [hLdv, hσ0, hσ1, hp₁, hp₂]; module)
        (by rw [hLhv, hσ0, hσ1, hσ2, hp₀, hp₁, hp₂]; module)
        hevn hrpos hrle hfr0 hfrle hfnear hf2r hf₁0 hf₁le hBfC2 (hBfrange cm).1
        (hK₁ cm hcm34) (hK₂ cm hcm34) hgK hK₁0 hK₂0 tpf_K₃ hδ hav0 tpf_alow tpf_aub
        hCpos tpf_h hMc
    -- ===================== STEP 7: THE CONTRADICTION =====================
    have hthr : r₀ ≤ (3 * δ ^ 3 / (256 * (Mc + 1))) ^ 2 := by
      rw [hr₀]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))
    have hsq : Real.sqrt r < 3 * δ ^ 3 / (256 * (Mc + 1)) :=
      (Real.sqrt_lt' ht0).mpr (lt_of_lt_of_le tpf_rsmall hthr)
    have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
    have hbig : Mc + 1 < 3 * δ ^ 3 / (256 * Real.sqrt r) := by
      rw [lt_div_iff₀ (by linarith only [hs0])]
      have h1 : 256 * (Mc + 1) * Real.sqrt r
          < 256 * (Mc + 1) * (3 * δ ^ 3 / (256 * (Mc + 1))) :=
        mul_lt_mul_of_pos_left hsq (by linarith only [hMc0])
      have h2 : 256 * (Mc + 1) * (3 * δ ^ 3 / (256 * (Mc + 1))) = 3 * δ ^ 3 := by
        field_simp
      rw [h2] at h1
      linarith only [h1]
    linarith only [tpf_Apos, tpf_neg, hbig]
  -- =====================================================================
  -- THE REDUCTION.  Negate the conclusion, then split on the sign.
  -- =====================================================================
  by_contra hcon
  push Not at hcon
  obtain ⟨δ, hδ, hbad⟩ := hcon
  -- the two-sided violation, in the `∀ i₀, ∃ i ≥ i₀` form
  have htwo : ∀ i₀ : ℕ, ∃ i, i₀ ≤ i ∧ ∃ x ∈ ball (0 : E) (1/4), ∃ y ∈ ball (0 : E) (1/4),
      x ≠ y ∧ δ * ‖x - y‖ < |U i x + U i y - 2 * U i ((2 : ℝ)⁻¹ • (x + y))| := by
    intro i₀
    obtain ⟨i, hi, x, hx, y, hy, hxy, hlt⟩ := hbad i₀
    exact ⟨i, hi, x, hx, y, hy, hxy, hlt⟩
  by_cases hpos : ∀ i₀ : ℕ, ∃ i, i₀ ≤ i ∧ ∃ x ∈ ball (0 : E) (1/4),
      ∃ y ∈ ball (0 : E) (1/4),
      x ≠ y ∧ δ * ‖x - y‖ < U i x + U i y - 2 * U i ((2 : ℝ)⁻¹ • (x + y))
  · exact key U q b hU hLip hflat δ hδ hpos
  · -- no positive violation beyond some index: the negated family violates positively
    push Not at hpos
    obtain ⟨j₀, hj₀⟩ := hpos
    refine key (fun i y => -(U i y)) (fun i => -(q i)) (fun i => -(b i)) ?_ ?_ ?_ δ hδ ?_
    · intro i
      have h := InfHarmonicNegScale (ball (0 : E) 1) (U i) (hU i) (-1) (by norm_num)
      have he : (fun y : E => (-1 : ℝ) * U i y) = fun y : E => -(U i y) := by
        funext y; ring
      rw [he] at h
      exact h
    · intro i x hx y hy
      have h := hLip i x hx y hy
      have he : -(U i x) - -(U i y) = -(U i x - U i y) := by ring
      rw [he, abs_neg]
      exact h
    · intro ε hε
      obtain ⟨i₀, hi₀⟩ := hflat ε hε
      refine ⟨i₀, fun i hi x hx => ?_⟩
      have h := hi₀ i hi x hx
      have he : -(U i x) - ((inner ℝ (-(q i)) x : ℝ) + -(b i))
          = -(U i x - ((inner ℝ (q i) x : ℝ) + b i)) := by
        rw [inner_neg_left]; ring
      rw [he, abs_neg]
      exact h
    · intro i₀
      obtain ⟨i, hi, x, hx, y, hy, hxy, hlt⟩ := htwo (max i₀ j₀)
      refine ⟨i, le_trans (le_max_left _ _) hi, x, hx, y, hy, hxy, ?_⟩
      have hA := hj₀ i (le_trans (le_max_right _ _) hi) x hx y hy hxy
      have hgoal : -(U i x) + -(U i y) - 2 * -(U i ((2 : ℝ)⁻¹ • (x + y)))
          = -(U i x + U i y - 2 * U i ((2 : ℝ)⁻¹ • (x + y))) := by ring
      rw [hgoal]
      rcases abs_cases (U i x + U i y - 2 * U i ((2 : ℝ)⁻¹ • (x + y))) with ⟨he, -⟩ | ⟨he, -⟩
      · rw [he] at hlt; linarith
      · rw [he] at hlt; linarith
