module

public import InfHarmonic.BaryConfigOfConvexHull

@[expose] public section
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 4 of Lemma 5.2, the separation-and-perturbation core: at a minimizing
slope `A₀` the center `x` lies in the convex hull of the compact set of maximizing
positions.  Were it outside, strict separation would produce a direction along
which perturbing `A₀` strictly lowers the slope functional, contradicting
minimality. -/
theorem BaryEnvHullOfMinSlope (f : WithLp 2 (F × ℝ) → ℝ) (s t : ℝ) (hs : 0 < s) (x : F)
    (hbdd : ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)})
    (Λ₀ M : ℝ) (hΛ₀ : 0 ≤ Λ₀) (hM : 0 < M) (A₀ : F) (hA₀ : ‖A₀‖ ≤ Λ₀)
    (hmin : ∀ A : F,
      sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y - x)}
        ≤ sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)
          - inner ℝ A (y - x)})
    (hattain : ∀ A : F, ‖A‖ ≤ Λ₀ + 1 → ∃ y₀ : F, ‖y₀‖ ≤ M ∧
      sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)
          - inner ℝ A (y - x)}
        = f (toLp 2 (y₀, t)) - ‖y₀‖ ^ 2 / (2 * s) - inner ℝ A (y₀ - x))
    (hloc : ∀ A : F, ‖A‖ ≤ Λ₀ + 1 → ∀ y : F,
      sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A (y' - x)}
        = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x) → ‖y‖ ≤ M)
    (hΓcont : ContinuousOn (fun A : F =>
      sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)
        - inner ℝ A (y - x)}) (closedBall (0 : F) (Λ₀ + 1)))
    (hfc : ContinuousOn (fun y : F => f (toLp 2 (y, t))) (closedBall (0 : F) M)) :
    x ∈ convexHull ℝ {y : F | ‖y‖ ≤ M ∧
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
        = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y' - x)}} := by
  -- `hs`, `hΛ₀`, `hloc` and `hΓcont` belong to this node's protected signature; the Lean
  -- route below reaches the conclusion without consuming them, so they are acknowledged
  -- here, in the body, rather than by editing the signature line.
  have _ := hs
  have _ := hΛ₀
  have _ := hloc
  have _ := hΓcont
  -- Every slope functional is a genuine least upper bound: this is `hbdd`.
  have hlub : ∀ A y : F, f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)
      ≤ sSup {w : ℝ | ∃ y' : F,
        w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s) - inner ℝ A (y' - x)} :=
    fun A y => le_csSup (hbdd A) ⟨y, rfl⟩
  -- Each slope functional is continuous on the position ball.
  have hφcont : ∀ A : F, ContinuousOn
      (fun y : F => f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x))
      (closedBall (0 : F) M) := by
    intro A
    have h1 : Continuous (fun y : F => ‖y‖ ^ 2 / (2 * s)) := by fun_prop
    have h2 : Continuous (fun y : F => (inner ℝ A (y - x) : ℝ)) := by fun_prop
    exact (hfc.sub h1.continuousOn).sub h2.continuousOn
  -- `E` is nonempty, by attainment at `A₀`.
  obtain ⟨y₀, hy₀M, hy₀eq⟩ := hattain A₀ (le_trans hA₀ (by linarith))
  have hy₀E : y₀ ∈ {y : F | ‖y‖ ≤ M ∧
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
        = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y' - x)}} := ⟨hy₀M, hy₀eq.symm⟩
  -- `E` is compact: a closed subset of the compact position ball.
  have hEc : IsCompact {y : F | ‖y‖ ≤ M ∧
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
        = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y' - x)}} := by
    have hrw : {y : F | ‖y‖ ≤ M ∧
        f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
          = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
            - inner ℝ A₀ (y' - x)}}
        = closedBall (0 : F) M ∩
            (fun y : F => f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)) ⁻¹'
              {sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
                - inner ℝ A₀ (y' - x)}} := by
      ext y
      simp
    rw [hrw]
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0 : F) M)
      ((hφcont A₀).preimage_isClosed_of_isClosed isClosed_closedBall isClosed_singleton)
      Set.inter_subset_left
  by_contra hxK
  -- The hull is compact (BaryConfigOfConvexHull), convex and nonempty.
  have hKc : IsCompact (convexHull ℝ _) := (BaryConfigOfConvexHull _).2 hEc
  have hKne : (convexHull ℝ {y : F | ‖y‖ ≤ M ∧
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
        = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y' - x)}}).Nonempty := ⟨y₀, subset_convexHull ℝ _ hy₀E⟩
  -- Strict separation via the nearest point of the hull to `x`.
  obtain ⟨p, hpK, hpmin⟩ := exists_norm_eq_iInf_of_complete_convex hKne hKc.isComplete
    (convex_convexHull ℝ _) x
  have hvar := (norm_eq_iInf_iff_real_inner_le_zero (convex_convexHull ℝ _) hpK).mp hpmin
  have hpx : p - x ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hxK (h ▸ hpK)
  have hd : 0 < ‖p - x‖ := norm_pos_iff.mpr hpx
  have hene : ‖‖p - x‖⁻¹ • (p - x)‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hd)]
  -- the separation inequality, in the currency the rest of the proof needs
  have hsep : ∀ w ∈ convexHull ℝ {y : F | ‖y‖ ≤ M ∧
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
        = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y' - x)}},
      ‖p - x‖ ≤ (inner ℝ (‖p - x‖⁻¹ • (p - x)) (w - x) : ℝ) := by
    intro w hw
    have h0 := hvar w hw
    rw [show (x - p : F) = -(p - x) from (neg_sub p x).symm, inner_neg_left] at h0
    have h1 : (0 : ℝ) ≤ (inner ℝ (p - x) (w - p) : ℝ) := by linarith
    have h2 : (inner ℝ (p - x) (w - x) : ℝ)
        = (inner ℝ (p - x) (w - p) : ℝ) + ‖p - x‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, ← inner_add_right]
      congr 1
      abel
    rw [real_inner_smul_left, h2]
    have hinv : 0 < ‖p - x‖⁻¹ := inv_pos.mpr hd
    have h3 : ‖p - x‖⁻¹ * ((inner ℝ (p - x) (w - p) : ℝ) + ‖p - x‖ ^ 2)
        = ‖p - x‖⁻¹ * (inner ℝ (p - x) (w - p) : ℝ) + ‖p - x‖ := by
      field_simp
    rw [h3]
    nlinarith [mul_nonneg hinv.le h1]
  -- a uniform bound on the linear term over the position ball
  have hRbd : ∀ y : F, ‖y‖ ≤ M →
      -(inner ℝ (‖p - x‖⁻¹ • (p - x)) (y - x) : ℝ) ≤ M + ‖x‖ := by
    intro y hy
    have hb : ‖y - x‖ ≤ M + ‖x‖ := le_trans (norm_sub_le y x) (by linarith)
    have habs := abs_real_inner_le_norm (‖p - x‖⁻¹ • (p - x)) (y - x)
    rw [hene, one_mul] at habs
    have := (abs_le.mp habs).1
    linarith
  -- On the slice where the separating functional is small, the dual value is strictly beaten.
  obtain ⟨Δ, hΔpos, hΔ⟩ : ∃ Δ : ℝ, 0 < Δ ∧ ∀ y : F, ‖y‖ ≤ M →
      (inner ℝ (‖p - x‖⁻¹ • (p - x)) (y - x) : ℝ) ≤ ‖p - x‖ / 2 →
      f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - x)
        ≤ sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
            - inner ℝ A₀ (y' - x)} - Δ := by
    have hslc : IsCompact (closedBall (0 : F) M ∩
        {y : F | (inner ℝ (‖p - x‖⁻¹ • (p - x)) (y - x) : ℝ) ≤ ‖p - x‖ / 2}) :=
      (isCompact_closedBall _ _).inter_right (isClosed_le (by fun_prop) continuous_const)
    rcases Set.eq_empty_or_nonempty (closedBall (0 : F) M ∩
        {y : F | (inner ℝ (‖p - x‖⁻¹ • (p - x)) (y - x) : ℝ) ≤ ‖p - x‖ / 2}) with hS | hS
    · refine ⟨1, one_pos, fun y hyM hyc => ?_⟩
      exact absurd (Set.mem_empty_iff_false y |>.mp
        (hS ▸ (Set.mem_inter (mem_closedBall_zero_iff.mpr hyM) hyc))) not_false
    · obtain ⟨ŷ, hŷS, hŷmax⟩ := hslc.exists_isMaxOn hS ((hφcont A₀).mono Set.inter_subset_left)
      have hŷM : ‖ŷ‖ ≤ M := mem_closedBall_zero_iff.mp hŷS.1
      have hŷslice : (inner ℝ (‖p - x‖⁻¹ • (p - x)) (ŷ - x) : ℝ) ≤ ‖p - x‖ / 2 := hŷS.2
      have hle := hlub A₀ ŷ
      have hne : f (toLp 2 (ŷ, t)) - ‖ŷ‖ ^ 2 / (2 * s) - inner ℝ A₀ (ŷ - x)
          ≠ sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
              - inner ℝ A₀ (y' - x)} := by
        intro heq
        have hge := hsep ŷ (subset_convexHull ℝ _ ⟨hŷM, heq⟩)
        linarith
      refine ⟨sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y' - x)} - (f (toLp 2 (ŷ, t)) - ‖ŷ‖ ^ 2 / (2 * s)
            - inner ℝ A₀ (ŷ - x)), ?_, fun y hyM hyc => ?_⟩
      · rcases lt_or_eq_of_le hle with hlt | heq
        · linarith
        · exact absurd heq hne
      · have hy := isMaxOn_iff.mp hŷmax y
          (Set.mem_inter (mem_closedBall_zero_iff.mpr hyM) hyc)
        linarith
  -- pick the perturbation size
  obtain ⟨h, hh0, hh1, hhsm⟩ : ∃ h : ℝ, 0 < h ∧ h ≤ 1 ∧
      h * ((M + ‖x‖) + ‖p - x‖ / 2) ≤ Δ := by
    have hC : (0:ℝ) ≤ (M + ‖x‖) + ‖p - x‖ / 2 := by positivity
    have hD : (0:ℝ) < (M + ‖x‖) + ‖p - x‖ / 2 + 1 := by positivity
    refine ⟨min 1 (Δ / ((M + ‖x‖) + ‖p - x‖ / 2 + 1)),
      lt_min one_pos (div_pos hΔpos hD), min_le_left _ _, ?_⟩
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hC) ?_
    rw [div_mul_eq_mul_div, div_le_iff₀ hD]
    have hexp : Δ * ((M + ‖x‖) + ‖p - x‖ / 2 + 1)
        = Δ * ((M + ‖x‖) + ‖p - x‖ / 2) + Δ := by ring
    linarith [hΔpos]
  -- the perturbed slope is admissible
  have hAh : ‖A₀ + h • (‖p - x‖⁻¹ • (p - x))‖ ≤ Λ₀ + 1 := by
    calc ‖A₀ + h • (‖p - x‖⁻¹ • (p - x))‖ ≤ ‖A₀‖ + ‖h • (‖p - x‖⁻¹ • (p - x))‖ :=
          norm_add_le _ _
      _ = ‖A₀‖ + h := by
          rw [norm_smul, hene, mul_one, Real.norm_eq_abs, abs_of_pos hh0]
      _ ≤ Λ₀ + 1 := by linarith
  obtain ⟨yh, hyhM, hyheq⟩ := hattain _ hAh
  -- the perturbed dual value is strictly below the value at A₀, contradicting minimality
  have hkey : sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s)
        - inner ℝ (A₀ + h • (‖p - x‖⁻¹ • (p - x))) (y - x)}
      < sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', t)) - ‖y'‖ ^ 2 / (2 * s)
        - inner ℝ A₀ (y' - x)} := by
    rw [hyheq]
    have hsplit : f (toLp 2 (yh, t)) - ‖yh‖ ^ 2 / (2 * s)
          - inner ℝ (A₀ + h • (‖p - x‖⁻¹ • (p - x))) (yh - x)
        = (f (toLp 2 (yh, t)) - ‖yh‖ ^ 2 / (2 * s) - inner ℝ A₀ (yh - x))
          - h * (inner ℝ (‖p - x‖⁻¹ • (p - x)) (yh - x) : ℝ) := by
      rw [inner_add_left, real_inner_smul_left]
      ring
    rw [hsplit]
    rcases le_or_gt (inner ℝ (‖p - x‖⁻¹ • (p - x)) (yh - x) : ℝ) (‖p - x‖ / 2) with hc | hc
    · have hg := hΔ yh hyhM hc
      have hlin := hRbd yh hyhM
      nlinarith
    · have hb := hlub A₀ yh
      nlinarith
  exact absurd (hmin _) (not_le.mpr hkey)
