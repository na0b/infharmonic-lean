import InfHarmonic.Preamble
set_option maxHeartbeats 400000
open Set Metric

/-- Step 8 of paper Lemma 3.2 (`FamilyFlatness`): the small-scale limit has
vanishing midpoint defect on the closed `2`-ball.

Work in `X = ℓ²(ℝ^d × ℝ)`. The data are a family `U_i : X → ℝ`, centers
`z_i ∈ X`, small radii `r_i > 0`, slow scales `R_k > 0`, a base point `z_*`, a
function `W : X → ℝ` and an index map `κ`. Two convergence hypotheses are
assumed, both along `κ` and both supplied by
\noderef{SlowScalesAndBlowupLimit}: the slow-scale limit
`(|z_{κ k} - z_*| + r_{κ k}) / R_k → 0`, and the uniform convergence on the
closed `2`-ball of the rescalings
`W_k(H) = (U_{κ k}(z_{κ k} + r_{κ k} H) - U_{κ k}(z_{κ k})) / r_{κ k}` to `W`.
The third hypothesis is the three-point estimate at the scales `R_k`, in the
asymptotic form it carries: for every `ε' > 0` the midpoint defect of the
blow-ups at `z_*` at scale `R_k` is at most `ε' |X - Y|` for all distinct
`X, Y` in the open `1/4`-ball, once `k` is large.

The conclusion is that `W(H) + W(K) = 2 W((H + K)/2)` for all `H, K` in the
closed `2`-ball. The proof substitutes `X = (z_{κ k} - z_* + r_{κ k} H) / R_k`
and likewise for `Y`: the slow-scale limit puts both inside the `1/4`-ball for
large `k`, the images of `X`, `Y` and their midpoint under
`V ↦ z_* + R_k V` are exactly the three points of `W_k`, and the two midpoint
defects differ by the factor `r_{κ k} / R_k`, which cancels against
`|X - Y| = (r_{κ k}/R_k)|H - K|`. The ambient space is the Euclidean
space-time of dimension `d + 1`. -/
theorem BlowupLimitVanishingMidpointDefect (d : ℕ)
    (Uq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (zq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (rq Rs : ℕ → ℝ) (zstar : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (Wlim : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ) (κ : ℕ → ℕ)
    (hrq0 : ∀ i, 0 < rq i) (hRs0 : ∀ k, 0 < Rs k)
    (hslow : Filter.Tendsto
      (fun k => (‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k) Filter.atTop (nhds 0))
    (hWconv : TendstoUniformlyOn
      (fun k Hv => (Uq (κ k) (zq (κ k) + rq (κ k) • Hv)
        - Uq (κ k) (zq (κ k))) / rq (κ k)) Wlim Filter.atTop
      (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2))
    (tpf : ∀ ε' > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      ∀ X ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 4),
      ∀ Y ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 4), X ≠ Y →
        |(Uq (κ k) (zstar + Rs k • X) - Uq (κ k) zstar) / Rs k
          + (Uq (κ k) (zstar + Rs k • Y) - Uq (κ k) zstar) / Rs k
          - 2 * ((Uq (κ k) (zstar + Rs k • ((2 : ℝ)⁻¹ • (X + Y))) - Uq (κ k) zstar)
              / Rs k)| ≤ ε' * ‖X - Y‖) :
    ∀ H ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
    ∀ K ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
    Wlim H + Wlim K = 2 * Wlim ((2 : ℝ)⁻¹ • (H + K)) := by
  obtain ⟨Wk, hWkdef⟩ : ∃ Wk : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      Wk = fun k Hv => (Uq (κ k) (zq (κ k) + rq (κ k) • Hv)
        - Uq (κ k) (zq (κ k))) / rq (κ k) := ⟨_, rfl⟩
  have hWconvK : TendstoUniformlyOn Wk Wlim Filter.atTop
      (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2) := by
    rw [hWkdef]; exact hWconv
  intro H hH K hK
  have hHm : H ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := hH
  have hKm : K ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := hK
  rw [mem_closedBall, dist_zero_right] at hH hK
  have hmid2 : (2 : ℝ)⁻¹ • (H + K)
      ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := by
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖(2 : ℝ)⁻¹ • (H + K)‖ = 2⁻¹ * ‖H + K‖ := by
      rw [norm_smul, Real.norm_eq_abs]; norm_num
    have h2 : ‖H + K‖ ≤ ‖H‖ + ‖K‖ := norm_add_le _ _
    rw [h1]
    linarith only [h2, hH, hK]
  rcases eq_or_ne H K with rfl | hne
  · rw [show (2 : ℝ)⁻¹ • (H + H) = H from by module]
    ring
  have hHKpos : 0 < ‖H - K‖ := by
    rw [norm_pos_iff, sub_ne_zero]
    exact hne
  -- the quantitative form: the defect is below every `ε' > 0`
  have hbound : ∀ ε' > 0,
      |Wlim H + Wlim K - 2 * Wlim ((2 : ℝ)⁻¹ • (H + K))| ≤ ε' := by
    intro ε' hε'
    obtain ⟨δ, hδ0, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ‖H - K‖ ≤ ε' / 2 := by
      refine ⟨ε' / (2 * ‖H - K‖), by positivity, le_of_eq ?_⟩
      field_simp
    obtain ⟨k₀, hk₀⟩ := tpf δ hδ0
    -- the substituted points of Step 8
    obtain ⟨Xs, hXsdef⟩ : ∃ Xs : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        Xs = fun k => (Rs k)⁻¹ • (zq (κ k) - zstar + rq (κ k) • H) := ⟨_, rfl⟩
    obtain ⟨Ys, hYsdef⟩ : ∃ Ys : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        Ys = fun k => (Rs k)⁻¹ • (zq (κ k) - zstar + rq (κ k) • K) := ⟨_, rfl⟩
    -- their images under `X ↦ z_* + R X` are the three points of `W_i`
    have himgX : ∀ k : ℕ, zstar + Rs k • Xs k = zq (κ k) + rq (κ k) • H := by
      intro k
      have hRne : Rs k ≠ 0 := ne_of_gt (hRs0 k)
      rw [hXsdef]
      match_scalars <;> (field_simp; try ring)
    have himgY : ∀ k : ℕ, zstar + Rs k • Ys k = zq (κ k) + rq (κ k) • K := by
      intro k
      have hRne : Rs k ≠ 0 := ne_of_gt (hRs0 k)
      rw [hYsdef]
      match_scalars <;> (field_simp; try ring)
    have himgM : ∀ k : ℕ, zstar + Rs k • ((2 : ℝ)⁻¹ • (Xs k + Ys k))
        = zq (κ k) + rq (κ k) • ((2 : ℝ)⁻¹ • (H + K)) := by
      intro k
      have hRne : Rs k ≠ 0 := ne_of_gt (hRs0 k)
      rw [hXsdef, hYsdef]
      match_scalars <;> (field_simp; try ring)
    have hXYdiff : ∀ k : ℕ, Xs k - Ys k = (rq (κ k) / Rs k) • (H - K) := by
      intro k
      have hRne : Rs k ≠ 0 := ne_of_gt (hRs0 k)
      rw [hXsdef, hYsdef]
      match_scalars <;> (field_simp; try ring)
    -- eq:ff-slow puts them inside `B_{1/4}`, which is `ThreePointFlatness`'s domain
    have hXnorm : ∀ k : ℕ,
        ‖Xs k‖ ≤ 2 * ((‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k) := by
      intro k
      have hinv : (0 : ℝ) < (Rs k)⁻¹ := inv_pos.mpr (hRs0 k)
      rw [hXsdef]
      show ‖(Rs k)⁻¹ • (zq (κ k) - zstar + rq (κ k) • H)‖
        ≤ 2 * ((‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hinv)]
      have h1 : ‖zq (κ k) - zstar + rq (κ k) • H‖
          ≤ ‖zq (κ k) - zstar‖ + ‖rq (κ k) • H‖ := norm_add_le _ _
      have h2 : ‖rq (κ k) • H‖ = rq (κ k) * ‖H‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hrq0 (κ k)))]
      have h3 : rq (κ k) * ‖H‖ ≤ rq (κ k) * 2 :=
        mul_le_mul_of_nonneg_left hH (le_of_lt (hrq0 (κ k)))
      rw [h2] at h1
      have h4 : ‖zq (κ k) - zstar + rq (κ k) • H‖
          ≤ 2 * (‖zq (κ k) - zstar‖ + rq (κ k)) := by
        linarith only [h1, h3, norm_nonneg (zq (κ k) - zstar)]
      calc (Rs k)⁻¹ * ‖zq (κ k) - zstar + rq (κ k) • H‖
          ≤ (Rs k)⁻¹ * (2 * (‖zq (κ k) - zstar‖ + rq (κ k))) :=
            mul_le_mul_of_nonneg_left h4 (le_of_lt hinv)
        _ = 2 * ((‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k) := by
            rw [div_eq_inv_mul]; ring
    have hYnorm : ∀ k : ℕ,
        ‖Ys k‖ ≤ 2 * ((‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k) := by
      intro k
      have hinv : (0 : ℝ) < (Rs k)⁻¹ := inv_pos.mpr (hRs0 k)
      rw [hYsdef]
      show ‖(Rs k)⁻¹ • (zq (κ k) - zstar + rq (κ k) • K)‖
        ≤ 2 * ((‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hinv)]
      have h1 : ‖zq (κ k) - zstar + rq (κ k) • K‖
          ≤ ‖zq (κ k) - zstar‖ + ‖rq (κ k) • K‖ := norm_add_le _ _
      have h2 : ‖rq (κ k) • K‖ = rq (κ k) * ‖K‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (hrq0 (κ k)))]
      have h3 : rq (κ k) * ‖K‖ ≤ rq (κ k) * 2 :=
        mul_le_mul_of_nonneg_left hK (le_of_lt (hrq0 (κ k)))
      rw [h2] at h1
      have h4 : ‖zq (κ k) - zstar + rq (κ k) • K‖
          ≤ 2 * (‖zq (κ k) - zstar‖ + rq (κ k)) := by
        linarith only [h1, h3, norm_nonneg (zq (κ k) - zstar)]
      calc (Rs k)⁻¹ * ‖zq (κ k) - zstar + rq (κ k) • K‖
          ≤ (Rs k)⁻¹ * (2 * (‖zq (κ k) - zstar‖ + rq (κ k))) :=
            mul_le_mul_of_nonneg_left h4 (le_of_lt hinv)
        _ = 2 * ((‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k) := by
            rw [div_eq_inv_mul]; ring
    -- one index at which all three requirements hold
    obtain ⟨k, hk, hgk, hclose⟩ : ∃ k : ℕ, k₀ ≤ k ∧
        (‖zq (κ k) - zstar‖ + rq (κ k)) / Rs k < 1 / 8 ∧
        ∀ w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
          dist (Wlim w) (Wk k w) < ε' / 8 := by
      refine (((Filter.eventually_ge_atTop k₀).and
        ((hslow.eventually_lt_const (by norm_num : (0:ℝ) < 1 / 8)).and
          (Metric.tendstoUniformlyOn_iff.mp hWconvK (ε' / 8)
            (by linarith only [hε'])))).exists).imp ?_
      exact fun k h => ⟨h.1, h.2.1, h.2.2⟩
    have hXm : Xs k ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 4) := by
      rw [mem_ball, dist_zero_right]
      linarith only [hXnorm k, hgk]
    have hYm : Ys k ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 4) := by
      rw [mem_ball, dist_zero_right]
      linarith only [hYnorm k, hgk]
    have hfac : 0 < rq (κ k) / Rs k := div_pos (hrq0 (κ k)) (hRs0 k)
    have hne' : Xs k ≠ Ys k := by
      intro heq
      have h0 : Xs k - Ys k = 0 := by rw [heq, sub_self]
      rw [hXYdiff k] at h0
      rcases smul_eq_zero.mp h0 with h | h
      · exact absurd h (ne_of_gt hfac)
      · exact hne (by rwa [sub_eq_zero] at h)
    have hXYn : ‖Xs k - Ys k‖ = rq (κ k) / Rs k * ‖H - K‖ := by
      rw [hXYdiff k, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hfac)]
    have hthree := hk₀ k hk (Xs k) hXm (Ys k) hYm hne'
    rw [himgX k, himgY k, himgM k, hXYn] at hthree
    -- the two midpoint defects differ by the factor `R_i / r_i`
    have hprop : (Uq (κ k) (zq (κ k) + rq (κ k) • H) - Uq (κ k) zstar) / Rs k
          + (Uq (κ k) (zq (κ k) + rq (κ k) • K) - Uq (κ k) zstar) / Rs k
          - 2 * ((Uq (κ k) (zq (κ k) + rq (κ k) • ((2 : ℝ)⁻¹ • (H + K)))
            - Uq (κ k) zstar) / Rs k)
        = rq (κ k) / Rs k
          * (Wk k H + Wk k K - 2 * Wk k ((2 : ℝ)⁻¹ • (H + K))) := by
      have hRne : Rs k ≠ 0 := ne_of_gt (hRs0 k)
      have hrne : rq (κ k) ≠ 0 := ne_of_gt (hrq0 (κ k))
      simp only [hWkdef]
      field_simp
      ring
    rw [hprop, abs_mul, abs_of_pos hfac,
      show δ * (rq (κ k) / Rs k * ‖H - K‖)
        = rq (κ k) / Rs k * (δ * ‖H - K‖) from by ring] at hthree
    have hWdef : |Wk k H + Wk k K - 2 * Wk k ((2 : ℝ)⁻¹ • (H + K))| ≤ δ * ‖H - K‖ :=
      le_of_mul_le_mul_left hthree hfac
    -- eq:ff-Wconv at the three points `H`, `K` and the midpoint
    have hcH := abs_lt.mp (by rw [← Real.dist_eq]; exact hclose H hHm)
    have hcK := abs_lt.mp (by rw [← Real.dist_eq]; exact hclose K hKm)
    have hcM := abs_lt.mp
      (by rw [← Real.dist_eq]; exact hclose ((2 : ℝ)⁻¹ • (H + K)) hmid2)
    have hWb := abs_le.mp hWdef
    rw [abs_le]
    constructor <;>
      linarith only [hcH.1, hcH.2, hcK.1, hcK.2, hcM.1, hcM.2, hWb.1, hWb.2, hδle]
  rcases le_or_gt |Wlim H + Wlim K - 2 * Wlim ((2 : ℝ)⁻¹ • (H + K))| 0 with hD | hD
  · have hz := abs_eq_zero.mp (le_antisymm hD (abs_nonneg _))
    linarith only [hz]
  · have h := hbound (|Wlim H + Wlim K - 2 * Wlim ((2 : ℝ)⁻¹ • (H + K))| / 2)
      (by linarith only [hD])
    linarith only [h, hD]
