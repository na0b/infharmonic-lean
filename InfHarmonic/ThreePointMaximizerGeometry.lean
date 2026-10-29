import InfHarmonic.Preamble
set_option maxHeartbeats 400000
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 4 of paper Proposition 2.6: the geometry at a maximizing triple of the
penalized three-point functional.

Let `Φ x y z = w x + w y - 2 w z - B(c) f(r) - |h|²/r²` with `c = (x+y)/2`,
`h = z - c` and `r = ‖x - y‖`, and let `(x, y, z)` be a triple of the closed
`3/4`-ball at which `Φ` is at least `β` and which maximizes `Φ` over the
triples of that ball whose first two entries are separated by at least
`β/(2 C')`. Four conclusions follow, in the paper's order.

First, `r < r₀`: positivity of the maximum together with `B(c) f(r) ≥ δ ν r/2`
turns the uniform smallness `|w| ≤ δ ν r₀ / 8` of the deviation into
`δ ν r / 2 < δ ν r₀ / 2`. Second, `|h| ≤ 2 C r²`: comparing the maximum with the
admissible competitor `z = c` gives `|h|²/r² ≤ 2 (w(c) - w(z)) ≤ 2 C |h|`.
Third, the two smallness packages `(3/16)√r ≤ 1/4` and `8 C² r ≤ δ/8`, which
follow from `r < r₀` and the thresholds on `r₀` alone. Fourth, writing `Zm` for
the point of `ℓ²(E³)` with coordinates `(x, y, z)` and `Φ` as the difference
`∑ⱼ gⱼ - Ψ` of the three one-point functions and the test, `Zm` is a *local*
maximum of that difference on all of `ℓ²(E³)`: the choice of `B_out` forces
`|c| < 1/2`, and with `r` small and `h = O(r²)` the three points are interior to
their `3/4`-balls while the separation is strictly above the constraint radius,
so the constrained maximum is unconstrained near `Zm`. The intermediate bounds
`|c| < 1/2`, `r < 1/2` and `2 C r² < 1/4` are what the interiority argument
consumes and are not among the conclusions. The ambient space is an arbitrary
finite-dimensional real inner-product space `E`. -/
theorem ThreePointMaximizerGeometry
    (Φ : E → E → E → ℝ) (Psi : PiLp 2 (fun _ : Fin 3 => E) → ℝ) (g : Fin 3 → E → ℝ)
    (w Bf : E → ℝ) (f : ℝ → ℝ)
    (x y z cm hv : E) (Zm : PiLp 2 (fun _ : Fin 3 => E))
    (r δ ν C C' B_out βk r₀ : ℝ)
    (hΦ : ∀ x' y' z' : E, Φ x' y' z' = w x' + w y' - 2 * w z'
      - Bf ((2 : ℝ)⁻¹ • (x' + y')) * f ‖x' - y'‖
      - ‖z' - (2 : ℝ)⁻¹ • (x' + y')‖ ^ 2 / ‖x' - y'‖ ^ 2)
    (hcm : cm = (2 : ℝ)⁻¹ • (x + y)) (hhv : hv = z - cm) (hrdef : r = ‖x - y‖)
    (hZm0 : WithLp.ofLp Zm 0 = x) (hZm1 : WithLp.ofLp Zm 1 = y)
    (hZm2 : WithLp.ofLp Zm 2 = z)
    (hval : ∀ Y : PiLp 2 (fun _ : Fin 3 => E),
      (∑ j, g j (WithLp.ofLp Y j)) - Psi Y
        = Φ (WithLp.ofLp Y 0) (WithLp.ofLp Y 1) (WithLp.ofLp Y 2))
    (hx34 : x ∈ closedBall (0 : E) (3 / 4)) (hy34 : y ∈ closedBall (0 : E) (3 / 4))
    (hz34 : z ∈ closedBall (0 : E) (3 / 4)) (hcm34 : cm ∈ closedBall (0 : E) (3 / 4))
    (hrpos : 0 < r) (hfnu : ν * r ≤ f r)
    (hwsmall : ∀ t ∈ closedBall (0 : E) (3 / 4), |w t| ≤ δ * ν * r₀ / 8)
    (hwLip : ∀ s ∈ closedBall (0 : E) (3 / 4), ∀ t ∈ closedBall (0 : E) (3 / 4),
      |w s - w t| ≤ C * ‖s - t‖)
    (hBfge : δ / 2 ≤ Bf cm) (hBfout : 1 / 2 ≤ ‖cm‖ → Bf cm = B_out)
    (hub : Φ x y z ≤ C * r + C ^ 2 * r ^ 2 - Bf cm * f r)
    (tpf_max : βk ≤ Φ x y z)
    (tpf_attain : ∀ x' y' z' : E, x' ∈ closedBall (0 : E) (3 / 4) →
      y' ∈ closedBall (0 : E) (3 / 4) → z' ∈ closedBall (0 : E) (3 / 4) →
      βk / (2 * C') ≤ ‖x' - y'‖ → Φ x' y' z' ≤ Φ x y z)
    (tpf_rlow : βk / C' ≤ ‖x - y‖)
    (hβkpos : 0 < βk) (hC'pos : 0 < C') (hCpos : 0 < C) (hδ : 0 < δ) (hνpos : 0 < ν)
    (hC' : C' = C + 3 / 2 * C ^ 2) (hBout : B_out = C' / ν + δ / 2 + 1)
    (hBoutpos : δ / 2 ≤ B_out)
    (hr014 : r₀ ≤ 1 / 4) (hr016 : r₀ ≤ 1 / (16 * C))
    (hr0169 : r₀ ≤ 16 / 9) (hr0δ : r₀ ≤ δ / (64 * C ^ 2)) :
    r < r₀ ∧ ‖hv‖ ≤ 2 * C * r ^ 2
      ∧ (3 / 16 * Real.sqrt r ≤ 1 / 4 ∧ 8 * C ^ 2 * r ≤ δ / 8)
      ∧ IsLocalMax (fun Y : PiLp 2 (fun _ : Fin 3 => E) =>
          (∑ j, g j (WithLp.ofLp Y j)) - Psi Y) Zm := by
  have hC2pos : (0 : ℝ) < C ^ 2 := pow_pos hCpos 2
  have hΦz : Φ x y z = w x + w y - 2 * w z - Bf cm * f r - ‖hv‖ ^ 2 / r ^ 2 := by
    rw [hΦ, hcm, hhv, hcm, hrdef]
  have hmaxpos : 0 < Φ x y z := lt_of_lt_of_le hβkpos tpf_max
  -- (4a) eq:tpf-rsmall, with `ε = ε₀ = δ ν r₀ / 8`
  have tpf_rsmall : r < r₀ := by
    have h1 := hwsmall x hx34
    have h2 := hwsmall y hy34
    have h3 := hwsmall z hz34
    rw [abs_le] at h1 h2 h3
    have hpen : 0 ≤ ‖hv‖ ^ 2 / r ^ 2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hmp := hmaxpos
    rw [hΦz] at hmp
    -- `B(c) f(r) ≥ (δ/2)(ν r)`
    have hνr : (0 : ℝ) ≤ ν * r := mul_nonneg hνpos.le hrpos.le
    have hfr0 : 0 ≤ f r := le_trans hνr hfnu
    have hprod : δ / 2 * (ν * r) ≤ Bf cm * f r := by
      have hstep1 : δ / 2 * (ν * r) ≤ δ / 2 * f r :=
        mul_le_mul_of_nonneg_left hfnu (by linarith)
      have hstep2 : δ / 2 * f r ≤ Bf cm * f r := mul_le_mul_of_nonneg_right hBfge hfr0
      linarith only [hstep1, hstep2]
    -- hence `δ ν r / 2 < 4 ε₀ = δ ν r₀ / 2`, which is `r < r₀`
    have hmul : δ * ν / 2 * r < δ * ν / 2 * r₀ := by
      linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, hmp, hprod, hpen]
    exact lt_of_mul_lt_mul_left hmul (by linarith only [mul_pos hδ hνpos])
  -- (4b) eq:tpf-h
  have tpf_h : ‖hv‖ ≤ 2 * C * r ^ 2 := by
    have hlow : βk / (2 * C') ≤ ‖x - y‖ := by
      have h1 : βk / (2 * C') = βk / C' / 2 := by
        rw [eq_div_iff (by norm_num), div_mul_eq_mul_div, div_eq_div_iff (by positivity)
          (by positivity)]
        ring
      have h2 : 0 ≤ βk / C' := le_of_lt (div_pos hβkpos hC'pos)
      rw [h1]; linarith only [tpf_rlow, h2]
    have hcomp := tpf_attain x y cm hx34 hy34 hcm34 hlow
    have hΦcm : Φ x y cm = w x + w y - 2 * w cm - Bf cm * f r := by
      rw [hΦ, ← hcm, ← hrdef, sub_self, norm_zero]
      simp
    rw [hΦcm, hΦz] at hcomp
    -- `|h|²/r² ≤ 2 (w c - w z) ≤ 2 C |h|`
    have hwlip := hwLip cm hcm34 z hz34
    have hnd : ‖cm - z‖ = ‖hv‖ := by
      rw [hhv, ← norm_neg]; congr 1; abel
    rw [hnd, abs_le] at hwlip
    have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hrpos 2
    have hstep : ‖hv‖ ^ 2 / r ^ 2 ≤ 2 * C * ‖hv‖ := by linarith only [hwlip.2, hcomp]
    rw [div_le_iff₀ hr2] at hstep
    rcases eq_or_lt_of_le (norm_nonneg hv) with h0 | h0
    · rw [← h0]; exact mul_nonneg (by linarith only [hCpos]) (sq_nonneg r)
    · have hstep' : ‖hv‖ * ‖hv‖ ≤ 2 * C * r ^ 2 * ‖hv‖ := by linarith only [hstep]
      exact le_of_mul_le_mul_right hstep' h0
  -- (4c) the maximizing midpoint is interior to the localization region
  have tpf_cnorm : ‖cm‖ < 1 / 2 := by
    by_contra hcon
    rw [not_lt] at hcon
    have hBfv : Bf cm = B_out := hBfout hcon
    have h := hub
    rw [hBfv] at h
    have hBν : B_out * ν = C' + (δ / 2 + 1) * ν := by
      rw [hBout]; field_simp; ring
    have hkey : 0 ≤ C ^ 2 * r * (3 / 2 - r) :=
      mul_nonneg (mul_nonneg (sq_nonneg C) hrpos.le)
        (by linarith only [tpf_rsmall, hr014])
    have hBout0 : 0 < B_out := lt_of_lt_of_le (by linarith) hBoutpos
    have hBf1 : B_out * (ν * r) ≤ B_out * f r :=
      mul_le_mul_of_nonneg_left hfnu hBout0.le
    have hBνr : B_out * (ν * r) = (C + 3 / 2 * C ^ 2 + (δ / 2 + 1) * ν) * r := by
      rw [← hC', ← hBν]; ring
    have hpos2 : 0 < (δ / 2 + 1) * ν * r :=
      mul_pos (mul_pos (by linarith only [hδ]) hνpos) hrpos
    linarith only [h, hBf1, hkey, hBνr, hmaxpos, hpos2]
  -- the two smallness packages, which follow from `r < r₀` alone
  have tpf_r1 : r < 1 / 2 ∧ 2 * C * r ^ 2 < 1 / 4 := by
    have hr14 : r < 1 / 4 := lt_of_lt_of_le tpf_rsmall hr014
    have hr16 : r < 1 / (16 * C) := lt_of_lt_of_le tpf_rsmall hr016
    have h16' : r * (16 * C) < 1 := by
      rw [← lt_div_iff₀ (by linarith only [hCpos])]; exact hr16
    refine ⟨by linarith only [hr14], ?_⟩
    nlinarith only [hrpos, hr14, h16', hCpos]
  have tpf_r2 : 3 / 16 * Real.sqrt r ≤ 1 / 4 ∧ 8 * C ^ 2 * r ≤ δ / 8 := by
    have hr169 : r ≤ 16 / 9 := le_of_lt (lt_of_lt_of_le tpf_rsmall hr0169)
    have hrδ : r ≤ δ / (64 * C ^ 2) := le_of_lt (lt_of_lt_of_le tpf_rsmall hr0δ)
    refine ⟨?_, ?_⟩
    · have h1 : Real.sqrt r ≤ Real.sqrt (16 / 9) := Real.sqrt_le_sqrt hr169
      have h2 : Real.sqrt (16 / 9) = 4 / 3 := by
        rw [show (16 : ℝ) / 9 = (4 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      rw [h2] at h1
      linarith only [h1]
    · rw [le_div_iff₀ (by linarith only [hC2pos])] at hrδ
      linarith only [hrδ]
  -- (4d) eq:tpf-localmax: the maximizer is a local maximum on the whole product space
  -- the three points are INTERIOR to the 3/4-balls, which is what makes the constrained
  -- maximum a local maximum on all of the product space
  have hxcm : ‖x - cm‖ = (2 : ℝ)⁻¹ * r := by
    rw [hcm, hrdef, show x - (2 : ℝ)⁻¹ • (x + y) = (2 : ℝ)⁻¹ • (x - y) by module,
      norm_smul, Real.norm_eq_abs]
    norm_num
  have hycm : ‖y - cm‖ = (2 : ℝ)⁻¹ * r := by
    rw [hcm, hrdef, show y - (2 : ℝ)⁻¹ • (x + y) = -((2 : ℝ)⁻¹ • (x - y)) by module,
      norm_neg, norm_smul, Real.norm_eq_abs]
    norm_num
  have hzcm : ‖z - cm‖ = ‖hv‖ := by rw [hhv]
  have hptlt : ∀ t : E, ‖t - cm‖ < 1 / 4 → ‖t‖ < 3 / 4 := by
    intro t ht
    have h1 : ‖t‖ ≤ ‖cm‖ + ‖t - cm‖ := by
      calc ‖t‖ = ‖cm + (t - cm)‖ := by congr 1; abel
        _ ≤ ‖cm‖ + ‖t - cm‖ := norm_add_le _ _
    linarith only [h1, ht, tpf_cnorm]
  have hxlt : ‖x‖ < 3 / 4 := hptlt x (by rw [hxcm]; linarith only [tpf_r1.1])
  have hylt : ‖y‖ < 3 / 4 := hptlt y (by rw [hycm]; linarith only [tpf_r1.1])
  have hzlt : ‖z‖ < 3 / 4 := hptlt z (by
    rw [hzcm]; linarith only [tpf_h, tpf_r1.2])
  have hrstrict : βk / (2 * C') < r := by
    have h1 : βk / (2 * C') < βk / C' := by
      rw [div_lt_div_iff₀ (by linarith only [hC'pos]) hC'pos]
      nlinarith only [hβkpos, hC'pos]
    linarith only [h1, tpf_rlow, hrdef]
  have hproj : ∀ j : Fin 3,
      Continuous (fun Y : PiLp 2 (fun _ : Fin 3 => E) => WithLp.ofLp Y j) :=
    fun j => (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => E) j).continuous
  have hevlt : ∀ (j : Fin 3) (t : E), WithLp.ofLp Zm j = t → ‖t‖ < 3 / 4 →
      ∀ᶠ Y : PiLp 2 (fun _ : Fin 3 => E) in nhds Zm, ‖WithLp.ofLp Y j‖ < 3 / 4 := by
    intro j t ht hlt
    have hc : ContinuousAt
        (fun Y : PiLp 2 (fun _ : Fin 3 => E) => ‖WithLp.ofLp Y j‖) Zm :=
      (hproj j).norm.continuousAt
    have h0 : (fun Y : PiLp 2 (fun _ : Fin 3 => E) => ‖WithLp.ofLp Y j‖) Zm < 3 / 4 := by
      show ‖WithLp.ofLp Zm j‖ < 3 / 4
      rw [ht]; exact hlt
    exact Filter.Tendsto.eventually hc (eventually_lt_nhds h0)
  have hev0 := hevlt 0 x hZm0 hxlt
  have hev1 := hevlt 1 y hZm1 hylt
  have hev2 := hevlt 2 z hZm2 hzlt
  have hevd : ∀ᶠ Y : PiLp 2 (fun _ : Fin 3 => E) in nhds Zm,
      βk / (2 * C') < ‖WithLp.ofLp Y 0 - WithLp.ofLp Y 1‖ := by
    have hc : ContinuousAt (fun Y : PiLp 2 (fun _ : Fin 3 => E) =>
        ‖WithLp.ofLp Y 0 - WithLp.ofLp Y 1‖) Zm :=
      ((hproj 0).sub (hproj 1)).norm.continuousAt
    have h0 : βk / (2 * C') < (fun Y : PiLp 2 (fun _ : Fin 3 => E) =>
        ‖WithLp.ofLp Y 0 - WithLp.ofLp Y 1‖) Zm := by
      show βk / (2 * C') < ‖WithLp.ofLp Zm 0 - WithLp.ofLp Zm 1‖
      rw [hZm0, hZm1, ← hrdef]; exact hrstrict
    exact Filter.Tendsto.eventually hc (eventually_gt_nhds h0)
  have tpf_localmax : IsLocalMax (fun Y : PiLp 2 (fun _ : Fin 3 => E) =>
      (∑ j, g j (WithLp.ofLp Y j)) - Psi Y) Zm := by
    filter_upwards [hev0, hev1, hev2, hevd] with Y h0 h1 h2 hd
    show (∑ j, g j (WithLp.ofLp Y j)) - Psi Y
      ≤ (∑ j, g j (WithLp.ofLp Zm j)) - Psi Zm
    rw [hval Y, hval Zm, hZm0, hZm1, hZm2]
    refine tpf_attain _ _ _ ?_ ?_ ?_ (le_of_lt hd)
    · rw [mem_closedBall, dist_eq_norm, sub_zero]; linarith only [h0]
    · rw [mem_closedBall, dist_eq_norm, sub_zero]; linarith only [h1]
    · rw [mem_closedBall, dist_eq_norm, sub_zero]; linarith only [h2]
  exact ⟨tpf_rsmall, tpf_h, tpf_r2, tpf_localmax⟩
