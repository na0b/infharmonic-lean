module

public import InfHarmonic.GradientDiffSecondOrder
public import InfHarmonic.MoreauEnvelopeGradient

@[expose] public section
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 2 of Alexandrov's theorem: along the curve `h ↦ u (y + h)` traced by the
proximal map, `ψ` has a second-order expansion whose quadratic form is
`⟪(I - P) h, P h⟫`, where `P` is the derivative of `u` at `y`. -/
theorem MoreauCurveExpansion (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E)
    (hu : IsMoreauProx ψ u) (y : E) (P : E →L[ℝ] E) (hP : HasFDerivAt u P y) :
    ∀ δ > 0, ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
      |ψ (u (y + h)) - ψ (u y) - inner ℝ (y - u y) (u (y + h) - u y)
        - inner ℝ ((ContinuousLinearMap.id ℝ E - P) h) (P h) / 2| ≤ δ * ‖h‖ ^ 2 := by
  -- THE ALGEBRAIC REDUCTION, recorded here rather than in scratch so it is durable.
  -- With x = u y, p = y - x, Q = id - P, xh = u (y + h) and rho = xh - x - P h, put
  --   E1 := psi_1 (y+h) - psi_1 y - <p,h> - <Q h, h>/2   (the GradientDiffSecondOrder error)
  --   E2 := <Q h, rho> - ‖rho‖^2 / 2.
  -- Then the target equals E1 + E2 EXACTLY (see `htgt` below).  The route: psi xh =
  -- psi_1 (y+h) - ‖v(y+h)‖^2/2 and psi x = psi_1 y - ‖p‖^2/2, and the exact identity
  -- v(y+h) = p + Q h - rho expands ‖v(y+h)‖^2 - ‖p‖^2.  Three cancellations finish it, each
  -- just `Q h + P h = h` or `xh - x = P h + rho`:
  --   <p,h> - <p,Qh> - <p,Ph> = 0,  <Qh,h>/2 - ‖Qh‖^2/2 - <Qh,Ph>/2 = 0,  +<p,rho> - <p,rho> = 0.
  -- Since `ring` does not know bilinearity of `inner`, every inner product is expanded onto the
  -- atoms {p, Q h, P h, rho} first (hexp, hph, hQhh, hpxh) and only then handed to `ring`.
  -- The Moreau envelope `F = ψ₁`, whose gradient is `v = id - u`.
  obtain ⟨F, hF⟩ : ∃ F : E → ℝ, F = fun w : E => ψ (u w) + ‖u w - w‖ ^ 2 / 2 := ⟨_, rfl⟩
  -- (A) `MoreauEnvelopeGradient`'s bound is QUADRATIC, hence o(‖z'-z‖): that is the gradient.
  have hgradF : ∀ z : E, HasGradientAt F (z - u z) z := by
    intro z
    rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    rw [Metric.eventually_nhds_iff]
    refine ⟨2 * c / 3, by positivity, fun z' hz' => ?_⟩
    have hb := MoreauEnvelopeGradient ψ hψ u hu z z'
    have hd : ‖z' - z‖ < 2 * c / 3 := by rw [← dist_eq_norm]; exact hz'
    rw [hF, Real.norm_eq_abs]
    calc |ψ (u z') + ‖u z' - z'‖ ^ 2 / 2 - (ψ (u z) + ‖u z - z‖ ^ 2 / 2)
            - (inner ℝ (z - u z) (z' - z) : ℝ)|
        ≤ 3 / 2 * ‖z' - z‖ ^ 2 := hb
      _ ≤ c * ‖z' - z‖ := by nlinarith [norm_nonneg (z' - z), hd, hc]
  -- (B) `u` and hence `v = id - u` are 1-Lipschitz, so `v` is continuous.
  have hulip : ∀ a b : E, ‖u a - u b‖ ≤ ‖a - b‖ := by
    intro a b
    have hm := MoreauProxMonotone ψ hψ a b (u a) (u b) (hu a) (hu b)
    nlinarith [sq_nonneg ‖(a - u a) - (b - u b)‖, norm_nonneg (u a - u b), norm_nonneg (a - b)]
  have hucont : Continuous u := by
    refine LipschitzWith.continuous (K := 1) ?_
    intro a b
    rw [edist_dist, edist_dist, dist_eq_norm, dist_eq_norm]
    simp only [ENNReal.coe_one, one_mul]
    exact ENNReal.ofReal_le_ofReal (hulip a b)
  have hvc : Continuous (fun z : E => z - u z) := continuous_id.sub hucont
  -- (C) `v = id - u` is differentiable at `y` with derivative `id - P`.
  have hvd : HasFDerivAt (fun z : E => z - u z) (ContinuousLinearMap.id ℝ E - P) y :=
    (hasFDerivAt_id y).sub hP
  intro δ hδ
  -- error budget: δ' = d small enough that ‖Q‖d + d²/2 ≤ δ/2, which is realizable because
  -- ‖Q‖ is a fixed finite operator norm built from the statement's own data.
  obtain ⟨d, hd0, hd1, hdb⟩ : ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧
      ‖ContinuousLinearMap.id ℝ E - P‖ * d + d ^ 2 / 2 ≤ δ / 2 := by
    have hQn : (0:ℝ) ≤ ‖ContinuousLinearMap.id ℝ E - P‖ := norm_nonneg _
    have hpos : (0:ℝ) < ‖ContinuousLinearMap.id ℝ E - P‖ + 1 := by linarith
    refine ⟨min 1 ((δ / 2) / (‖ContinuousLinearMap.id ℝ E - P‖ + 1)),
      lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have hle1 : min 1 ((δ / 2) / (‖ContinuousLinearMap.id ℝ E - P‖ + 1)) ≤ 1 := min_le_left _ _
    have hdpos : (0:ℝ) < min 1 ((δ / 2) / (‖ContinuousLinearMap.id ℝ E - P‖ + 1)) :=
      lt_min one_pos (by positivity)
    have hle2 := min_le_right (1:ℝ) ((δ / 2) / (‖ContinuousLinearMap.id ℝ E - P‖ + 1))
    rw [le_div_iff₀ hpos] at hle2
    nlinarith [hle2, hdpos, mul_le_of_le_one_right hdpos.le hle1]
  -- E1: the envelope expansion, from the closed gradient lemma, with δ/2
  obtain ⟨ρ₁, hρ₁, hE1⟩ := GradientDiffSecondOrder F (fun z : E => z - u z) hgradF hvc y
    (ContinuousLinearMap.id ℝ E - P) hvd (δ / 2) (by positivity)
  -- the first-order remainder of `u` at `y`
  obtain ⟨ρ₂, hρ₂, hrho⟩ : ∃ ρ > 0, ∀ h : E, ‖h‖ < ρ →
      ‖u (y + h) - u y - P h‖ ≤ d * ‖h‖ := by
    have hlo := (hP.isLittleO).def hd0
    rw [Metric.eventually_nhds_iff] at hlo
    obtain ⟨ε, hε, hball⟩ := hlo
    refine ⟨ε, hε, fun h hh => ?_⟩
    have hmem : dist (y + h) y < ε := by rw [dist_eq_norm]; simpa using hh
    simpa using hball hmem
  refine ⟨min ρ₁ ρ₂, lt_min hρ₁ hρ₂, fun h hh => ?_⟩
  have hh1 : ‖h‖ < ρ₁ := lt_of_lt_of_le hh (min_le_left _ _)
  have hh2 : ‖h‖ < ρ₂ := lt_of_lt_of_le hh (min_le_right _ _)
  obtain ⟨p, hp⟩ : ∃ z : E, z = y - u y := ⟨_, rfl⟩
  obtain ⟨Qh, hQh⟩ : ∃ z : E, z = (ContinuousLinearMap.id ℝ E - P) h := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ z : E, z = u (y + h) - u y - P h := ⟨_, rfl⟩
  have hQhv : Qh = h - P h := by rw [hQh]; simp
  -- the exact identity v(y+h) = p + Qh - ϱ
  have hvid : u (y + h) - (y + h) = -(p + Qh - rr) := by rw [hp, hQhv, hrr]; abel
  have hnv : ‖u (y + h) - (y + h)‖ = ‖p + Qh - rr‖ := by rw [hvid, norm_neg]
  have hnp : ‖u y - y‖ = ‖p‖ := by rw [hp]; exact norm_sub_rev _ _
  have hFyh : F (y + h) = ψ (u (y + h)) + ‖u (y + h) - (y + h)‖ ^ 2 / 2 := by rw [hF]
  have hFy : F y = ψ (u y) + ‖u y - y‖ ^ 2 / 2 := by rw [hF]
  -- expand the square of the three-term sum, without needing bilinearity from `ring`
  have hexp : ‖p + Qh - rr‖ ^ 2
      = ‖p‖ ^ 2 + 2 * (inner ℝ p Qh : ℝ) + ‖Qh‖ ^ 2
        - 2 * ((inner ℝ p rr : ℝ) + (inner ℝ Qh rr : ℝ)) + ‖rr‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real, inner_add_left]
  -- the three cancellation identities, each just `Qh + Ph = h` or `xh - x = Ph + ϱ`
  have hph : (inner ℝ p h : ℝ) = (inner ℝ p Qh : ℝ) + (inner ℝ p (P h) : ℝ) := by
    have e1 : (inner ℝ p (Qh + P h) : ℝ) = (inner ℝ p Qh : ℝ) + (inner ℝ p (P h) : ℝ) :=
      inner_add_right _ _ _
    rw [← e1]; congr 1; rw [hQhv]; abel
  have hQhh : (inner ℝ Qh h : ℝ) = ‖Qh‖ ^ 2 + (inner ℝ Qh (P h) : ℝ) := by
    have e1 : (inner ℝ Qh (Qh + P h) : ℝ) = ‖Qh‖ ^ 2 + (inner ℝ Qh (P h) : ℝ) := by
      rw [inner_add_right, real_inner_self_eq_norm_sq]
    rw [← e1]; congr 1; rw [hQhv]; abel
  have hpxh : (inner ℝ p (u (y + h) - u y) : ℝ)
      = (inner ℝ p (P h) : ℝ) + (inner ℝ p rr : ℝ) := by
    have e1 : (inner ℝ p (P h + rr) : ℝ) = (inner ℝ p (P h) : ℝ) + (inner ℝ p rr : ℝ) :=
      inner_add_right _ _ _
    rw [← e1]; congr 1; rw [hrr]; abel
  -- TARGET = E1 + E2, exactly
  have htgt : ψ (u (y + h)) - ψ (u y) - (inner ℝ p (u (y + h) - u y) : ℝ)
        - (inner ℝ Qh (P h) : ℝ) / 2
      = (F (y + h) - F y - (inner ℝ p h : ℝ) - (inner ℝ Qh h : ℝ) / 2)
        + ((inner ℝ Qh rr : ℝ) - ‖rr‖ ^ 2 / 2) := by
    rw [hFyh, hFy, hnp, hnv, hexp, hph, hQhh, hpxh]; ring
  -- bound the two errors
  have hE1b := hE1 h hh1
  have hQhb : ‖Qh‖ ≤ ‖ContinuousLinearMap.id ℝ E - P‖ * ‖h‖ := by
    rw [hQh]; exact ContinuousLinearMap.le_opNorm _ _
  have hrrb : ‖rr‖ ≤ d * ‖h‖ := by rw [hrr]; exact hrho h hh2
  have hnn : (0:ℝ) ≤ ‖h‖ := norm_nonneg h
  have hE2b : |(inner ℝ Qh rr : ℝ) - ‖rr‖ ^ 2 / 2| ≤ δ / 2 * ‖h‖ ^ 2 := by
    have h1 : |(inner ℝ Qh rr : ℝ)|
        ≤ ‖ContinuousLinearMap.id ℝ E - P‖ * d * ‖h‖ ^ 2 := by
      refine le_trans (abs_real_inner_le_norm Qh rr) ?_
      nlinarith [mul_le_mul hQhb hrrb (norm_nonneg rr) (by positivity :
        (0:ℝ) ≤ ‖ContinuousLinearMap.id ℝ E - P‖ * ‖h‖)]
    have h2 : ‖rr‖ ^ 2 / 2 ≤ d ^ 2 / 2 * ‖h‖ ^ 2 := by
      nlinarith [mul_self_le_mul_self (norm_nonneg rr) hrrb]
    have h3 : (0:ℝ) ≤ ‖rr‖ ^ 2 / 2 := by positivity
    have h5 : (0:ℝ) ≤ d ^ 2 / 2 * ‖h‖ ^ 2 := by positivity
    have hkey : ‖ContinuousLinearMap.id ℝ E - P‖ * d * ‖h‖ ^ 2 + d ^ 2 / 2 * ‖h‖ ^ 2
        ≤ δ / 2 * ‖h‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hdb (sq_nonneg ‖h‖)]
    have hab := abs_le.mp h1
    rw [abs_le]
    refine ⟨?_, ?_⟩
    · linarith only [hab.1, h2, h3, h5, hkey]
    · linarith only [hab.2, h2, h3, h5, hkey]
  -- combine: substitute the abbreviations away so the goal matches syntactically
  -- (rewriting the goal backwards through them is what times out `whnf`)
  subst hp
  subst hQh
  rw [htgt]
  refine le_trans (abs_add_le _ _) ?_
  linarith only [hE1b, hE2b]
