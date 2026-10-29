module

public import InfHarmonic.AffineBlowups
public import InfHarmonic.NormalizedFamilyLipschitz
public import InfHarmonic.EquiLipschitzUniformLimit

@[expose] public section
set_option maxHeartbeats 1000000
open Set Metric

/-- Steps 4, 5 and 7 of paper Lemma 3.2 (`FamilyFlatness`): three chained
subsequence extractions along the convergent subsequence of normalized family
members.

Given a normalized inf-family `(U_i)` with a common bound and Lipschitz
constant `L` on the closed `7/8`-ball, centers `z_i` in the open `3/4`-ball and
radii `r_i -> 0`, together with a subsequence `ι` along which the centers
converge to `z_*` and the members converge uniformly on the closed `7/8`-ball to
an infinity-harmonic limit `U_∘`, one further subsequence `j` can be chosen
which simultaneously achieves three things.

*Step 4, the slow scales.* A sequence `R_k` of radii with `0 < R_k <= 1/16` for
which `(|z_{ι(j k)} - z_*| + r_{ι(j k)}) / R_k -> 0`: the scales `R_k` decay so
slowly that the centers and the radii are negligible against them. The upper
bound `1/16` is what keeps `z_* + R_k X` inside the closed `7/8`-ball.

*Step 5, the blow-up slope.* A vector `P_0` such that the normalized difference
quotients `(U_{ι(j k)}(z_* + R_k X) - U_{ι(j k)}(z_*)) / R_k` converge to the
linear function `<P_0, X>` uniformly on the open unit ball, in the asymptotic
`for every ε' > 0 there is k_0` form. This comes from the asymptotic linearity
of blow-ups of the infinity-harmonic limit at `z_*` together with the Riesz
representation of the resulting continuous linear functional.

*Step 7, the rescaled limit.* A function `W` on the closed `2`-ball which is the
uniform limit of the rescalings
`(U_{ι(j k)}(z_{ι(j k)} + r_{ι(j k)} H) - U_{ι(j k)}(z_{ι(j k)})) / r_{ι(j k)}`,
is continuous there, and is normalized by `W 0 = 0` and `W e_b = 1`, where
`e_b = (0,1)` is the unit time direction. The two normalizations come from the
rescaling itself and from the fact that every member of a normalized inf-family
is the sum of a space-only function and the time coordinate.

The three extractions are chained, each taken from the output of the previous
one, and only the composed index `j` is returned; the intermediate
subsequences do not appear in the conclusion. -/
theorem SlowScalesAndBlowupLimit (d : ℕ)
    (eb : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (hebdef : eb = WithLp.toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)))
    (L : ℝ) (hL0 : 0 ≤ L)
    (hLb : ∀ U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ, NormalizedInfFamily d U →
      (∀ z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8), |U z| ≤ L) ∧
      (∀ a ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
        ∀ b ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
          |U a - U b| ≤ L * ‖a - b‖))
    (Uq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (zq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (rq : ℕ → ℝ)
    (hUq : ∀ i, NormalizedInfFamily d (Uq i))
    (hzq : ∀ i, zq i ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))
    (hrq0 : ∀ i, 0 < rq i)
    (hrqlim : Filter.Tendsto rq Filter.atTop (nhds 0))
    (ι : ℕ → ℕ) (hι : StrictMono ι)
    (zstar : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (Ucirc : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hzstar : ‖zstar‖ ≤ 3 / 4)
    (hzconv : Filter.Tendsto (fun k => zq (ι k)) Filter.atTop (nhds zstar))
    (hUunif : TendstoUniformlyOn (fun k => Uq (ι k)) Ucirc Filter.atTop
      (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)))
    (hUharm : IsInfHarmonicOn
      (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) Ucirc)
    (hinside : ∀ Rv : ℝ, 0 < Rv → Rv ≤ 1 / 16 →
      ∀ X : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖X‖ ≤ 1 →
        zstar + Rv • X ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) :
    ∃ (j : ℕ → ℕ) (Rs : ℕ → ℝ)
      (Wlim : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
      (P0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
      StrictMono j ∧
      (∀ k, 0 < Rs k) ∧
      (∀ k, Rs k ≤ 1 / 16) ∧
      Filter.Tendsto
        (fun k => (‖zq (ι (j k)) - zstar‖ + rq (ι (j k))) / Rs k)
        Filter.atTop (nhds 0) ∧
      (∀ ε' > 0, ∃ k₀ : ℕ, ∀ k ≥ k₀,
        ∀ X ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1,
          |(Uq (ι (j k)) (zstar + Rs k • X) - Uq (ι (j k)) zstar) / Rs k
            - (inner ℝ P0 X : ℝ)| ≤ ε') ∧
      TendstoUniformlyOn
        (fun k H => (Uq (ι (j k)) (zq (ι (j k)) + rq (ι (j k)) • H)
          - Uq (ι (j k)) (zq (ι (j k)))) / rq (ι (j k))) Wlim Filter.atTop
        (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2) ∧
      ContinuousOn Wlim
        (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2) ∧
      Wlim 0 = 0 ∧ Wlim eb = 1 := by
  -- ---------- STEP 4: the slow scales ----------
  obtain ⟨Rs₀, hRs₀def⟩ : ∃ Rs₀ : ℕ → ℝ,
      Rs₀ = fun n : ℕ => 1 / 16 * (1 / ((n : ℝ) + 1)) := ⟨_, rfl⟩
  have hRs₀0 : ∀ n, 0 < Rs₀ n := by
    intro n; rw [hRs₀def]; positivity
  have hRs₀16 : ∀ n, Rs₀ n ≤ 1 / 16 := by
    intro n
    rw [hRs₀def]
    show 1 / 16 * (1 / ((n : ℝ) + 1)) ≤ 1 / 16
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith only [this]
    nlinarith only [h1]
  have hRs₀lim : Filter.Tendsto Rs₀ Filter.atTop (nhds 0) := by
    rw [hRs₀def]
    have h := Filter.Tendsto.const_mul (1 / 16 : ℝ) tendsto_one_div_add_atTop_nhds_zero_nat
    rw [mul_zero] at h
    exact h
  -- the three sequences that must be small relative to `Rs₀`, each eventually so
  have hrqι : Filter.Tendsto (fun k => rq (ι k)) Filter.atTop (nhds 0) :=
    hrqlim.comp hι.tendsto_atTop
  have hzn : Filter.Tendsto (fun k => ‖zq (ι k) - zstar‖) Filter.atTop (nhds 0) := by
    have h := (hzconv.sub_const zstar).norm
    rw [sub_self, norm_zero] at h
    exact h
  have hext : ∀ n : ℕ, ∀ᶠ k in Filter.atTop,
      (∀ w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
          |Uq (ι k) w - Ucirc w| ≤ Rs₀ n / ((n : ℝ) + 1)) ∧
      ‖zq (ι k) - zstar‖ + rq (ι k) ≤ Rs₀ n / ((n : ℝ) + 1) ∧
      rq (ι k) ≤ 1 / 16 := by
    intro n
    have han : 0 < Rs₀ n / ((n : ℝ) + 1) := by
      have := hRs₀0 n
      positivity
    have e1 : ∀ᶠ k in Filter.atTop,
        ∀ w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8),
          |Uq (ι k) w - Ucirc w| ≤ Rs₀ n / ((n : ℝ) + 1) := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hUunif _ han] with k hk w hw
      have h := hk w hw
      rw [Real.dist_eq] at h
      rw [abs_sub_comm]
      exact le_of_lt h
    have e2 : ∀ᶠ k in Filter.atTop,
        ‖zq (ι k) - zstar‖ + rq (ι k) ≤ Rs₀ n / ((n : ℝ) + 1) := by
      have hsum : Filter.Tendsto (fun k => ‖zq (ι k) - zstar‖ + rq (ι k))
          Filter.atTop (nhds 0) := by
        have h := hzn.add hrqι
        rw [add_zero] at h
        exact h
      filter_upwards [hsum.eventually_lt_const han] with k hk
      exact le_of_lt hk
    have e3 : ∀ᶠ k in Filter.atTop, rq (ι k) ≤ 1 / 16 := by
      filter_upwards [hrqι.eventually_lt_const (by norm_num : (0:ℝ) < 1 / 16)] with k hk
      exact le_of_lt hk
    exact e1.and (e2.and e3)
  obtain ⟨j₀, hj₀, hj₀P⟩ := Filter.extraction_forall_of_eventually hext
  -- ---------- STEP 5: the blow-up of the single limit `Ucirc` at `zstar` ----------
  have hzsmem : zstar ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
    rw [mem_ball, dist_zero_right]
    linarith only [hzstar]
  obtain ⟨hAB1, hAB2⟩ :=
    AffineBlowups (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8)) Ucirc hUharm
      zstar hzsmem
  obtain ⟨ι₅, V, hι₅, hVconv⟩ := hAB2 Rs₀ hRs₀0 hRs₀lim
  obtain ⟨Lin, hLin⟩ := hAB1 (fun i => Rs₀ (ι₅ i)) V (fun i => hRs₀0 _)
    (hRs₀lim.comp hι₅.tendsto_atTop) hVconv
  obtain ⟨P0, hP0def⟩ : ∃ P0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      P0 = (InnerProductSpace.toDual ℝ (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))).symm Lin :=
    ⟨_, rfl⟩
  have hP0 : ∀ X : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      (inner ℝ P0 X : ℝ) = Lin X := by
    intro X
    rw [hP0def]
    exact InnerProductSpace.toDual_symm_apply
  -- ---------- STEP 7: the blow-ups at the moving centers `z_i` ----------
  obtain ⟨Wseq, hWseqdef⟩ : ∃ Wseq : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      Wseq = fun n H => (Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H)
        - Uq (ι (j₀ n)) (zq (ι (j₀ n)))) / rq (ι (j₀ n)) := ⟨_, rfl⟩
  have hrqsmall : ∀ n, rq (ι (j₀ n)) ≤ 1 / 16 := fun n => (hj₀P n).2.2
  have hzqc : ∀ n, zq (ι (j₀ n)) ∈ closedBall
      (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
    intro n
    have h := hzq (ι (j₀ n))
    rw [mem_ball, dist_zero_right] at h
    rw [mem_closedBall, dist_zero_right]
    linarith only [h]
  have hmvmem : ∀ (n : ℕ) (H : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), ‖H‖ ≤ 2 →
      zq (ι (j₀ n)) + rq (ι (j₀ n)) • H
        ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
    intro n H hH
    have hz := hzq (ι (j₀ n))
    rw [mem_ball, dist_zero_right] at hz
    have hr0 := hrq0 (ι (j₀ n))
    have hr16 := hrqsmall n
    rw [mem_closedBall, dist_zero_right]
    have h1 : ‖zq (ι (j₀ n)) + rq (ι (j₀ n)) • H‖
        ≤ ‖zq (ι (j₀ n))‖ + ‖rq (ι (j₀ n)) • H‖ := norm_add_le _ _
    have h2 : ‖rq (ι (j₀ n)) • H‖ = rq (ι (j₀ n)) * ‖H‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr0)]
    have h3 : rq (ι (j₀ n)) * ‖H‖ ≤ rq (ι (j₀ n)) * 2 :=
      mul_le_mul_of_nonneg_left hH (le_of_lt hr0)
    rw [h2] at h1
    linarith only [h1, h3, hz, hr16]
  -- the two estimates of eq:ff-lip, transported to the blow-ups
  have hWbd : ∀ n : ℕ, ∀ H ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
      |Wseq n H| ≤ 2 * L := by
    intro n H hH
    rw [mem_closedBall, dist_zero_right] at hH
    have hr0 := hrq0 (ι (j₀ n))
    have hlip := (hLb (Uq (ι (j₀ n))) (hUq (ι (j₀ n)))).2
      (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H) (hmvmem n H hH) (zq (ι (j₀ n))) (hzqc n)
    have hdn : ‖zq (ι (j₀ n)) + rq (ι (j₀ n)) • H - zq (ι (j₀ n))‖
        = rq (ι (j₀ n)) * ‖H‖ := by
      rw [show zq (ι (j₀ n)) + rq (ι (j₀ n)) • H - zq (ι (j₀ n))
        = rq (ι (j₀ n)) • H from by abel, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt hr0)]
    rw [hdn] at hlip
    rw [hWseqdef]
    show |(Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H)
      - Uq (ι (j₀ n)) (zq (ι (j₀ n)))) / rq (ι (j₀ n))| ≤ 2 * L
    rw [abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    have h4 : L * (rq (ι (j₀ n)) * ‖H‖) ≤ L * (rq (ι (j₀ n)) * 2) := by
      have := mul_le_mul_of_nonneg_left hH (le_of_lt hr0)
      exact mul_le_mul_of_nonneg_left this hL0
    linarith only [hlip, h4]
  have hWlip : ∀ n : ℕ, ∀ H ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
      ∀ H' ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2,
      |Wseq n H - Wseq n H'| ≤ L * ‖H - H'‖ := by
    intro n H hH H' hH'
    rw [mem_closedBall, dist_zero_right] at hH hH'
    have hr0 := hrq0 (ι (j₀ n))
    have hlip := (hLb (Uq (ι (j₀ n))) (hUq (ι (j₀ n)))).2
      (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H) (hmvmem n H hH)
      (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H') (hmvmem n H' hH')
    have hdn : ‖zq (ι (j₀ n)) + rq (ι (j₀ n)) • H
          - (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H')‖
        = rq (ι (j₀ n)) * ‖H - H'‖ := by
      rw [show zq (ι (j₀ n)) + rq (ι (j₀ n)) • H - (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H')
        = rq (ι (j₀ n)) • (H - H') from by rw [smul_sub]; abel, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg (le_of_lt hr0)]
    rw [hdn] at hlip
    rw [hWseqdef]
    show |(Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H)
        - Uq (ι (j₀ n)) (zq (ι (j₀ n)))) / rq (ι (j₀ n))
      - (Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H')
        - Uq (ι (j₀ n)) (zq (ι (j₀ n)))) / rq (ι (j₀ n))| ≤ L * ‖H - H'‖
    rw [div_sub_div_same, show Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H)
        - Uq (ι (j₀ n)) (zq (ι (j₀ n)))
        - (Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H')
          - Uq (ι (j₀ n)) (zq (ι (j₀ n))))
        = Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H)
          - Uq (ι (j₀ n)) (zq (ι (j₀ n)) + rq (ι (j₀ n)) • H') from by ring,
      abs_div, abs_of_pos hr0, div_le_iff₀ hr0]
    linarith only [hlip]
  obtain ⟨ι₇, Wlim, hι₇, hWconv₇⟩ :=
    EquiLipschitzUniformLimit (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 (2 * L) L
      (by norm_num) (fun k => Wseq (ι₅ k)) (fun k => hWbd (ι₅ k)) (fun k => hWlip (ι₅ k))
  -- ---------- ASSEMBLY ----------
  refine ⟨fun k => j₀ (ι₅ (ι₇ k)), fun k => Rs₀ (ι₅ (ι₇ k)), Wlim, P0,
    hj₀.comp (hι₅.comp hι₇), fun k => hRs₀0 _, fun k => hRs₀16 _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- eq:ff-slow
  · have hg : Filter.Tendsto
        (fun n => (‖zq (ι (j₀ n)) - zstar‖ + rq (ι (j₀ n))) / Rs₀ n)
        Filter.atTop (nhds 0) := by
      refine squeeze_zero (fun n => ?_) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      · exact div_nonneg (add_nonneg (norm_nonneg _) (le_of_lt (hrq0 _)))
          (le_of_lt (hRs₀0 n))
      · rw [div_le_iff₀ (hRs₀0 n)]
        calc ‖zq (ι (j₀ n)) - zstar‖ + rq (ι (j₀ n)) ≤ Rs₀ n / ((n : ℝ) + 1) :=
              (hj₀P n).2.1
          _ = 1 / ((n : ℝ) + 1) * Rs₀ n := by ring
    exact hg.comp (hι₅.comp hι₇).tendsto_atTop
  -- eq:ff-hatconv
  · intro ε' hε'
    -- the `Ucirc` blow-ups converge uniformly on the closed unit ball
    obtain ⟨i₀, hi₀⟩ := Filter.eventually_atTop.mp
      (Metric.tendstoUniformlyOn_iff.mp
        (hVconv (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1)
          (isCompact_closedBall _ _)) (ε' / 2) (by linarith only [hε']))
    -- an index past which `2/(n+1) ≤ ε'/2`
    obtain ⟨k₁, hk₁⟩ := exists_nat_gt (4 / ε')
    refine ⟨max i₀ k₁, fun k hk X hX => ?_⟩
    have hki : i₀ ≤ k := le_trans (le_max_left _ _) hk
    have hkk : k₁ ≤ k := le_trans (le_max_right _ _) hk
    have hle₇ : k ≤ ι₇ k := hι₇.le_apply
    have hle₅ : ι₇ k ≤ ι₅ (ι₇ k) := hι₅.le_apply
    have hnk : k ≤ ι₅ (ι₇ k) := le_trans hle₇ hle₅
    set n := ι₅ (ι₇ k) with hndef
    have hXle : ‖X‖ ≤ 1 := by
      rw [mem_ball, dist_zero_right] at hX
      exact le_of_lt hX
    have hR0 := hRs₀0 n
    have hAmem := hinside (Rs₀ n) hR0 (hRs₀16 n) X hXle
    have hBmem : zstar ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7 / 8) := by
      rw [mem_closedBall, dist_zero_right]
      linarith only [hzstar]
    have hgapA := (hj₀P n).1 (zstar + Rs₀ n • X) hAmem
    have hgapB := (hj₀P n).1 zstar hBmem
    -- eq:ff-slow in its qualitative form: the `U_i` blow-ups and the `Ucirc` blow-ups at
    -- the SAME scale differ by `2 η_i / R_i ≤ 2/(n+1)`
    have hgap : |(Uq (ι (j₀ n)) (zstar + Rs₀ n • X) - Uq (ι (j₀ n)) zstar) / Rs₀ n
        - (Ucirc (zstar + Rs₀ n • X) - Ucirc zstar) / Rs₀ n| ≤ 2 / ((n : ℝ) + 1) := by
      rw [div_sub_div_same,
        show Uq (ι (j₀ n)) (zstar + Rs₀ n • X) - Uq (ι (j₀ n)) zstar
            - (Ucirc (zstar + Rs₀ n • X) - Ucirc zstar)
          = Uq (ι (j₀ n)) (zstar + Rs₀ n • X) - Ucirc (zstar + Rs₀ n • X)
            - (Uq (ι (j₀ n)) zstar - Ucirc zstar) from by ring,
        abs_div, abs_of_pos hR0, div_le_iff₀ hR0]
      have h3 := abs_le.mp hgapA
      have h4 := abs_le.mp hgapB
      have hid : 2 / ((n : ℝ) + 1) * Rs₀ n = 2 * (Rs₀ n / ((n : ℝ) + 1)) := by ring
      rw [abs_le, hid]
      constructor <;> linarith only [h3.1, h3.2, h4.1, h4.2]
    -- the `Ucirc` part: the blow-up limit is the Riesz representative of `P0`
    have hVpart : |(Ucirc (zstar + Rs₀ n • X) - Ucirc zstar) / Rs₀ n
        - (inner ℝ P0 X : ℝ)| ≤ ε' / 2 := by
      have hXmem : X ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 1 := by
        rw [mem_closedBall, dist_zero_right]
        exact hXle
      have h := hi₀ (ι₇ k) (le_trans hki hle₇) X hXmem
      rw [Real.dist_eq] at h
      rw [hP0 X, ← hLin X, abs_sub_comm]
      exact le_of_lt h
    have hfin : 2 / ((n : ℝ) + 1) ≤ ε' / 2 := by
      have hcast : (k₁ : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans hkk hnk
      have h4 : 4 / ε' < (n : ℝ) := lt_of_lt_of_le hk₁ hcast
      rw [div_lt_iff₀ hε'] at h4
      rw [div_le_iff₀ (show (0:ℝ) < (n : ℝ) + 1 by positivity)]
      linarith only [h4, hε']
    calc |(Uq (ι (j₀ n)) (zstar + Rs₀ n • X) - Uq (ι (j₀ n)) zstar) / Rs₀ n
            - (inner ℝ P0 X : ℝ)|
        ≤ |(Uq (ι (j₀ n)) (zstar + Rs₀ n • X) - Uq (ι (j₀ n)) zstar) / Rs₀ n
            - (Ucirc (zstar + Rs₀ n • X) - Ucirc zstar) / Rs₀ n|
          + |(Ucirc (zstar + Rs₀ n • X) - Ucirc zstar) / Rs₀ n
            - (inner ℝ P0 X : ℝ)| := abs_sub_le _ _ _
      _ ≤ 2 / ((n : ℝ) + 1) + ε' / 2 := add_le_add hgap hVpart
      _ ≤ ε' := by linarith only [hfin]
  -- eq:ff-Wconv
  · simp only [hWseqdef] at hWconv₇
    exact hWconv₇
  -- continuity of the limit, from the common Lipschitz bound
  · refine hWconv₇.continuousOn (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun k => ?_))
    refine LipschitzOnWith.continuousOn (K := Real.toNNReal L) ?_
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal L hL0]
    exact hWlip (ι₅ (ι₇ k)) x hx y hy
  -- eq:ff-W0
  · have h0mem : (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := by
      rw [mem_closedBall, dist_self]; norm_num
    have h := hWconv₇.tendsto_at h0mem
    have hzero : ∀ k, Wseq (ι₅ k) (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) = 0 := by
      intro k
      rw [hWseqdef]
      show (Uq (ι (j₀ (ι₅ k))) (zq (ι (j₀ (ι₅ k)))
        + rq (ι (j₀ (ι₅ k))) • (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
          - Uq (ι (j₀ (ι₅ k))) (zq (ι (j₀ (ι₅ k))))) / rq (ι (j₀ (ι₅ k))) = 0
      rw [smul_zero, add_zero, sub_self, zero_div]
    have h' : Filter.Tendsto (fun _ : ℕ => (0:ℝ)) Filter.atTop (nhds (Wlim 0)) := by
      simpa only [hzero] using h
    exact (tendsto_nhds_unique tendsto_const_nhds h').symm
  -- eq:ff-Web
  · have hebn : ‖eb‖ = 1 := by
      rw [hebdef, WithLp.prod_norm_eq_of_L2]
      norm_num
    have hebmem : eb ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) 2 := by
      rw [mem_closedBall, dist_zero_right, hebn]; norm_num
    have h := hWconv₇.tendsto_at hebmem
    have hone : ∀ k, Wseq (ι₅ k) eb = 1 := by
      intro k
      obtain ⟨u, -, -, -, -, -, hUeq⟩ := hUq (ι (j₀ (ι₅ k)))
      have hr0 := hrq0 (ι (j₀ (ι₅ k)))
      rw [hWseqdef]
      show (Uq (ι (j₀ (ι₅ k))) (zq (ι (j₀ (ι₅ k))) + rq (ι (j₀ (ι₅ k))) • eb)
          - Uq (ι (j₀ (ι₅ k))) (zq (ι (j₀ (ι₅ k))))) / rq (ι (j₀ (ι₅ k))) = 1
      rw [hUeq, hUeq, hebdef]
      simp [hr0.ne']
    have h' : Filter.Tendsto (fun _ : ℕ => (1:ℝ)) Filter.atTop (nhds (Wlim eb)) := by
      simpa only [hone] using h
    exact (tendsto_nhds_unique tendsto_const_nhds h').symm
