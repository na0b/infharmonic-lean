module

public import InfHarmonic.RescaledEquation
public import InfHarmonic.LinearLift
public import InfHarmonic.RescaledLimitStability
public import InfHarmonic.LimitSolutionLocalToGlobal
public import InfHarmonic.NormalizedInfFamily

@[expose] public section
set_option maxHeartbeats 500000
open Metric Set Filter Topology WithLp

/-- Step 10 of paper Proposition 3.6 (`NonaffineLimit`): the locally uniform
limit of the normalized solutions solves the limiting equation on all of
space-time.

Work in `X = ℓ²(ℝ^d × ℝ)`. The data are a normalized inf-family `U_i`, centers
`z_i ∈ B_{3/4}`, radii `r_i > 0` with `r_i → 0`, degenerating parameters
`λ_i > 0` with `λ_i → 0` and `λ_i ≤ 1` past an index `i₂`, slopes `c_i > 0`
past `i₁`, linear isometries `Φ_i`, and the normalized solutions `v_i`
determined by the increment identity
`U_i(z_i + r_i Φ_i(√λ_i x, t)) = U_i(z_i) + r_i c_i (t + λ_i v_i(x,t))`.
Along the subsequence `ψ` of Step 9 the `v_{ψ j}` converge locally uniformly to
a continuous `v_∞`; `ψ` and its four properties are taken as hypotheses and
their source is \noderef{AsymptEquicontOriginNormalizedLimit}, which is not
re-narrated here.

The conclusion is `IsLimitSolutionOn` on the whole space for `v_∞`. The proof
has the three stages the paper's eq:nl-domains discussion describes. First, for
`i ≥ i₁` the function `v_i` solves the rescaled equation on the preimage under
`w ↦ z_i + r_i Φ_i(√λ_i x, t)` of the lifted unit ball: the normalized family
supplies `u_i` with `U_i(y,b) = u_i(y) + b`, \noderef{LinearLift} makes that sum
infinity-harmonic on the lifted ball, and \noderef{RescaledEquation} converts
the increment identity into the equation. Second, each bounded ball
`B_{k+1}` sits inside every late member's normalized domain --- that is where
`r_i → 0` is used, through the displacement bound
`‖r_i Φ_i(√λ_i x,t)‖ ≤ 2 r_i ‖w‖ < 1/4` --- so after shifting the index by a
tail `m_k` the hypotheses of \noderef{RescaledLimitStability} hold on that ball
and give `IsLimitSolutionOn B_{k+1} v_∞`. Third, the balls `B_{k+1}`,
`k ∈ ℕ`, cover the space by the Archimedean property, and
\noderef{LimitSolutionLocalToGlobal} glues the per-ball statements. The gluing
is genuinely needed: the stability node's hypothesis is universally quantified
over the index, while the normalized domains only exhaust the space. -/
theorem NonaffineLimitIsLimitSolution (d : ℕ) (r lam cc : ℕ → ℝ)
    (U : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (z : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (Φ : ℕ → (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)
                ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
    (v : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (i₁ i₂ : ℕ) (psi : ℕ → ℕ)
    (vlim : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hr0 : ∀ i, 0 < r i) (hrlim : Tendsto r atTop (𝓝 0))
    (hlam0 : ∀ i, 0 < lam i) (hlamlim : Tendsto lam atTop (𝓝 0))
    (hlamle1 : ∀ i ≥ i₂, lam i ≤ 1)
    (hzG : ∀ i, z i ∈ ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (3 / 4))
    (hUnorm : ∀ i, NormalizedInfFamily d (U i))
    (hcc0 : ∀ i ≥ i₁, 0 < cc i)
    (hveq : ∀ i ≥ i₁, ∀ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      U i (z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))
        = U i (z i) + r i * cc i * ((ofLp w).2 + lam i * v i w))
    (hpsimono : StrictMono psi) (hpsige : ∀ j, i₁ ≤ psi j)
    (hvcont : Continuous vlim)
    (hvconv : ∀ K : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), IsCompact K →
      TendstoUniformlyOn (fun j => v (psi j)) vlim atTop K) :
    IsLimitSolutionOn (Set.univ : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
      vlim := by
  -- the `L²` norm of a space-time point dominates each of its two coordinates
  have hballbox : ∀ (rho : ℝ) (y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
      y ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) rho →
      ‖(ofLp y).1‖ ≤ rho ∧ |(ofLp y).2| ≤ rho := by
    intro rho y hy
    rw [mem_closedBall, dist_zero_right] at hy
    have hsq := WithLp.prod_norm_sq_eq_of_L2 y
    have h1 : ‖y.fst‖ = ‖(ofLp y).1‖ := rfl
    have h2 : ‖y.snd‖ = |(ofLp y).2| := rfl
    rw [h1, h2] at hsq
    have hn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    exact ⟨by nlinarith only [hsq, hy, hn, norm_nonneg (ofLp y).1, abs_nonneg (ofLp y).2],
      by nlinarith only [hsq, hy, hn, norm_nonneg (ofLp y).1, abs_nonneg (ofLp y).2]⟩
  -- eq:nl-domains in the form Step 10 needs: for `i ≥ i₁` the function `v i` solves the
  -- rescaled equation on the PREIMAGE of the lifted unit ball.  `NormalizedInfFamily`
  -- supplies `u_i` and the identity `U_i(y,b) = u_i y + b`, which is exactly
  -- `LinearLift`'s lifted function; `RescaledEquation`'s increment slot is the
  -- hypothesis `hveq`, i.e. the normalization identity written at the slope `cc i`.
  have hresc : ∀ i ≥ i₁, IsRescaledSolutionOn (lam i)
      ((fun w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) =>
        z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2))) ⁻¹'
        ((fun y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp y).1) ⁻¹'
          ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (v i) := by
    intro i hi
    obtain ⟨u, hu, -, -, -, -, hUeq⟩ := hUnorm i
    have hUfun : (fun w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) =>
        u (ofLp w).1 + (ofLp w).2) = U i := by
      funext w; exact (hUeq w).symm
    have hUinf : IsInfHarmonicOn
        ((fun y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp y).1) ⁻¹'
          ball (0 : EuclideanSpace ℝ (Fin d)) 1) (U i) := by
      rw [← hUfun]
      exact LinearLift (ball (0 : EuclideanSpace ℝ (Fin d)) 1) u hu
    refine RescaledEquation _ (U i) hUinf (z i) (r i) (cc i) (lam i)
      (hr0 i) (hcc0 i hi) (hlam0 i) (Φ i) (v i) ?_
    intro w
    exact hveq i hi w
  -- restriction of a rescaled solution to an open subset.  The direction is the one that
  -- needs `Ω'` OPEN: a local extremum relative to an open `Ω'` containing the point is a
  -- local extremum outright, because `𝓝[Ω'] z = 𝓝 z`, and hence one relative to any
  -- larger set.
  have hrestr : ∀ (lm : ℝ) (Ω Ω' : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
      (g : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ),
      IsOpen Ω' → Ω' ⊆ Ω → IsRescaledSolutionOn lm Ω g →
      IsRescaledSolutionOn lm Ω' g := by
    intro lm Ω Ω' g hop hsb hsol
    obtain ⟨-, hc, hsub, hsup⟩ := hsol
    refine ⟨hop, hc.mono hsb, ?_, ?_⟩
    · intro zz hzz φ hφ hmax
      refine hsub zz (hsb hzz) φ hφ (hmax.filter_mono ?_)
      rw [hop.nhdsWithin_eq hzz]
      exact nhdsWithin_le_nhds
    · intro zz hzz φ hφ hmin
      refine hsup zz (hsb hzz) φ hφ (hmin.filter_mono ?_)
      rw [hop.nhdsWithin_eq hzz]
      exact nhdsWithin_le_nhds
  have hballsol : ∀ k : ℕ,
      IsLimitSolutionOn (ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) ((k : ℝ) + 1))
        vlim := by
    intro k
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    -- THE TAIL INDEX.  `r i * 2(k+1) < 1/4` past `m`, and `32 λ_i ≤ 1` past `i₂`.
    obtain ⟨m, hm⟩ := Filter.eventually_atTop.mp
      (hrlim.eventually_lt_const (show (0 : ℝ) < 1 / (8 * ((k : ℝ) + 1)) by positivity))
    obtain ⟨m2, hm2def⟩ : ∃ m2 : ℕ, m2 = max (max m i₂) i₁ := ⟨_, rfl⟩
    have hm2m : m ≤ m2 := by
      rw [hm2def]; exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hm2i2 : i₂ ≤ m2 := by
      rw [hm2def]; exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hm2i1 : i₁ ≤ m2 := by rw [hm2def]; exact le_max_right _ _
    -- every point of the ball maps into the lifted unit ball, for `i ≥ m2`
    have hsub : ∀ i ≥ m2,
        ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) ((k : ℝ) + 1) ⊆
        ((fun w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) =>
          z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2))) ⁻¹'
          ((fun y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp y).1) ⁻¹'
            ball (0 : EuclideanSpace ℝ (Fin d)) 1)) := by
      intro i hi w hw
      have hi2 : i₂ ≤ i := le_trans hm2i2 hi
      have hri : r i < 1 / (8 * ((k : ℝ) + 1)) := hm i (le_trans hm2m hi)
      have hr := hr0 i
      have hlam1 : lam i ≤ 1 := hlamle1 i hi2
      have hsl1 : Real.sqrt (lam i) ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
        exact Real.sqrt_le_sqrt hlam1
      have hsl0 : (0 : ℝ) ≤ Real.sqrt (lam i) := Real.sqrt_nonneg _
      rw [mem_ball, dist_zero_right] at hw
      obtain ⟨hwx, hwt⟩ := hballbox ‖w‖ w (by rw [mem_closedBall, dist_zero_right])
      -- `‖(√λ x, t)‖ ≤ ‖x‖ + |t| ≤ 2‖w‖`
      have hnu : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ ≤ 2 * ‖w‖ := by
        have hsq := WithLp.prod_norm_sq_eq_of_L2
          (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        have he1 : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).fst‖
            = Real.sqrt (lam i) * ‖(ofLp w).1‖ := by
          show ‖Real.sqrt (lam i) • (ofLp w).1‖ = _
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsl0]
        have he2 : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).snd‖ = |(ofLp w).2| := rfl
        rw [he1, he2] at hsq
        have hb1 : Real.sqrt (lam i) * ‖(ofLp w).1‖ ≤ ‖w‖ := by
          nlinarith only [hsl1, hsl0, hwx, norm_nonneg (ofLp w).1]
        have hb1n : (0 : ℝ) ≤ Real.sqrt (lam i) * ‖(ofLp w).1‖ :=
          mul_nonneg hsl0 (norm_nonneg _)
        have hsq2 : ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ ^ 2 ≤ (2 * ‖w‖) ^ 2 := by
          nlinarith only [hsq, hb1, hb1n, hwt, abs_nonneg (ofLp w).2, norm_nonneg w]
        exact le_of_pow_le_pow_left₀ (by norm_num)
          (by positivity : (0 : ℝ) ≤ 2 * ‖w‖) hsq2
      -- so the displacement is shorter than `1/4`
      have hdisp : ‖r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2))‖
          < 1 / 4 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, LinearIsometryEquiv.norm_map]
        have h1 : r i * ‖(toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)
            : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))‖ ≤ r i * (2 * ‖w‖) :=
          mul_le_mul_of_nonneg_left hnu (le_of_lt hr)
        have h2 : r i * (2 * ‖w‖) < r i * (2 * ((k : ℝ) + 1)) := by
          nlinarith only [hw, hr]
        have h3 : r i * (2 * ((k : ℝ) + 1)) < 1 / 4 := by
          have h4 : r i * (8 * ((k : ℝ) + 1)) < 1 := by
            have h5 : (0 : ℝ) < 8 * ((k : ℝ) + 1) := by positivity
            rw [← lt_div_iff₀ h5]
            exact hri
          nlinarith only [h4, hr, hk1]
        linarith only [h1, h2, h3]
      -- hence it lands in the lifted unit ball
      have hzi : ‖z i‖ < 3 / 4 := by
        have h := hzG i
        rwa [mem_ball, dist_zero_right] at h
      have htot : ‖z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1,
          (ofLp w).2))‖ < 1 := by
        have h := norm_add_le (z i)
          (r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))
        linarith only [h, hzi, hdisp]
      obtain ⟨hpx, -⟩ := hballbox ‖z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1,
        (ofLp w).2))‖ _ (by rw [mem_closedBall, dist_zero_right])
      show (ofLp (z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))).1
        ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
      rw [mem_ball, dist_zero_right]
      linarith only [hpx, htot]
    -- the shifted tail, and viscosity stability at the degenerating parameter
    have hidx : ∀ j : ℕ, m2 ≤ psi (j + m2) := fun j =>
      le_trans (Nat.le_add_left m2 j) (hpsimono.le_apply (x := j + m2))
    refine RescaledLimitStability _ isOpen_ball (fun j => lam (psi (j + m2))) ?_
      (fun j => v (psi (j + m2))) vlim ?_ ?_
    · refine hlamlim.comp (tendsto_atTop_mono (fun j => ?_) tendsto_id)
      exact le_trans (Nat.le_add_right j m2) (hpsimono.le_apply (x := j + m2))
    · intro j
      exact hrestr (lam (psi (j + m2))) _ _ (v (psi (j + m2))) isOpen_ball
        (hsub (psi (j + m2)) (hidx j)) (hresc (psi (j + m2)) (hpsige (j + m2)))
    · intro C hCsub hC
      exact fun uu huu => (tendsto_add_atTop_nat m2).eventually (hvconv C hC uu huu)
  have hlimsol : IsLimitSolutionOn (Set.univ : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
      vlim := by
    refine LimitSolutionLocalToGlobal Set.univ
      (fun k : ℕ => ball (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) ((k : ℝ) + 1))
      vlim isOpen_univ (fun k => Set.subset_univ _) ?_ hvcont.continuousOn hballsol
    intro zz _
    obtain ⟨k, hk⟩ := exists_nat_gt ‖zz‖
    exact ⟨k, by rw [mem_ball, dist_zero_right]; linarith only [hk]⟩
  exact hlimsol
