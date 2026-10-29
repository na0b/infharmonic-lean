module

public import InfHarmonic.FrameConfigCovariance
public import InfHarmonic.EnvelopeCompetitorBounds
public import InfHarmonic.JensenSupremumFinite
public import InfHarmonic.FrameInvariance
public import InfHarmonic.ClassCompactness
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.BaryEnvSandwich
public import InfHarmonic.ContactEnv
public import InfHarmonic.ContactEnvelopeProperties
public import InfHarmonic.ContactEnvelopeSlopeLimit

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Proposition 5.4, the extremal envelope contact: if `A_{m,C₀}` has a
nonaffine member then there are `κ ∈ (0,∞)` and a member `v` centered at
`z_* = (0,1)` with the horizontal Jensen bound of constant `κ` at every time,
for which the contact envelope `W = C_t v - κ²t/2` is continuous, has
subquadratic spatial growth on compact positive-time intervals, is a subsolution
of the limiting equation on positive times, is sandwiched between `v - κ²t/2`
and `v` with contact at `z_*`, is spatially semiconcave, has barycentric gap
exactly `κ²t/2` at every contact, and whose forward envelope slopes at `z_*`
tend to the finite envelope Hamiltonian `H_v(z_*)`. -/
theorem EnvelopeContact (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (v₀ : WithLp 2 (F × ℝ) → ℝ)
    (hv₀ : IsFitClass C₀ v₀) (hna : ¬ IsSpaceTimeAffine v₀) :
    ∃ (κ H : ℝ) (v : WithLp 2 (F × ℝ) → ℝ),
      0 < κ ∧ IsFitClass C₀ v ∧
      IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))) ∧
      HasJensenBound Set.univ v κ ∧
      ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} ∧
      SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ) ∧
      IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} (ContactEnv v κ) ∧
      (∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
        v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧
        ContactEnv v κ z ≤ v z) ∧
      ContactEnv v κ (toLp 2 ((0 : F), (1 : ℝ))) = 0 ∧
      v (toLp 2 ((0 : F), (1 : ℝ))) = 0 ∧
      (∀ t : ℝ, 0 < t → ConcaveOn ℝ (Set.univ : Set F)
        (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t))) ∧
      (∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z = v z →
        (BaryEnv v (ofLp z).2 z - v z) / (ofLp z).2 = κ ^ 2 / 2) ∧
      EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal) ∧
      Tendsto (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
        (𝓝[>] (0 : ℝ)) (𝓝 H) := by
  classical
  -- Step 1: a centered nonaffine member and the extremal constant.
  obtain ⟨p₀, a₀, hfit₀⟩ := hv₀.2 0 1 one_pos
  obtain ⟨w, hw⟩ : ∃ g : WithLp 2 (F × ℝ) → ℝ, g = FrameChange v₀ 0 1 p₀ a₀ := ⟨_, rfl⟩
  have hwclass : IsFitClass C₀ w := by
    rw [hw]
    exact (FrameInvariance C₀ v₀ hv₀ 0 1 one_pos p₀ a₀).1
  have hwform : ∀ (x : F) (t : ℝ), w (toLp 2 (x - t • p₀, t))
      = v₀ (toLp 2 (x, t)) - v₀ 0 - inner ℝ p₀ (x - t • p₀)
        - (a₀ + ‖p₀‖ ^ 2 / 2) * t := by
    intro x t
    rw [hw]
    simp only [FrameChange, one_smul, one_mul, div_one, zero_add]
    rw [show (x - t • p₀) + t • p₀ = x from by abel]
  have hw0 : w 0 = 0 := by
    have h := hwform 0 0
    simp only [zero_smul, sub_zero, mul_zero, inner_zero_right] at h
    rw [show ((0 : F), (0 : ℝ)) = (0 : F × ℝ) from rfl, toLp_zero] at h
    linarith [h]
  have hwcent : IsCenteredAt C₀ w 0 := by
    refine ⟨hw0, ?_⟩
    have hpt : (0 : WithLp 2 (F × ℝ))
        + toLp 2 ((1 : ℝ) • ((ofLp (0 : WithLp 2 (F × ℝ))).1
          + (ofLp (0 : WithLp 2 (F × ℝ))).2 • p₀), (1 : ℝ) * (ofLp (0 : WithLp 2 (F × ℝ))).2)
        = 0 := by simp
    have h := (FrameInvariance C₀ v₀ hv₀ 0 1 one_pos p₀ a₀).2 0 1 p₀ a₀ (by
      rw [hpt, one_mul]
      exact hfit₀)
    rw [hw]
    simpa using h
  have hwna : ¬ IsSpaceTimeAffine w := by
    intro ⟨q, bb, cc, haff⟩
    refine hna ⟨q + p₀, bb - (inner ℝ q p₀ : ℝ) - ‖p₀‖ ^ 2 / 2 + a₀, cc + v₀ 0, fun z => ?_⟩
    obtain ⟨x, hx⟩ : ∃ a : F, a = (ofLp z).1 := ⟨_, rfl⟩
    obtain ⟨t, ht⟩ : ∃ a : ℝ, a = (ofLp z).2 := ⟨_, rfl⟩
    have hzeq : z = toLp 2 (x, t) := by rw [hx, ht, Prod.mk.eta, toLp_ofLp]
    have h1 := hwform x t
    have h2 := haff (toLp 2 (x - t • p₀, t))
    dsimp only at h2
    rw [h2] at h1
    have h3 : (inner ℝ q (x - t • p₀) : ℝ) = inner ℝ q x - t * inner ℝ q p₀ := by
      rw [inner_sub_right, real_inner_smul_right]
    have h4 : (inner ℝ p₀ (x - t • p₀) : ℝ) = inner ℝ p₀ x - t * ‖p₀‖ ^ 2 := by
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [h3, h4] at h1
    rw [hzeq]
    dsimp only
    rw [inner_add_left]
    linarith [h1]
  obtain ⟨vc, κ, hvcclass, hvccent, hvcna, hκ0, hvcJ, hκmin⟩ :=
    JensenSupremumFinite C₀ hC₀ w hwclass hwcent hwna
  -- Step 2: near-attaining configurations.
  have hradnn : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
      0 ≤ BaryRadius n θ y x := by
    intro n θ y x
    rw [BaryRadius]
    exact Real.sqrt_nonneg _
  have hraddegen : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
      IsBaryConfig n θ y x → BaryRadius n θ y x = 0 → ∀ i, y i = x := by
    intro n θ y x hcfg hrad i
    obtain ⟨hpos, hsum, hmean⟩ := hcfg
    have hnn : (0 : ℝ) ≤ ∑ i, θ i * ‖y i - x‖ ^ 2 := by
      refine Finset.sum_nonneg (fun i _ => ?_)
      exact mul_nonneg (hpos i).le (by positivity)
    have hz : (∑ i, θ i * ‖y i - x‖ ^ 2) = 0 := by
      rw [BaryRadius, Real.sqrt_eq_zero hnn] at hrad
      exact hrad
    have hterm : θ i * ‖y i - x‖ ^ 2 = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => ?_)).mp hz i (Finset.mem_univ i)
      exact mul_nonneg (hpos k).le (by positivity)
    have hnorm : ‖y i - x‖ = 0 := by
      rcases mul_eq_zero.mp hterm with h | h
      · exact absurd h (ne_of_gt (hpos i))
      · have : ‖y i - x‖ ^ 2 = 0 := h
        nlinarith [this, norm_nonneg (y i - x)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hnear : ∀ ε : ℝ, 0 < ε →
      ∃ (t : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
        IsBaryConfig n θ y x ∧ 0 < BaryRadius n θ y x ∧
        (κ - ε) * BaryRadius n θ y x
          < (∑ i, θ i * vc (toLp 2 (y i, t))) - vc (toLp 2 (x, t)) := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have hJ' : HasJensenBound Set.univ vc (κ - ε) := by
      intro t _ n θ y x hcfg
      rcases lt_or_eq_of_le (hradnn n θ y x) with hpos | hzero
      · exact hcon t n θ y x hcfg hpos
      · have hrad : BaryRadius n θ y x = 0 := hzero.symm
        have hall := hraddegen n θ y x hcfg hrad
        obtain ⟨hp, hs, hm⟩ := hcfg
        have hsum0 : (∑ i, θ i * vc (toLp 2 (y i, t)))
            = vc (toLp 2 (x, t)) := by
          have h1 : ∀ i : Fin n, θ i * vc (toLp 2 (y i, t))
              = θ i * vc (toLp 2 (x, t)) := by
            intro i
            rw [hall i]
          rw [Finset.sum_congr rfl (fun i _ => h1 i), ← Finset.sum_mul, hs, one_mul]
        rw [hsum0, hrad]
        simp
    have := hκmin (κ - ε) hJ'
    linarith
  choose tj nj θj yj xj hcfgj hρj hDj using
    (fun j : ℕ => hnear (1 / (j + 1)) (by positivity))
  -- the Jensen bound is preserved by every change of frame, from (F0)
  have hJframe : ∀ (g : WithLp 2 (F × ℝ) → ℝ) (z₀ : WithLp 2 (F × ℝ)) (R : ℝ), 0 < R →
      ∀ (p₀ : F) (a₀ : ℝ), HasJensenBound Set.univ g κ →
      HasJensenBound Set.univ (FrameChange g z₀ R p₀ a₀) κ := by
    intro g z₀ R hR p₀ a₀ hJ s _ n θ y x hcfg
    obtain ⟨hiff, hrad, -, hdef⟩ := FrameConfigCovariance g z₀ R hR p₀ a₀ s
    have himg : IsBaryConfig n θ (fun i => (ofLp z₀).1 + R • (y i + s • p₀))
        ((ofLp z₀).1 + R • (x + s • p₀)) := (hiff n θ y x).mpr hcfg
    have hJimg := hJ ((ofLp z₀).2 + R * s) (Set.mem_univ _) n θ
      (fun i => (ofLp z₀).1 + R • (y i + s • p₀)) ((ofLp z₀).1 + R • (x + s • p₀)) himg
    rw [hrad n θ y x] at hJimg
    rw [hdef n θ y x hcfg]
    have hRinv : (0 : ℝ) < 1 / R := by positivity
    have hmul := mul_le_mul_of_nonneg_left hJimg hRinv.le
    have hrw : (1 / R) * (κ * (R * BaryRadius n θ y x)) = κ * BaryRadius n θ y x := by
      field_simp
    linarith [hmul, hrw]
  -- Step 3: normalizing each configuration.
  obtain ⟨ρ, hρ⟩ : ∃ r : ℕ → ℝ,
      r = fun j => BaryRadius (nj j) (θj j) (yj j) (xj j) := ⟨_, rfl⟩
  have hρapp : ∀ j, ρ j = BaryRadius (nj j) (θj j) (yj j) (xj j) := by
    intro j
    rw [hρ]
  have hρpos : ∀ j, 0 < ρ j := by
    intro j
    rw [hρapp j]
    exact hρj j
  have hstep3 : ∀ j : ℕ, ∃ (vj : WithLp 2 (F × ℝ) → ℝ) (yh : Fin (nj j) → F),
      IsFitClass C₀ vj ∧ IsCenteredAt C₀ vj 0 ∧ HasJensenBound Set.univ vj κ ∧
      IsBaryConfig (nj j) (θj j) yh 0 ∧ BaryRadius (nj j) (θj j) yh 0 = 1 ∧
      κ - 1 / (j + 1) < ∑ i, θj j i * vj (toLp 2 (yh i, (0 : ℝ))) := by
    intro j
    obtain ⟨pj, aj, hfitj⟩ := hvcclass.2 (toLp 2 (xj j, tj j)) (ρ j) (hρpos j)
    obtain ⟨vj, hvj⟩ : ∃ g : WithLp 2 (F × ℝ) → ℝ,
        g = FrameChange vc (toLp 2 (xj j, tj j)) (ρ j) pj aj := ⟨_, rfl⟩
    obtain ⟨yh, hyh⟩ : ∃ f : Fin (nj j) → F,
        f = fun i => (ρ j)⁻¹ • (yj j i - xj j) := ⟨_, rfl⟩
    obtain ⟨hiff, hrad, -, hdef⟩ :=
      FrameConfigCovariance vc (toLp 2 (xj j, tj j)) (ρ j) (hρpos j) pj aj (0 : ℝ)
    -- the normalized positions are carried back to the original ones
    have hTy : ∀ i, (ofLp (toLp 2 (xj j, tj j))).1 + ρ j • (yh i + (0 : ℝ) • pj)
        = yj j i := by
      intro i
      simp only [zero_smul, add_zero, hyh]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt (hρpos j)), one_smul]
      abel
    have hTx : (ofLp (toLp 2 (xj j, tj j))).1 + ρ j • ((0 : F) + (0 : ℝ) • pj)
        = xj j := by
      simp
    have hTfun : (fun i => (ofLp (toLp 2 (xj j, tj j))).1 + ρ j • (yh i + (0 : ℝ) • pj))
        = yj j := funext hTy
    -- the class, the centering and the Jensen bound
    have hvjclass : IsFitClass C₀ vj := by
      rw [hvj]
      exact (FrameInvariance C₀ vc hvcclass (toLp 2 (xj j, tj j)) (ρ j) (hρpos j) pj aj).1
    have hvj0 : vj 0 = 0 := by
      rw [hvj]
      simp only [FrameChange, ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_smul,
        add_zero, smul_zero, mul_zero, inner_zero_right]
      rw [show (toLp 2 ((0 : F), (0 : ℝ)) : WithLp 2 (F × ℝ)) = 0 from by simp, add_zero]
      simp
    have hvjcent : IsCenteredAt C₀ vj 0 := by
      refine ⟨hvj0, ?_⟩
      have hpt : (toLp 2 (xj j, tj j) : WithLp 2 (F × ℝ))
          + toLp 2 ((ρ j) • ((ofLp (0 : WithLp 2 (F × ℝ))).1
            + (ofLp (0 : WithLp 2 (F × ℝ))).2 • pj),
            (ρ j) * (ofLp (0 : WithLp 2 (F × ℝ))).2)
          = toLp 2 (xj j, tj j) := by simp
      have h := (FrameInvariance C₀ vc hvcclass (toLp 2 (xj j, tj j)) (ρ j)
        (hρpos j) pj aj).2 0 1 pj aj (by
          rw [hpt, mul_one]
          exact hfitj)
      rw [hvj]
      simpa using h
    have hvjJ : HasJensenBound Set.univ vj κ := by
      rw [hvj]
      exact hJframe vc (toLp 2 (xj j, tj j)) (ρ j) (hρpos j) pj aj hvcJ
    -- the normalized configuration has mean zero and radius one
    have hcfgh : IsBaryConfig (nj j) (θj j) yh 0 := by
      refine (hiff (nj j) (θj j) yh 0).mp ?_
      rw [hTfun, hTx]
      exact hcfgj j
    have hradh : BaryRadius (nj j) (θj j) yh 0 = 1 := by
      have h := hrad (nj j) (θj j) yh 0
      rw [hTfun, hTx] at h
      have h2 : ρ j = ρ j * BaryRadius (nj j) (θj j) yh 0 := by
        rw [← h, hρapp j]
      have h3 := hρpos j
      field_simp at h2
      linarith [h2]
    -- the normalized defect
    have hdefect : (∑ i, θj j i * vj (toLp 2 (yh i, (0 : ℝ))))
        = (1 / ρ j) * ((∑ i, θj j i * vc (toLp 2 (yj j i, tj j)))
            - vc (toLp 2 (xj j, tj j))) := by
      have h := hdef (nj j) (θj j) yh 0 hcfgh
      rw [hvj]
      have hz : (ofLp (toLp 2 (xj j, tj j))).2 + ρ j * (0 : ℝ) = tj j := by simp
      have hyfun : ∀ i, (ofLp (toLp 2 (xj j, tj j))).1 + ρ j • (yh i + (0 : ℝ) • pj)
          = yj j i := hTy
      simp only [hyfun, hTx, hz] at h
      rw [show (toLp 2 ((0 : F), (0 : ℝ)) : WithLp 2 (F × ℝ)) = 0 from by simp] at h
      rw [← hvj] at h ⊢
      rw [hvj0, sub_zero] at h
      exact h
    refine ⟨vj, yh, hvjclass, hvjcent, hvjJ, hcfgh, hradh, ?_⟩
    rw [hdefect]
    have hD := hDj j
    rw [← hρapp j] at hD
    have hρne : ρ j ≠ 0 := ne_of_gt (hρpos j)
    have hinv : (0 : ℝ) < 1 / ρ j := div_pos one_pos (hρpos j)
    have hmul := mul_lt_mul_of_pos_left hD hinv
    have hrw : (1 / ρ j) * ((κ - 1 / ((j : ℝ) + 1)) * ρ j) = κ - 1 / ((j : ℝ) + 1) := by
      field_simp
    linarith [hmul, hrw]
  -- Step 4, first part: the Jensen bound passes to a locally uniform limit.
  have hJlimit : ∀ (u : ℕ → WithLp 2 (F × ℝ) → ℝ) (g : WithLp 2 (F × ℝ) → ℝ),
      (∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K →
        TendstoUniformlyOn u g atTop K) →
      (∀ j, HasJensenBound Set.univ (u j) κ) → HasJensenBound Set.univ g κ := by
    intro u g hunif hJ t _ n θ y x hcfg
    have hptw : ∀ z : WithLp 2 (F × ℝ), Tendsto (fun j => u j z) atTop (𝓝 (g z)) := by
      intro z
      exact (hunif {z} isCompact_singleton).tendsto_at rfl
    have hlim : Tendsto (fun j => (∑ i, θ i * u j (toLp 2 (y i, t)))
        - u j (toLp 2 (x, t))) atTop
        (𝓝 ((∑ i, θ i * g (toLp 2 (y i, t))) - g (toLp 2 (x, t)))) := by
      refine Tendsto.sub ?_ (hptw _)
      refine tendsto_finsetSum _ (fun i _ => ?_)
      exact (hptw (toLp 2 (y i, t))).const_mul (θ i)
    refine le_of_tendsto hlim ?_
    exact Filter.Eventually.of_forall
      (fun j => hJ j t (Set.mem_univ _) n θ y x hcfg)
  -- ===========================================================================
  -- ROUTE MAP for the rest of the proof, by the names it introduces.
  --
  -- Step 4.  `ClassCompactness` gives the limit `vhat` (`hvhatclass`,
  -- `hvhatcent`, `hvhatJ` through `hJlimit`).  `hsubq` reads subquadratic growth
  -- of any centered class member straight off `UniformSubquadratic`, so
  -- `FitClassGrowth` is not needed here.  Claim 4a (`hclaim4a`) is the FINITE
  -- far/near split, not the paper's measure route: `IsBaryConfig` is a family
  -- over `Fin n`, so no tightness, no weak limit and no cutoff appear.  The
  -- attainment `hattain : BaryEnv vhat R 0 = κ / 2` at `R = 1/κ` is a squeeze --
  -- lower bound from the configuration via `EnvelopeCompetitorBounds`, upper
  -- bound from `BaryEnvSandwich` -- and the chain must run in that order.
  --
  -- Claim T (translation in time), proved inline because the `.tex` carries it
  -- inline: `hTfit`, `hTLimitOp`, `hTsub`, `hTsuper`, `hTclass`, `hTcent`, `hTJ`,
  -- `hTbary`, in the forward direction, which is all Step 5 uses; the converse is
  -- the same statement at `-c`.  Parts that do not see the time direction are
  -- proved for a general shift `sh`; only the Jensen bound and the barycentric
  -- envelope need the shift to be purely temporal.  The viscosity transfer is
  -- `iteratedFDeriv_comp_add_right` for the 2-jet and `fderiv_comp_add_right` for
  -- the gradient inside `LimitOp`.
  --
  -- Step 5.  `g = FrameChange vhat 0 R pst ast` (`hgclass`, `hgcent`, `hgJ`).
  -- (F2) is needed only at `σ = 1`, `(y,s) = (0,0)`, `z₀ = 0`, where `T_0 y = R•y`
  -- and `t = 0`, so it is proved in that specialization and in MULTIPLIED form,
  -- `hF2 : R * BaryEnv g 1 0 = BaryEnv vhat R 0`, which keeps everything
  -- division-free but one `le_div_iff₀`.  Both halves are
  -- `EnvelopeCompetitorBounds`' third conjunct used against itself, with the
  -- configuration bijection from `FrameConfigCovariance` (i),(iii), the radius
  -- from (ii) and the value identity from (iv).  Then
  -- `hgapg : BaryEnv g 1 0 = κ ^ 2 / 2`, and the final function
  -- `vfin = fun ζ => g (ζ - toLp 2 (0,1))` is the ONE combined change of frame
  -- and time translation.
  --
  -- Step 6.  (a) `hWsand` from `BaryEnvSandwich` at `I = Set.Ioi 0` and `s = t`;
  -- (b) `hWcont` and `hWconc` from `BaryEnvDuality` at the OPEN `I = Set.Ioi 0`,
  -- its continuity clause composed with `z ↦ ((ofLp z).2, z)` and its concavity
  -- clause at `s = t`; (c) `hWgrow` from the sandwich and the growth of `vfin`
  -- with the paper's `M = max {M₁, sqrt (2 c_J / ε)}`; (d) `hWsub` from
  -- `BarycentricSubsolution` at `c = κ ^ 2 / 2`, through `hbridge`; (e) `hWgap`
  -- straight from `ContactEnv`'s definition.
  -- THE BRIDGE THAT IS NOT DEFEQ (`hbridge`).  `BarycentricSubsolution` concludes
  -- about `fun z => BaryEnv f (ofLp z).2 z - (κ ^ 2 / 2) * (ofLp z).2` while
  -- `ContactEnv` is `BaryEnv v (ofLp z).2 z - κ ^ 2 * (ofLp z).2 / 2`: equal as
  -- reals, NOT definitionally equal, and `IsLimitSubOn` takes the FUNCTION, so the
  -- bridge is `funext` then `ring` and then an explicit rewrite (pm-0035).
  --
  -- Step 7.  `H := (EnvHamiltonian vfin z_*).toReal`, finite because
  -- `EnvHamiltonianSolution`'s third clause rules out `⊤` and `ContactFiniteSlope`
  -- rules out `⊥`; `EReal.coe_toReal` takes NOT-TOP FIRST.  `ContactFiniteSlope`
  -- carries the paper's whole lower-bound argument -- the `r = κ` squeeze, the
  -- duality minimizing slope, the positive-weight attainment and the completed
  -- square -- so it is one citation and none of that is redone here.  The slope
  -- comparison is `EnvelopeCompetitorBounds` for `W` and for `vfin`, each half
  -- against the other's domination half (`hslopeP`, `hslopeM`), and the limit is
  -- `EnvelopeSlopeOrder` clause 2 at `h < 1` (`hWlow`) extended by clause 1
  -- (`hWmono`) to every `h > 0`, then `tendsto_order`.
  -- ===========================================================================
  -- Step 4: compactness and the attainment of the sandwich.
  choose vj yh hvjclass hvjcent hvjJ hcfgh hradh hdefj using hstep3
  obtain ⟨ι, vhat, hιmono, hunif, hvhatclass, hvhatcent⟩ :=
    ClassCompactness C₀ hC₀ 0 (Or.inl rfl) vj hvjclass hvjcent
  have hvhatJ : HasJensenBound Set.univ vhat κ :=
    hJlimit (fun j => vj (ι j)) vhat hunif (fun j => hvjJ (ι j))
  have hzero : (toLp 2 ((0 : F), (0 : ℝ)) : WithLp 2 (F × ℝ)) = 0 := by simp
  -- the second moment of each normalized configuration is one
  have hmom : ∀ j, (∑ i, θj j i * ‖yh j i‖ ^ 2) = 1 := by
    intro j
    have h := hradh j
    rw [BaryRadius] at h
    have hrw : ∀ i : Fin (nj j), θj j i * ‖yh j i - (0 : F)‖ ^ 2
        = θj j i * ‖yh j i‖ ^ 2 := by
      intro i
      rw [sub_zero]
    rw [Finset.sum_congr rfl (fun i _ => hrw i)] at h
    exact Real.sqrt_eq_one.mp h
  -- the Jensen bound caps each normalized defect at `κ`
  have hupper : ∀ j, (∑ i, θj j i * vj j (toLp 2 (yh j i, (0 : ℝ)))) ≤ κ := by
    intro j
    have h := hvjJ j 0 (Set.mem_univ _) (nj j) (θj j) (yh j) 0 (hcfgh j)
    rw [hradh j, mul_one, hzero, (hvjcent j).1] at h
    linarith [h]
  have hdeftend : Tendsto (fun j => ∑ i, θj j i * vj j (toLp 2 (yh j i, (0 : ℝ))))
      atTop (𝓝 κ) := by
    have hlow : Tendsto (fun j : ℕ => κ - 1 / ((j : ℝ) + 1)) atTop (𝓝 κ) := by
      have h0 : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using Filter.Tendsto.const_sub κ h0
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun j => ?_) (fun j => hupper j)
    exact (hdefj j).le
  -- Claim 4a: the extremal defect survives the limit.  Finite far/near split.
  have hsplit : ∀ (M dd : ℝ), 0 < dd → ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F)
      (u : WithLp 2 (F × ℝ) → ℝ), (∀ i, 0 < θ i) → (∑ i, θ i) = 1 →
      (∑ i, θ i * ‖y i‖ ^ 2) = 1 →
      (∀ i, ‖y i‖ ≤ M →
        |vhat (toLp 2 (y i, (0 : ℝ))) - u (toLp 2 (y i, (0 : ℝ)))| ≤ dd / 8) →
      (∀ i, M ≤ ‖y i‖ → |vhat (toLp 2 (y i, (0 : ℝ)))| ≤ dd / 8 * ‖y i‖ ^ 2) →
      (∀ i, M ≤ ‖y i‖ → |u (toLp 2 (y i, (0 : ℝ)))| ≤ dd / 8 * ‖y i‖ ^ 2) →
      |(∑ i, θ i * vhat (toLp 2 (y i, (0 : ℝ))))
        - (∑ i, θ i * u (toLp 2 (y i, (0 : ℝ))))| ≤ dd / 8 + dd / 4 := by
    intro M dd hdd n θ y u hpos hsum hmom2 hnear hfar1 hfar2
    obtain ⟨d, hd⟩ : ∃ d : Fin n → ℝ, d = fun i =>
      |vhat (toLp 2 (y i, (0 : ℝ))) - u (toLp 2 (y i, (0 : ℝ)))| := ⟨_, rfl⟩
    have hdnn : ∀ i, 0 ≤ d i := by intro i; rw [hd]; exact abs_nonneg _
    -- the pointwise bound: `d i ≤ dd/8 + (dd/4) * ‖y i‖ ^ 2` in both regimes
    have hpt : ∀ i, θ i * d i ≤ θ i * (dd / 8) + θ i * (dd / 4 * ‖y i‖ ^ 2) := by
      intro i
      rcases le_or_gt (‖y i‖) M with hle | hgt
      · have h1 : d i ≤ dd / 8 := by rw [hd]; exact hnear i hle
        have h2 : (0 : ℝ) ≤ θ i * (dd / 4 * ‖y i‖ ^ 2) := by
          have := (hpos i).le
          have : (0:ℝ) ≤ dd / 4 * ‖y i‖ ^ 2 := by positivity
          exact mul_nonneg (hpos i).le this
        have h3 : θ i * d i ≤ θ i * (dd / 8) :=
          mul_le_mul_of_nonneg_left h1 (hpos i).le
        linarith
      · have hMle : M ≤ ‖y i‖ := le_of_lt hgt
        have h1 : d i ≤ dd / 4 * ‖y i‖ ^ 2 := by
          rw [hd]
          have ha := hfar1 i hMle
          have hb := hfar2 i hMle
          have := abs_sub (vhat (toLp 2 (y i, (0 : ℝ)))) (u (toLp 2 (y i, (0 : ℝ))))
          have hsub : |vhat (toLp 2 (y i, (0 : ℝ))) - u (toLp 2 (y i, (0 : ℝ)))|
              ≤ |vhat (toLp 2 (y i, (0 : ℝ)))| + |u (toLp 2 (y i, (0 : ℝ)))| :=
            abs_sub _ _
          linarith [hsub, ha, hb]
        have h2 : (0 : ℝ) ≤ θ i * (dd / 8) := by
          have : (0:ℝ) ≤ dd / 8 := by positivity
          exact mul_nonneg (hpos i).le this
        have h3 : θ i * d i ≤ θ i * (dd / 4 * ‖y i‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (hpos i).le
        linarith
    have hsum1 : (∑ i, θ i * (dd / 8)) = dd / 8 := by
      rw [← Finset.sum_mul, hsum, one_mul]
    have hsum2 : (∑ i, θ i * (dd / 4 * ‖y i‖ ^ 2)) = dd / 4 := by
      have hrw : ∀ i : Fin n, θ i * (dd / 4 * ‖y i‖ ^ 2)
          = (dd / 4) * (θ i * ‖y i‖ ^ 2) := by intro i; ring
      rw [Finset.sum_congr rfl (fun i _ => hrw i), ← Finset.mul_sum, hmom2, mul_one]
    have hchain : (∑ i, θ i * d i) ≤ dd / 8 + dd / 4 := by
      have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpt i)
      rw [Finset.sum_add_distrib, hsum1, hsum2] at h
      exact h
    have habs : |(∑ i, θ i * vhat (toLp 2 (y i, (0 : ℝ))))
        - (∑ i, θ i * u (toLp 2 (y i, (0 : ℝ))))| ≤ ∑ i, θ i * d i := by
      rw [← Finset.sum_sub_distrib]
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum (fun i _ => ?_)
      rw [← mul_sub, abs_mul, abs_of_pos (hpos i), hd]
    linarith [habs, hchain]
  have hclaim4a : Tendsto
      (fun j => ∑ i, θj (ι j) i * vhat (toLp 2 (yh (ι j) i, (0 : ℝ)))) atTop (𝓝 κ) := by
    have hdiff : Tendsto (fun j =>
        (∑ i, θj (ι j) i * vhat (toLp 2 (yh (ι j) i, (0 : ℝ))))
          - (∑ i, θj (ι j) i * vj (ι j) (toLp 2 (yh (ι j) i, (0 : ℝ)))))
        atTop (𝓝 0) := by
      rw [Metric.tendsto_atTop]
      intro δ hδ
      obtain ⟨M, hM0, hMbd⟩ := UniformSubquadratic C₀ hC₀ (0 : WithLp 2 (F × ℝ))
        (Or.inl rfl) {(0 : ℝ)} isCompact_singleton (δ / 8) (by positivity)
      obtain ⟨K, hK⟩ : ∃ S : Set (WithLp 2 (F × ℝ)),
          S = (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
            (Metric.closedBall (0 : F) M ×ˢ ({(0 : ℝ)} : Set ℝ)) := ⟨_, rfl⟩
      have hKcpt : IsCompact K := by
        rw [hK]
        exact ((isCompact_closedBall (0 : F) M).prod isCompact_singleton).image (by fun_prop)
      have hev := (Metric.tendstoUniformlyOn_iff.mp (hunif K hKcpt)) (δ / 8) (by positivity)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      refine ⟨N, fun j hj => ?_⟩
      have hnear : ∀ i, ‖yh (ι j) i‖ ≤ M →
          |vhat (toLp 2 (yh (ι j) i, (0 : ℝ)))
            - vj (ι j) (toLp 2 (yh (ι j) i, (0 : ℝ)))| ≤ δ / 8 := by
        intro i hle
        have hmem : (toLp 2 (yh (ι j) i, (0 : ℝ)) : WithLp 2 (F × ℝ)) ∈ K := by
          rw [hK]
          refine ⟨(yh (ι j) i, (0 : ℝ)), ⟨?_, rfl⟩, rfl⟩
          simpa using hle
        have hd := hN j hj _ hmem
        rw [Real.dist_eq] at hd
        exact hd.le
      have hfar1 : ∀ i, M ≤ ‖yh (ι j) i‖ →
          |vhat (toLp 2 (yh (ι j) i, (0 : ℝ)))| ≤ δ / 8 * ‖yh (ι j) i‖ ^ 2 := by
        intro i hge
        exact hMbd vhat hvhatclass hvhatcent _ (by simpa using hge) (by simp)
      have hfar2 : ∀ i, M ≤ ‖yh (ι j) i‖ →
          |vj (ι j) (toLp 2 (yh (ι j) i, (0 : ℝ)))| ≤ δ / 8 * ‖yh (ι j) i‖ ^ 2 := by
        intro i hge
        exact hMbd (vj (ι j)) (hvjclass (ι j)) (hvjcent (ι j)) _
          (by simpa using hge) (by simp)
      have hb := hsplit M δ hδ (nj (ι j)) (θj (ι j)) (yh (ι j)) (vj (ι j))
        (hcfgh (ι j)).1 (hcfgh (ι j)).2.1 (hmom (ι j)) hnear hfar1 hfar2
      rw [Real.dist_eq, sub_zero]
      linarith [hb]
    have hcomp := hdeftend.comp hιmono.tendsto_atTop
    have hsum := hdiff.add hcomp
    simpa using hsum
  -- subquadratic growth comes straight from the uniform statement, for any
  -- centered member of the class
  have hsubq : ∀ zc : WithLp 2 (F × ℝ), (zc = 0 ∨ zc = toLp 2 ((0 : F), (1 : ℝ))) →
      ∀ g : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ g → IsCenteredAt C₀ g zc →
      SubquadraticGrowth (Set.univ : Set ℝ) g := by
    intro zc hzc g hgc hgcent J _ hJc ε hε
    obtain ⟨M, hM0, hMbd⟩ := UniformSubquadratic C₀ hC₀ zc hzc J hJc ε hε
    exact ⟨M, hM0, fun z h1 h2 => hMbd g hgc hgcent z h1 h2⟩
  -- the attainment of the sandwich: a squeeze, lower bound then upper bound
  obtain ⟨R, hR⟩ : ∃ r : ℝ, r = 1 / κ := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    rw [hR]
    exact div_pos one_pos hκ0
  have hvhatcont : ContinuousOn vhat
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hvhatclass.1.1.2.1
  have hvhatgrow : SubquadraticGrowth (Set.univ : Set ℝ) vhat :=
    hsubq 0 (Or.inl rfl) vhat hvhatclass hvhatcent
  obtain ⟨-, -, hCB3⟩ :=
    EnvelopeCompetitorBounds (F := F) Set.univ vhat hvhatcont hvhatgrow
  have hlow : κ - 1 / (2 * R) ≤ BaryEnv vhat R 0 := by
    have hdom := (hCB3 R 0 hR0 (Set.mem_univ _)).1
    refine le_of_tendsto (hclaim4a.sub_const (1 / (2 * R))) ?_
    refine Filter.Eventually.of_forall (fun j => ?_)
    have h := hdom (nj (ι j)) (θj (ι j)) (yh (ι j)) (by
      simpa using hcfgh (ι j))
    simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero] at h
    rw [hradh (ι j)] at h
    simpa using h
  have hupp : BaryEnv vhat R 0 ≤ κ ^ 2 * R / 2 := by
    have h := (BaryEnvSandwich (F := F) Set.univ vhat κ hκ0.le hvhatcont hvhatJ
      hvhatgrow R 0 hR0 (Set.mem_univ _)).2
    rw [hvhatcent.1] at h
    linarith [h]
  have hattain : BaryEnv vhat R 0 = κ / 2 := by
    have h1 : 1 / (2 * R) = κ / 2 := by
      rw [hR]
      field_simp
    have h2 : κ ^ 2 * R / 2 = κ / 2 := by
      rw [hR]
      field_simp
    rw [h1] at hlow
    rw [h2] at hupp
    linarith [hlow, hupp]
  -- ===== Claim T: translation in time, in the forward direction used below =====
  have hTfit : ∀ (sh : WithLp 2 (F × ℝ)) (g : WithLp 2 (F × ℝ) → ℝ)
      (ζ : WithLp 2 (F × ℝ)) (ρ : ℝ) (p : F) (a : ℝ),
      IsFit C₀ g (ζ - sh) ρ p a → IsFit C₀ (fun ξ => g (ξ - sh)) ζ ρ p a := by
    intro sh g ζ ρ p a hf h l hl hhl
    have hpt : ζ + toLp 2 (h, l) - sh = (ζ - sh) + toLp 2 (h, l) := by abel
    show |g (ζ + toLp 2 (h, l) - sh) - g (ζ - sh) - inner ℝ p h
        - (a - ‖p‖ ^ 2 / 2) * l| ≤ C₀ * ρ
    rw [hpt]
    exact hf h l hl hhl
  have hTLimitOp : ∀ (sh : WithLp 2 (F × ℝ)) (φ : WithLp 2 (F × ℝ) → ℝ)
      (ζ : WithLp 2 (F × ℝ)),
      LimitOp (fun ν => φ (ν + sh)) ζ = LimitOp φ (ζ + sh) := by
    intro sh φ ζ
    have hgr : gradient (fun ν : WithLp 2 (F × ℝ) => φ (ν + sh)) ζ
        = gradient φ (ζ + sh) := by
      simp only [gradient, fderiv_comp_add_right]
    rw [LimitOp, LimitOp, hgr, iteratedFDeriv_comp_add_right]
  have hTshiftCD : ∀ sh : WithLp 2 (F × ℝ),
      ContDiff ℝ 2 (fun ν : WithLp 2 (F × ℝ) => ν + sh) :=
    fun sh => contDiff_id.add contDiff_const
  have hTten : ∀ (sh ζ : WithLp 2 (F × ℝ)),
      Tendsto (fun ν : WithLp 2 (F × ℝ) => ν + sh)
        (nhdsWithin (ζ - sh) (Set.univ : Set (WithLp 2 (F × ℝ))))
        (nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ)))) := by
    intro sh ζ
    rw [nhdsWithin_univ, nhdsWithin_univ]
    have h : Tendsto (fun ν : WithLp 2 (F × ℝ) => ν + sh) (𝓝 (ζ - sh))
        (𝓝 (ζ - sh + sh)) := ((hTshiftCD sh).continuous).tendsto _
    rw [sub_add_cancel] at h
    exact h
  have hTcont : ∀ (sh : WithLp 2 (F × ℝ)) (g : WithLp 2 (F × ℝ) → ℝ),
      ContinuousOn g (Set.univ : Set (WithLp 2 (F × ℝ))) →
      ContinuousOn (fun ξ => g (ξ - sh)) (Set.univ : Set (WithLp 2 (F × ℝ))) := by
    intro sh g hg
    exact hg.comp ((continuous_id.sub continuous_const).continuousOn)
      (fun z _ => Set.mem_univ _)
  have hTsub : ∀ (sh : WithLp 2 (F × ℝ)) (g : WithLp 2 (F × ℝ) → ℝ),
      IsLimitSubOn Set.univ g → IsLimitSubOn Set.univ (fun ξ => g (ξ - sh)) := by
    intro sh g hg
    refine ⟨isOpen_univ, hTcont sh g hg.2.1, ?_⟩
    intro ζ _ φ hφ hmax
    have hzs : ζ - sh + sh = ζ := by abel
    have hφ' : ContDiffAt ℝ 2 (fun ν : WithLp 2 (F × ℝ) => φ (ν + sh)) (ζ - sh) := by
      have h2 : ContDiffAt ℝ 2 φ ((fun ν : WithLp 2 (F × ℝ) => ν + sh) (ζ - sh)) := by
        simpa only [hzs] using hφ
      exact h2.comp (ζ - sh) ((hTshiftCD sh).contDiffAt)
    have hmax' : IsLocalMaxOn (fun ν => g ν - φ (ν + sh))
        (Set.univ : Set (WithLp 2 (F × ℝ))) (ζ - sh) := by
      have h0 : ∀ᶠ ξ in nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ))),
          g (ξ - sh) - φ ξ ≤ g (ζ - sh) - φ ζ := hmax
      have h1 := (hTten sh ζ).eventually h0
      show ∀ᶠ ν in nhdsWithin (ζ - sh) (Set.univ : Set (WithLp 2 (F × ℝ))),
        g ν - φ (ν + sh) ≤ g (ζ - sh) - φ (ζ - sh + sh)
      rw [hzs]
      filter_upwards [h1] with ν hν
      simpa using hν
    have hres := hg.2.2 (ζ - sh) (Set.mem_univ _) (fun ν => φ (ν + sh)) hφ' hmax'
    rw [hTLimitOp sh φ (ζ - sh), hzs] at hres
    exact hres
  have hTsuper : ∀ (sh : WithLp 2 (F × ℝ)) (g : WithLp 2 (F × ℝ) → ℝ),
      IsLimitSuperOn Set.univ g → IsLimitSuperOn Set.univ (fun ξ => g (ξ - sh)) := by
    intro sh g hg
    refine ⟨isOpen_univ, hTcont sh g hg.2.1, ?_⟩
    intro ζ _ φ hφ hmin
    have hzs : ζ - sh + sh = ζ := by abel
    have hφ' : ContDiffAt ℝ 2 (fun ν : WithLp 2 (F × ℝ) => φ (ν + sh)) (ζ - sh) := by
      have h2 : ContDiffAt ℝ 2 φ ((fun ν : WithLp 2 (F × ℝ) => ν + sh) (ζ - sh)) := by
        simpa only [hzs] using hφ
      exact h2.comp (ζ - sh) ((hTshiftCD sh).contDiffAt)
    have hmin' : IsLocalMinOn (fun ν => g ν - φ (ν + sh))
        (Set.univ : Set (WithLp 2 (F × ℝ))) (ζ - sh) := by
      have h0 : ∀ᶠ ξ in nhdsWithin ζ (Set.univ : Set (WithLp 2 (F × ℝ))),
          g (ζ - sh) - φ ζ ≤ g (ξ - sh) - φ ξ := hmin
      have h1 := (hTten sh ζ).eventually h0
      show ∀ᶠ ν in nhdsWithin (ζ - sh) (Set.univ : Set (WithLp 2 (F × ℝ))),
        g (ζ - sh) - φ (ζ - sh + sh) ≤ g ν - φ (ν + sh)
      rw [hzs]
      filter_upwards [h1] with ν hν
      simpa using hν
    have hres := hg.2.2 (ζ - sh) (Set.mem_univ _) (fun ν => φ (ν + sh)) hφ' hmin'
    rw [hTLimitOp sh φ (ζ - sh), hzs] at hres
    exact hres
  have hTclass : ∀ (sh : WithLp 2 (F × ℝ)) (g : WithLp 2 (F × ℝ) → ℝ),
      IsFitClass C₀ g → IsFitClass C₀ (fun ξ => g (ξ - sh)) := by
    intro sh g hg
    refine ⟨⟨hTsub sh g hg.1.1, hTsuper sh g hg.1.2⟩, ?_⟩
    intro ζ ρ hρ
    obtain ⟨p, a, hf⟩ := hg.2 (ζ - sh) ρ hρ
    exact ⟨p, a, hTfit sh g ζ ρ p a hf⟩
  have hTcent : ∀ (sh : WithLp 2 (F × ℝ)) (g : WithLp 2 (F × ℝ) → ℝ)
      (ζ : WithLp 2 (F × ℝ)),
      IsCenteredAt C₀ g (ζ - sh) → IsCenteredAt C₀ (fun ξ => g (ξ - sh)) ζ :=
    fun sh g ζ h => ⟨h.1, hTfit sh g ζ 1 0 0 h.2⟩
  have hptT : ∀ (y : F) (t c : ℝ),
      (toLp 2 (y, t) : WithLp 2 (F × ℝ)) - toLp 2 ((0 : F), c) = toLp 2 (y, t - c) := by
    intro y t c
    have h : (toLp 2 (y, t) : WithLp 2 (F × ℝ)) - toLp 2 ((0 : F), c)
        = toLp 2 (y - 0, t - c) := rfl
    rw [h, sub_zero]
  have hofs1 : ∀ (c : ℝ) (ζ : WithLp 2 (F × ℝ)),
      (ofLp (ζ - toLp 2 ((0 : F), c))).1 = (ofLp ζ).1 := by
    intro c ζ
    show (ofLp ζ).1 - (0 : F) = (ofLp ζ).1
    rw [sub_zero]
  have hofs2 : ∀ (c : ℝ) (ζ : WithLp 2 (F × ℝ)),
      (ofLp (ζ - toLp 2 ((0 : F), c))).2 = (ofLp ζ).2 - c := fun _ _ => rfl
  have hTJ : ∀ (c kk : ℝ) (g : WithLp 2 (F × ℝ) → ℝ),
      HasJensenBound Set.univ g kk →
      HasJensenBound Set.univ (fun ξ => g (ξ - toLp 2 ((0 : F), c))) kk := by
    intro c kk g hg t _ n θ y x hcfg
    have h := hg (t - c) (Set.mem_univ _) n θ y x hcfg
    simpa only [hptT] using h
  have hTbary : ∀ (c σ : ℝ) (g : WithLp 2 (F × ℝ) → ℝ) (ζ : WithLp 2 (F × ℝ)),
      BaryEnv (fun ξ => g (ξ - toLp 2 ((0 : F), c))) σ ζ
        = BaryEnv g σ (ζ - toLp 2 ((0 : F), c)) := by
    intro c σ g ζ
    rw [BaryEnv, BaryEnv, hofs1 c ζ, hofs2 c ζ]
    congr 1
    ext w
    simp only [hptT]
  -- ===== Step 5: the final frame and the normalized contact =====
  obtain ⟨pst, ast, hfitst⟩ := hvhatclass.2 0 R hR0
  obtain ⟨g, hg⟩ : ∃ f : WithLp 2 (F × ℝ) → ℝ, f = FrameChange vhat 0 R pst ast :=
    ⟨_, rfl⟩
  obtain ⟨hFIclass, hFIfit⟩ := FrameInvariance C₀ vhat hvhatclass 0 R hR0 pst ast
  have hbase0 : (0 : WithLp 2 (F × ℝ))
      + toLp 2 (R • ((ofLp (0 : WithLp 2 (F × ℝ))).1
        + (ofLp (0 : WithLp 2 (F × ℝ))).2 • pst), R * (ofLp (0 : WithLp 2 (F × ℝ))).2)
      = 0 := by
    simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_smul, add_zero, smul_zero,
      mul_zero, hzero]
  have hgclass : IsFitClass C₀ g := by rw [hg]; exact hFIclass
  have hg0 : g 0 = 0 := by
    rw [hg]
    simp only [FrameChange]
    rw [hbase0]
    simp
  have hgfit : IsFit C₀ g 0 1 0 0 := by
    have h := hFIfit 0 1 pst ast (by rw [hbase0, mul_one]; exact hfitst)
    rw [hg]
    simpa using h
  have hgcent : IsCenteredAt C₀ g 0 := ⟨hg0, hgfit⟩
  have hgJ : HasJensenBound Set.univ g κ := by
    rw [hg]
    exact hJframe vhat 0 R hR0 pst ast hvhatJ
  -- (F2) at `σ = 1` and `(y,s) = (0,0)`: the envelope gap scales by `1/R`.
  have hz1 : (ofLp (0 : WithLp 2 (F × ℝ))).1 = (0 : F) := by simp
  have hz2 : (ofLp (0 : WithLp 2 (F × ℝ))).2 = (0 : ℝ) := by simp
  have hTmap : ∀ y : F,
      (ofLp (0 : WithLp 2 (F × ℝ))).1 + R • (y + (0 : ℝ) • pst) = R • y := by
    intro y
    rw [hz1]
    simp
  have hTtime : (ofLp (0 : WithLp 2 (F × ℝ))).2 + R * (0 : ℝ) = 0 := by
    rw [hz2]
    ring
  obtain ⟨hFCC1, hFCC2, hFCC3, hFCC4⟩ := FrameConfigCovariance vhat 0 R hR0 pst ast 0
  have hFCC1' : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (xb : F),
      IsBaryConfig n θ (fun i => R • y i) (R • xb) ↔ IsBaryConfig n θ y xb := by
    intro n θ y xb
    simpa only [hTmap] using hFCC1 n θ y xb
  have hFCC2' : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (xb : F),
      BaryRadius n θ (fun i => R • y i) (R • xb) = R * BaryRadius n θ y xb := by
    intro n θ y xb
    simpa only [hTmap] using hFCC2 n θ y xb
  have hFCC3' : ∀ Y : F, ∃ y : F, R • y = Y := by
    intro Y
    obtain ⟨y, hy⟩ := hFCC3 Y
    exact ⟨y, by rw [← hTmap y]; exact hy⟩
  have hFCC4' : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (xb : F),
      IsBaryConfig n θ y xb →
      (∑ i, θ i * g (toLp 2 (y i, (0 : ℝ)))) - g (toLp 2 (xb, (0 : ℝ)))
        = (1 / R) * ((∑ i, θ i * vhat (toLp 2 (R • y i, (0 : ℝ))))
            - vhat (toLp 2 (R • xb, (0 : ℝ)))) := by
    intro n θ y xb hcfg
    rw [hg]
    simpa only [hTmap, hTtime] using hFCC4 n θ y xb hcfg
  have hgcont : ContinuousOn g
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hgclass.1.1.2.1
  have hggrow : SubquadraticGrowth (Set.univ : Set ℝ) g :=
    hsubq 0 (Or.inl rfl) g hgclass hgcent
  obtain ⟨-, -, hCBg⟩ := EnvelopeCompetitorBounds (F := F) Set.univ g hgcont hggrow
  have hF2 : R * BaryEnv g 1 0 = BaryEnv vhat R 0 := by
    refine le_antisymm ?_ ?_
    · have hext := (hCBg 1 0 one_pos (Set.mem_univ _)).2 (BaryEnv vhat R 0 / R) ?_
      · have h := mul_le_mul_of_nonneg_left hext hR0.le
        rwa [show R * (BaryEnv vhat R 0 / R) = BaryEnv vhat R 0 from by field_simp] at h
      · intro n θ y hcfg
        rw [hz1] at hcfg
        rw [hz1, hz2]
        have h4 := hFCC4' n θ y 0 hcfg
        rw [smul_zero, hzero, hg0, hvhatcent.1, sub_zero, sub_zero] at h4
        have hcfg2 : IsBaryConfig n θ (fun i => R • y i)
            (ofLp (0 : WithLp 2 (F × ℝ))).1 := by
          rw [hz1]
          have h := (hFCC1' n θ y 0).mpr hcfg
          rwa [smul_zero] at h
        have hdom := (hCB3 R 0 hR0 (Set.mem_univ _)).1 n θ (fun i => R • y i) hcfg2
        rw [hz1, hz2] at hdom
        have hr2 : BaryRadius n θ (fun i => R • y i) (0 : F)
            = R * BaryRadius n θ y 0 := by
          have h := hFCC2' n θ y 0
          rwa [smul_zero] at h
        rw [hr2, show (R * BaryRadius n θ y (0 : F)) ^ 2 / (2 * R)
            = R * BaryRadius n θ y (0 : F) ^ 2 / 2 from by field_simp] at hdom
        rw [le_div_iff₀ hR0]
        have hS : (∑ i, θ i * g (toLp 2 (y i, (0 : ℝ)))) * R
            = ∑ i, θ i * vhat (toLp 2 (R • y i, (0 : ℝ))) := by
          rw [h4]
          field_simp
        rw [show ((∑ i, θ i * g (toLp 2 (y i, (0 : ℝ))))
              - BaryRadius n θ y (0 : F) ^ 2 / (2 * 1)) * R
            = (∑ i, θ i * g (toLp 2 (y i, (0 : ℝ)))) * R
              - R * BaryRadius n θ y (0 : F) ^ 2 / 2 from by ring, hS]
        linarith [hdom]
    · refine (hCB3 R 0 hR0 (Set.mem_univ _)).2 (R * BaryEnv g 1 0) ?_
      intro n θ Y hcfg
      rw [hz1] at hcfg
      rw [hz1, hz2]
      choose yy hyy using fun i : Fin n => hFCC3' (Y i)
      have hYfun : (fun i => R • yy i) = Y := funext hyy
      have hcfgy : IsBaryConfig n θ yy (0 : F) := by
        refine (hFCC1' n θ yy 0).mp ?_
        rw [smul_zero, hYfun]
        exact hcfg
      have hdomg := (hCBg 1 0 one_pos (Set.mem_univ _)).1 n θ yy (by rw [hz1]; exact hcfgy)
      rw [hz1, hz2] at hdomg
      have h4 := hFCC4' n θ yy 0 hcfgy
      rw [smul_zero, hzero, hg0, hvhatcent.1, sub_zero, sub_zero] at h4
      have hr2 : BaryRadius n θ Y (0 : F) = R * BaryRadius n θ yy 0 := by
        have h := hFCC2' n θ yy 0
        rwa [smul_zero, hYfun] at h
      have hvv : (∑ i, θ i * vhat (toLp 2 (Y i, (0 : ℝ))))
          = R * (∑ i, θ i * g (toLp 2 (yy i, (0 : ℝ)))) := by
        have e : (∑ i, θ i * vhat (toLp 2 (Y i, (0 : ℝ))))
            = ∑ i, θ i * vhat (toLp 2 (R • yy i, (0 : ℝ))) :=
          Finset.sum_congr rfl (fun i _ => by rw [hyy i])
        rw [e, h4]
        field_simp
      rw [hr2, hvv, show (R * BaryRadius n θ yy (0 : F)) ^ 2 / (2 * R)
          = R * BaryRadius n θ yy (0 : F) ^ 2 / 2 from by field_simp]
      have h := mul_le_mul_of_nonneg_left hdomg hR0.le
      rw [show R * ((∑ i, θ i * g (toLp 2 (yy i, (0 : ℝ))))
            - BaryRadius n θ yy (0 : F) ^ 2 / (2 * 1))
          = R * (∑ i, θ i * g (toLp 2 (yy i, (0 : ℝ))))
            - R * BaryRadius n θ yy (0 : F) ^ 2 / 2 from by ring] at h
      linarith [h]
  -- the normalized contact for `g`, hence for the final function
  have hgapg : BaryEnv g 1 0 = κ ^ 2 / 2 := by
    rw [hattain] at hF2
    have hRκ : R * κ = 1 := by
      rw [hR]
      field_simp
    have h3 : κ * (R * BaryEnv g 1 0) = κ * (κ / 2) := by rw [hF2]
    rw [show κ * (R * BaryEnv g 1 0) = R * κ * BaryEnv g 1 0 from by ring, hRκ,
      one_mul] at h3
    rw [h3]
    ring
  -- the final function: the frame change followed by the unit time translation
  obtain ⟨vfin, hvfin⟩ : ∃ f : WithLp 2 (F × ℝ) → ℝ,
      f = fun ζ => g (ζ - toLp 2 ((0 : F), (1 : ℝ))) := ⟨_, rfl⟩
  have hshift0 : (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))
      - toLp 2 ((0 : F), (1 : ℝ)) = 0 := sub_self _
  have hvfinclass : IsFitClass C₀ vfin := by
    rw [hvfin]
    exact hTclass _ g hgclass
  have hvfincent : IsCenteredAt C₀ vfin (toLp 2 ((0 : F), (1 : ℝ))) := by
    rw [hvfin]
    refine hTcent _ g _ ?_
    rw [hshift0]
    exact hgcent
  have hvfinJ : HasJensenBound Set.univ vfin κ := by
    rw [hvfin]
    exact hTJ 1 κ g hgJ
  have hvfin0 : vfin (toLp 2 ((0 : F), (1 : ℝ))) = 0 := hvfincent.1
  have hvfinbary : BaryEnv vfin 1 (toLp 2 ((0 : F), (1 : ℝ))) = κ ^ 2 / 2 := by
    rw [hvfin, hTbary 1 1 g, hshift0, hgapg]
  have hstartime : (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 = 1 := rfl
  have hcontact : ContactEnv vfin κ (toLp 2 ((0 : F), (1 : ℝ))) = 0 := by
    rw [ContactEnv, hstartime, hvfinbary]
    ring
  -- ===== Step 6: the contact envelope =====
  -- the six properties of `W = C_t v - κ²t/2` are `ContactEnvelopeProperties`; the one
  -- consequence of the fit class prepared here is the growth that Step 7 also reads.
  have hvfingrow : SubquadraticGrowth (Set.univ : Set ℝ) vfin :=
    hsubq (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) vfin hvfinclass hvfincent
  obtain ⟨hWsand, hWcont, hWconc, hWgrow, hWsub, hWgap⟩ :=
    ContactEnvelopeProperties C₀ κ vfin hκ0 hvfinclass hvfinJ hvfingrow
  -- ===== Step 7: the slope at the contact =====
  -- the slope limit at the contact is `ContactEnvelopeSlopeLimit`: it consumes four of
  -- Step 6's six conclusions and returns `H` with the two conjuncts the assembly needs.
  obtain ⟨H, hHeq, htend⟩ :=
    ContactEnvelopeSlopeLimit C₀ κ hC₀ vfin hκ0 hvfinclass hvfincent hvfinJ hvfingrow
      hcontact hWcont hWgrow hWsub hWsand
  -- ===== assembly: the fourteen conjuncts =====
  exact ⟨κ, H, vfin, hκ0, hvfinclass, hvfincent, hvfinJ, hWcont, hWgrow, hWsub,
    hWsand, hcontact, hvfin0, hWconc, hWgap, hHeq, htend⟩
