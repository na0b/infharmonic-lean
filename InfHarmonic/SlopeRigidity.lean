module

public import InfHarmonic.IsFitClass
public import InfHarmonic.FitClassGrowth
public import InfHarmonic.FarOptimizerBound
public import InfHarmonic.IsSpaceTimeAffine
public import InfHarmonic.EnvSlopeP
public import InfHarmonic.EnvSlopeM
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.EnvHamiltonianSolution
public import InfHarmonic.FrameInvariance
public import InfHarmonic.CenteredGrowth
public import InfHarmonic.EnvelopeCompetitorBounds

@[expose] public section
set_option maxHeartbeats 400000
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 7.1, rigidity from constant envelope slopes: a member of
`A_{m,C₀}` whose two envelope slopes at one point are equal to one constant at
every length is affine. -/
theorem SlopeRigidity (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : IsFitClass C₀ v) (b : F) (t₀ B : ℝ)
    (hslopes : ∀ l : ℝ, 0 < l →
      EnvSlopeP v l (toLp 2 (b, t₀)) = B ∧ EnvSlopeM v l (toLp 2 (b, t₀)) = B) :
    IsSpaceTimeAffine v := by
  classical
  -- Step 1: translation to the origin, and the reduction to `V`.
  obtain ⟨V, hV⟩ : ∃ g : WithLp 2 (F × ℝ) → ℝ,
      g = FrameChange v (toLp 2 (b, t₀)) 1 0 0 := ⟨_, rfl⟩
  have hVform : ∀ z : WithLp 2 (F × ℝ),
      V z = v (toLp 2 (b, t₀) + z) - v (toLp 2 (b, t₀)) := by
    intro z
    rw [hV]
    simp only [FrameChange, one_smul, one_mul, div_one, smul_zero, add_zero,
      inner_zero_left, norm_zero, sub_zero]
    rw [Prod.mk.eta, toLp_ofLp]
    simp
  have hVclass : IsFitClass C₀ V := by
    rw [hV]
    exact (FrameInvariance C₀ v hv (toLp 2 (b, t₀)) 1 one_pos 0 0).1
  have hV0 : V 0 = 0 := by
    have h := hVform 0
    rw [add_zero] at h
    linarith [h]
  -- the reduction: an affine `V` makes `v` affine
  have hreduce : IsSpaceTimeAffine V → IsSpaceTimeAffine v := by
    intro ⟨q, β, γ, hVaff⟩
    refine ⟨q, β, γ - inner ℝ q b - β * t₀ + v (toLp 2 (b, t₀)), fun z => ?_⟩
    have hz : v z = V (z - toLp 2 (b, t₀)) + v (toLp 2 (b, t₀)) := by
      have h := hVform (z - toLp 2 (b, t₀))
      rw [show toLp 2 (b, t₀) + (z - toLp 2 (b, t₀)) = z from by abel] at h
      linarith [h]
    have hc1 : (ofLp (z - toLp 2 (b, t₀))).1 = (ofLp z).1 - b := by simp
    have hc2 : (ofLp (z - toLp 2 (b, t₀))).2 = (ofLp z).2 - t₀ := by simp
    rw [hz, hVaff, hc1, hc2, inner_sub_right]
    ring
  -- Steps 2 to 4: the box bounds and the subquadratic growth of `V` and of `v`
  obtain ⟨CV, hCV0, hVbox0, hVgrow⟩ := FitClassGrowth C₀ hC₀ V hVclass
  obtain ⟨Cv, hCv0, hvbox0, hvgrow⟩ := FitClassGrowth C₀ hC₀ v hv
  have hVbox : ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
      ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
      |V z| ≤ CV * K * (1 + Real.log K) ^ 2 := by
    intro K hK z hz1 hz2
    have h := hVbox0 K hK z hz1 hz2
    rw [hV0, sub_zero] at h
    exact h
  -- Step 7 is available for `V` at every center, from the box bound
  have hfar : ∀ (x : F) (t : ℝ), ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, 1 ≤ l → ∀ y : F,
      V (toLp 2 (x, t + l)) ≤ V (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l) →
      ‖y‖ ≤ C * l * (1 + Real.log l) ^ 2 :=
    fun x t => FarOptimizerBound CV hCV0 V hVbox x t
  -- the pointwise relation between `V` and `v` in coordinates
  have hcomp : ∀ (y : F) (s : ℝ),
      V (toLp 2 (y, s)) = v (toLp 2 (b + y, t₀ + s)) - v (toLp 2 (b, t₀)) := by
    intro y s
    have h := hVform (toLp 2 (y, s))
    have hadd : (toLp 2 (b, t₀) : WithLp 2 (F × ℝ)) + toLp 2 (y, s)
        = toLp 2 (b + y, t₀ + s) := by
      rw [← toLp_add]
      rfl
    rw [hadd] at h
    exact h
  have hcompN : ∀ (y : F) (l : ℝ),
      V (toLp 2 (y, -l)) = v (toLp 2 (b + y, t₀ - l)) - v (toLp 2 (b, t₀)) := by
    intro y l
    have h := hcomp y (-l)
    rw [show t₀ + -l = t₀ - l from by ring] at h
    exact h
  -- Step 5: the envelope slopes of `V` at the origin equal `B`
  have hVcont : ContinuousOn V ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hVclass.1.1.2.1
  have hvcont : ContinuousOn v ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hv.1.1.2.1
  obtain ⟨hVP, hVM, -⟩ :=
    EnvelopeCompetitorBounds (F := F) Set.univ V hVcont hVgrow
  obtain ⟨hvP, hvM, -⟩ :=
    EnvelopeCompetitorBounds (F := F) Set.univ v hvcont hvgrow
  have hPtransfer : ∀ l : ℝ, 0 < l →
      QuadEnvP V l 0 = QuadEnvP v l (toLp 2 (b, t₀)) - v (toLp 2 (b, t₀)) := by
    intro l hl
    have hVdom := (hVP l 0 hl (Set.mem_univ _) (Set.mem_univ _)).1
    have hVext := (hVP l 0 hl (Set.mem_univ _) (Set.mem_univ _)).2
    have hvdom := (hvP l (toLp 2 (b, t₀)) hl (Set.mem_univ _) (Set.mem_univ _)).1
    have hvext := (hvP l (toLp 2 (b, t₀)) hl (Set.mem_univ _) (Set.mem_univ _)).2
    refine le_antisymm (hVext _ (fun y => ?_)) ?_
    · have h1 := hvdom (b + y)
      simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_add,
        sub_zero, add_sub_cancel_left] at h1 ⊢
      rw [hcomp y l]
      linarith [h1]
    · have h5 : QuadEnvP v l (toLp 2 (b, t₀)) ≤ QuadEnvP V l 0 + v (toLp 2 (b, t₀)) := by
        refine hvext _ (fun y' => ?_)
        have h1 := hVdom (y' - b)
        simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_add,
          sub_zero] at h1 ⊢
        rw [hcomp (y' - b) l, show b + (y' - b) = y' from by abel] at h1
        linarith [h1]
      linarith [h5]
  have hMtransfer : ∀ l : ℝ, 0 < l →
      QuadEnvM V l 0 = QuadEnvM v l (toLp 2 (b, t₀)) - v (toLp 2 (b, t₀)) := by
    intro l hl
    have hVdom := (hVM l 0 hl (Set.mem_univ _) (Set.mem_univ _)).1
    have hVext := (hVM l 0 hl (Set.mem_univ _) (Set.mem_univ _)).2
    have hvdom := (hvM l (toLp 2 (b, t₀)) hl (Set.mem_univ _) (Set.mem_univ _)).1
    have hvext := (hvM l (toLp 2 (b, t₀)) hl (Set.mem_univ _) (Set.mem_univ _)).2
    refine le_antisymm ?_ (hVext _ (fun y => ?_))
    · have h5 : QuadEnvM V l 0 + v (toLp 2 (b, t₀)) ≤ QuadEnvM v l (toLp 2 (b, t₀)) := by
        refine hvext _ (fun y' => ?_)
        have h1 := hVdom (y' - b)
        simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_sub,
          sub_zero] at h1 ⊢
        rw [hcompN (y' - b) l, show b + (y' - b) = y' from by abel] at h1
        linarith [h1]
      linarith [h5]
    · have h1 := hvdom (b + y)
      simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_sub,
        sub_zero, add_sub_cancel_left] at h1 ⊢
      rw [hcompN y l]
      linarith [h1]
  have hVslopes : ∀ l : ℝ, 0 < l →
      EnvSlopeP V l 0 = B ∧ EnvSlopeM V l 0 = B := by
    intro l hl
    obtain ⟨hsP, hsM⟩ := hslopes l hl
    refine ⟨?_, ?_⟩
    · rw [EnvSlopeP] at hsP ⊢
      rw [hPtransfer l hl, hV0]
      rw [← hsP]
      ring_nf
    · rw [EnvSlopeM] at hsM ⊢
      rw [hMtransfer l hl, hV0]
      rw [← hsM]
      ring_nf
  -- Step 6: the future paraboloid
  have hparab : ∀ (y : F) (t : ℝ), 0 < t →
      V (toLp 2 (y, t)) ≤ B * t + ‖y‖ ^ 2 / (2 * t) := by
    intro y t ht
    have hPt : QuadEnvP V t 0 = B * t := by
      have h := (hVslopes t ht).1
      rw [EnvSlopeP, hV0, sub_zero, div_eq_iff (ne_of_gt ht)] at h
      linarith [h]
    have hdom := (hVP t 0 ht (Set.mem_univ _) (Set.mem_univ _)).1 y
    simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_add, sub_zero] at hdom
    rw [hPt] at hdom
    linarith [hdom]
  -- Step 8: the forward slope of `V` is at most `B` at every center and length
  obtain ⟨hattP, hattM, -, -, -, -⟩ :=
    QuadEnvAttained (F := F) Set.univ isOpen_univ V hVcont hVgrow
  obtain ⟨hslmono, -, -, -⟩ :=
    EnvHamiltonianSolution (F := F) Set.univ isOpen_univ V hVcont hVgrow hVclass.1
  -- the elementary logarithm bound `(1 + log u)^4 ≤ 6561 √u`
  have hlog8 : ∀ u : ℝ, 1 ≤ u → (1 + Real.log u) ^ 4 ≤ 6561 * Real.sqrt u := by
    intro u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hs1 : (1 : ℝ) ≤ Real.sqrt u := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hu
    have hs2 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt u) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hs1
    have hs3 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (Real.sqrt u)) := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hs2
    have hlogu : Real.log u = 8 * Real.log (Real.sqrt (Real.sqrt (Real.sqrt u))) := by
      rw [Real.log_sqrt (Real.sqrt_nonneg _), Real.log_sqrt (Real.sqrt_nonneg _),
        Real.log_sqrt hu0.le]
      ring
    have hle : Real.log (Real.sqrt (Real.sqrt (Real.sqrt u)))
        ≤ Real.sqrt (Real.sqrt (Real.sqrt u)) := by
      have := Real.log_le_sub_one_of_pos (show (0:ℝ) < Real.sqrt (Real.sqrt (Real.sqrt u)) by
        linarith)
      linarith
    have hM : 1 + Real.log u ≤ 9 * Real.sqrt (Real.sqrt (Real.sqrt u)) := by
      rw [hlogu]
      linarith [hle, hs3]
    have hMnn : (0 : ℝ) ≤ 1 + Real.log u := by
      have : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu
      linarith
    have hpow : (1 + Real.log u) ^ 4
        ≤ (9 * Real.sqrt (Real.sqrt (Real.sqrt u))) ^ 4 :=
      pow_le_pow_left₀ hMnn hM 4
    have hq1 : Real.sqrt (Real.sqrt (Real.sqrt u)) ^ 2 = Real.sqrt (Real.sqrt u) :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hq2 : Real.sqrt (Real.sqrt u) ^ 2 = Real.sqrt u :=
      Real.sq_sqrt (Real.sqrt_nonneg _)
    have hq3 : (9 * Real.sqrt (Real.sqrt (Real.sqrt u))) ^ 4 = 6561 * Real.sqrt u := by
      have : (9 * Real.sqrt (Real.sqrt (Real.sqrt u))) ^ 4
          = 6561 * (Real.sqrt (Real.sqrt (Real.sqrt u)) ^ 2) ^ 2 := by ring
      rw [this, hq1, hq2]
    linarith [hpow, hq3]
  -- the cost estimate, as a statement about plain reals
  have hcostbd : ∀ nY nX tt LL CF M ip : ℝ,
      0 < LL → LL / 2 ≤ tt + LL → 0 ≤ nY → 0 ≤ nX → 0 ≤ CF → 1 ≤ M →
      nY ≤ CF * LL * M ^ 2 → ip ≤ nY * nX →
      -tt * nY ^ 2 + 2 * (tt + LL) * ip - (tt + LL) * nX ^ 2
        ≤ (|tt| * CF ^ 2 + nX * CF) * M ^ 4 * (2 * LL * (tt + LL)) := by
    intro nY nX tt LL CF M ip hLL hhalf hnY hnX hCF hM hbd hip
    have htL : 0 < tt + LL := by linarith
    have hM2 : (1 : ℝ) ≤ M ^ 2 := by nlinarith [hM]
    have hM4 : M ^ 2 ≤ M ^ 4 := by nlinarith [hM, hM2]
    have hM4nn : (0 : ℝ) ≤ M ^ 4 := by positivity
    have hsq : nY ^ 2 ≤ CF ^ 2 * LL ^ 2 * M ^ 4 := by
      have h1 : nY ^ 2 ≤ (CF * LL * M ^ 2) ^ 2 := pow_le_pow_left₀ hnY hbd 2
      nlinarith [h1]
    have hLL2 : LL ^ 2 ≤ 2 * LL * (tt + LL) := by nlinarith [hhalf, hLL]
    have habs : -tt ≤ |tt| := neg_le_abs tt
    have habsnn : (0 : ℝ) ≤ |tt| := abs_nonneg tt
    have hterm1 : -tt * nY ^ 2 ≤ |tt| * CF ^ 2 * M ^ 4 * (2 * LL * (tt + LL)) := by
      have h1 : -tt * nY ^ 2 ≤ |tt| * nY ^ 2 := by nlinarith [habs, sq_nonneg nY]
      have h2 : |tt| * nY ^ 2 ≤ |tt| * (CF ^ 2 * LL ^ 2 * M ^ 4) :=
        mul_le_mul_of_nonneg_left hsq habsnn
      have h3 : |tt| * (CF ^ 2 * LL ^ 2 * M ^ 4)
          ≤ |tt| * (CF ^ 2 * (2 * LL * (tt + LL)) * M ^ 4) := by
        have h4 : CF ^ 2 * LL ^ 2 * M ^ 4 ≤ CF ^ 2 * (2 * LL * (tt + LL)) * M ^ 4 := by
          have h5 : CF ^ 2 * LL ^ 2 ≤ CF ^ 2 * (2 * LL * (tt + LL)) :=
            mul_le_mul_of_nonneg_left hLL2 (by positivity)
          exact mul_le_mul_of_nonneg_right h5 hM4nn
        exact mul_le_mul_of_nonneg_left h4 habsnn
      have h6 : |tt| * (CF ^ 2 * (2 * LL * (tt + LL)) * M ^ 4)
          = |tt| * CF ^ 2 * M ^ 4 * (2 * LL * (tt + LL)) := by ring
      linarith [h1, h2, h3, h6]
    have hterm2 : 2 * (tt + LL) * ip ≤ nX * CF * M ^ 4 * (2 * LL * (tt + LL)) := by
      have h1 : 2 * (tt + LL) * ip ≤ 2 * (tt + LL) * (nY * nX) := by
        have := mul_le_mul_of_nonneg_left hip (show (0:ℝ) ≤ 2 * (tt + LL) by linarith)
        linarith
      have h2 : nY * nX ≤ CF * LL * M ^ 2 * nX := mul_le_mul_of_nonneg_right hbd hnX
      have h3 : 2 * (tt + LL) * (nY * nX) ≤ 2 * (tt + LL) * (CF * LL * M ^ 2 * nX) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      have h4 : 2 * (tt + LL) * (CF * LL * M ^ 2 * nX)
          = nX * CF * M ^ 2 * (2 * LL * (tt + LL)) := by ring
      have h5 : nX * CF * M ^ 2 * (2 * LL * (tt + LL))
          ≤ nX * CF * M ^ 4 * (2 * LL * (tt + LL)) := by
        have h6 : nX * CF * M ^ 2 ≤ nX * CF * M ^ 4 :=
          mul_le_mul_of_nonneg_left hM4 (by positivity)
        exact mul_le_mul_of_nonneg_right h6 (by positivity)
      linarith [h1, h3, h4, h5]
    have hterm3 : -((tt + LL) * nX ^ 2) ≤ 0 := by
      have : (0 : ℝ) ≤ (tt + LL) * nX ^ 2 := by positivity
      linarith
    have hsum : (|tt| * CF ^ 2 + nX * CF) * M ^ 4 * (2 * LL * (tt + LL))
        = |tt| * CF ^ 2 * M ^ 4 * (2 * LL * (tt + LL))
          + nX * CF * M ^ 4 * (2 * LL * (tt + LL)) := by ring
    linarith [hterm1, hterm2, hterm3, hsum]
  have hslopeB : ∀ (x : F) (t l : ℝ), 0 < l → EnvSlopeP V l (toLp 2 (x, t)) ≤ B := by
    intro x t l hl
    obtain ⟨Cf, hCf0, hfarx⟩ := hfar x t
    obtain ⟨D, hD⟩ : ∃ d : ℝ, d = |t| * Cf ^ 2 + ‖x‖ * Cf + 1 := ⟨_, rfl⟩
    have hD0 : 0 < D := by
      rw [hD]
      have h1 : (0 : ℝ) ≤ |t| * Cf ^ 2 := by positivity
      have h2 : (0 : ℝ) ≤ ‖x‖ * Cf := by positivity
      linarith
    obtain ⟨Aa, hAa⟩ : ∃ a : ℝ, a = |B * t| + |V (toLp 2 (x, t))| := ⟨_, rfl⟩
    have hAa0 : 0 ≤ Aa := by
      rw [hAa]
      linarith [abs_nonneg (B * t), abs_nonneg (V (toLp 2 (x, t)))]
    -- the bound at a large length
    have hbig : ∀ L : ℝ, 1 ≤ L → 2 * |t| + 1 ≤ L →
        EnvSlopeP V L (toLp 2 (x, t)) ≤ B + (Aa + D * (6561 * Real.sqrt L)) / L := by
      intro L hL1 hLt
      have hL0 : (0 : ℝ) < L := by linarith
      have hhalf : L / 2 ≤ t + L := by
        have := abs_nonneg t
        have h2 : -|t| ≤ t := neg_abs_le t
        linarith
      have htL : (0 : ℝ) < t + L := by linarith
      obtain ⟨yL, hyL⟩ := hattP L (toLp 2 (x, t)) hL0 (Set.mem_univ _) (Set.mem_univ _)
      dsimp only at hyL
      have hdom := (hVP L (toLp 2 (x, t)) hL0 (Set.mem_univ _) (Set.mem_univ _)).1 x
      simp only [sub_self, norm_zero] at hdom
      have hbeat : V (toLp 2 (x, t + L))
          ≤ V (toLp 2 (yL, t + L)) - ‖yL - x‖ ^ 2 / (2 * L) := by
        rw [← hyL]
        simpa using hdom
      have hyLbd := hfarx L hL1 yL hbeat
      have hpar := hparab yL (t + L) htL
      -- the cost difference
      have hip : (inner ℝ yL x : ℝ) ≤ ‖yL‖ * ‖x‖ := real_inner_le_norm yL x
      have hMge : (1 : ℝ) ≤ 1 + Real.log L := by
        have : (0 : ℝ) ≤ Real.log L := Real.log_nonneg hL1
        linarith
      have hcost := hcostbd ‖yL‖ ‖x‖ t L Cf (1 + Real.log L) (inner ℝ yL x)
        hL0 hhalf (norm_nonneg _) (norm_nonneg _) hCf0.le hMge hyLbd hip
      have hexp : ‖yL‖ ^ 2 / (2 * (t + L)) - ‖yL - x‖ ^ 2 / (2 * L)
          = (-t * ‖yL‖ ^ 2 + 2 * (t + L) * (inner ℝ yL x : ℝ) - (t + L) * ‖x‖ ^ 2)
            / (2 * L * (t + L)) := by
        rw [norm_sub_sq_real]
        field_simp
        ring
      have hdiff : ‖yL‖ ^ 2 / (2 * (t + L)) - ‖yL - x‖ ^ 2 / (2 * L)
          ≤ (|t| * Cf ^ 2 + ‖x‖ * Cf) * (1 + Real.log L) ^ 4 := by
        rw [hexp, div_le_iff₀ (by positivity : (0:ℝ) < 2 * L * (t + L))]
        exact hcost
      have hDbd : (|t| * Cf ^ 2 + ‖x‖ * Cf) * (1 + Real.log L) ^ 4
          ≤ D * (6561 * Real.sqrt L) := by
        have h1 : (1 + Real.log L) ^ 4 ≤ 6561 * Real.sqrt L := hlog8 L hL1
        have h2 : (|t| * Cf ^ 2 + ‖x‖ * Cf) ≤ D := by rw [hD]; linarith
        have h3 : (0 : ℝ) ≤ |t| * Cf ^ 2 + ‖x‖ * Cf := by positivity
        have h4 : (0 : ℝ) ≤ 6561 * Real.sqrt L := by positivity
        calc (|t| * Cf ^ 2 + ‖x‖ * Cf) * (1 + Real.log L) ^ 4
            ≤ (|t| * Cf ^ 2 + ‖x‖ * Cf) * (6561 * Real.sqrt L) :=
              mul_le_mul_of_nonneg_left h1 h3
          _ ≤ D * (6561 * Real.sqrt L) := mul_le_mul_of_nonneg_right h2 h4
      -- assemble
      have hQ : QuadEnvP V L (toLp 2 (x, t)) ≤ B * (t + L) + D * (6561 * Real.sqrt L) := by
        rw [hyL]
        have h1 : V (toLp 2 (yL, t + L)) - ‖yL - x‖ ^ 2 / (2 * L)
            ≤ B * (t + L) + (‖yL‖ ^ 2 / (2 * (t + L)) - ‖yL - x‖ ^ 2 / (2 * L)) := by
          linarith [hpar]
        linarith [h1, hdiff, hDbd]
      rw [EnvSlopeP, div_le_iff₀ hL0]
      have hVx : -V (toLp 2 (x, t)) ≤ |V (toLp 2 (x, t))| := neg_le_abs _
      have hBt : B * t ≤ |B * t| := le_abs_self _
      have hrw : (B + (Aa + D * (6561 * Real.sqrt L)) / L) * L
          = B * L + (Aa + D * (6561 * Real.sqrt L)) := by
        field_simp
      rw [hrw, hAa]
      linarith [hQ, hVx, hBt]
    -- let `L` tend to infinity
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨L, hL1, hLt, hLl, hLA, hLD⟩ : ∃ L : ℝ, 1 ≤ L ∧ 2 * |t| + 1 ≤ L ∧ l ≤ L ∧
        Aa / L ≤ ε / 2 ∧ D * (6561 * Real.sqrt L) / L ≤ ε / 2 := by
      obtain ⟨L, hLmax⟩ : ∃ L : ℝ, L = max (max 1 (2 * |t| + 1))
          (max l (max (2 * Aa / ε) ((2 * 6561 * D / ε) ^ 2))) := ⟨_, rfl⟩
      have h1 : (1 : ℝ) ≤ L := by
        rw [hLmax]; exact le_trans (le_max_left _ _) (le_max_left _ _)
      have h2 : 2 * |t| + 1 ≤ L := by
        rw [hLmax]; exact le_trans (le_max_right _ _) (le_max_left _ _)
      have h3 : l ≤ L := by
        rw [hLmax]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      have h4 : 2 * Aa / ε ≤ L := by
        rw [hLmax]
        exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)
      have h5 : (2 * 6561 * D / ε) ^ 2 ≤ L := by
        rw [hLmax]
        exact le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)
      have hL0 : (0 : ℝ) < L := by linarith
      refine ⟨L, h1, h2, h3, ?_, ?_⟩
      · rw [div_le_iff₀ hL0]
        rw [div_le_iff₀ hε] at h4
        linarith
      · have hsq : 2 * 6561 * D / ε ≤ Real.sqrt L := by
          have hnn : (0 : ℝ) ≤ 2 * 6561 * D / ε := by positivity
          rw [show (2 * 6561 * D / ε) = Real.sqrt ((2 * 6561 * D / ε) ^ 2) from by
            rw [Real.sqrt_sq hnn]]
          exact Real.sqrt_le_sqrt h5
        have hsL : (0 : ℝ) < Real.sqrt L := Real.sqrt_pos.mpr hL0
        have hmul : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
        rw [div_le_iff₀ hL0]
        rw [div_le_iff₀ hε] at hsq
        nlinarith [hsq, hsL, hmul, hD0, hε]
    have hmonoL := (hslmono (toLp 2 (x, t)) l L hl hLl (fun σ _ => Set.mem_univ _)).1
    have hb := hbig L hL1 hLt
    have hsplit : (Aa + D * (6561 * Real.sqrt L)) / L
        = Aa / L + D * (6561 * Real.sqrt L) / L := by ring
    rw [hsplit] at hb
    linarith [hmonoL, hb, hLA, hLD]
  -- Step 9: the global directed comparison
  have hdirected : ∀ (x y : F) (t l : ℝ), 0 < l →
      V (toLp 2 (y, t + l)) - V (toLp 2 (x, t)) ≤ B * l + ‖y - x‖ ^ 2 / (2 * l) := by
    intro x y t l hl
    have hdom := (hVP l (toLp 2 (x, t)) hl (Set.mem_univ _) (Set.mem_univ _)).1 y
    dsimp only at hdom
    have hsl := hslopeB x t l hl
    rw [EnvSlopeP, div_le_iff₀ hl] at hsl
    linarith [hdom, hsl]
  -- Step 10: equality points and a single velocity
  have hfwd : ∀ l : ℝ, 0 < l → ∃ q : F,
      V (toLp 2 (l • q, l)) = B * l + l * ‖q‖ ^ 2 / 2 := by
    intro l hl
    obtain ⟨y, hy⟩ := hattP l 0 hl (Set.mem_univ _) (Set.mem_univ _)
    simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_add, sub_zero] at hy
    have hPl : QuadEnvP V l 0 = B * l := by
      have h := (hVslopes l hl).1
      rw [EnvSlopeP, hV0, sub_zero, div_eq_iff (ne_of_gt hl)] at h
      linarith [h]
    refine ⟨l⁻¹ • y, ?_⟩
    have hsm : l • (l⁻¹ • y) = y := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hl), one_smul]
    rw [hsm]
    have hn : ‖l⁻¹ • y‖ ^ 2 = ‖y‖ ^ 2 / l ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl)]
      field_simp
    rw [hn]
    have hVy : V (toLp 2 (y, l)) = B * l + ‖y‖ ^ 2 / (2 * l) := by
      rw [hPl] at hy
      linarith [hy]
    rw [hVy]
    field_simp
  have hbwd : ∀ r : ℝ, 0 < r → ∃ q : F,
      V (toLp 2 (-(r • q), -r)) = -(B * r) - r * ‖q‖ ^ 2 / 2 := by
    intro r hr
    obtain ⟨y, hy⟩ := hattM r 0 hr (Set.mem_univ _) (Set.mem_univ _)
    simp only [ofLp_zero, Prod.fst_zero, Prod.snd_zero, zero_sub, sub_zero] at hy
    have hMr : QuadEnvM V r 0 = -(B * r) := by
      have h := (hVslopes r hr).2
      rw [EnvSlopeM, hV0, zero_sub, div_eq_iff (ne_of_gt hr)] at h
      linarith [h]
    refine ⟨-(r⁻¹ • y), ?_⟩
    have hsm : -(r • -(r⁻¹ • y)) = y := by
      rw [smul_neg, neg_neg, smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    rw [hsm]
    have hn : ‖-(r⁻¹ • y)‖ ^ 2 = ‖y‖ ^ 2 / r ^ 2 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
      field_simp
    rw [hn]
    have hVy : V (toLp 2 (y, -r)) = -(B * r) - ‖y‖ ^ 2 / (2 * r) := by
      rw [hMr] at hy
      linarith [hy]
    rw [hVy]
    field_simp
  have hunique : ∀ (l r : ℝ), 0 < l → 0 < r → ∀ qp qm : F,
      V (toLp 2 (l • qp, l)) = B * l + l * ‖qp‖ ^ 2 / 2 →
      V (toLp 2 (-(r • qm), -r)) = -(B * r) - r * ‖qm‖ ^ 2 / 2 → qp = qm := by
    intro l r hl hr qp qm hP hM
    have hlr : (0 : ℝ) < l + r := by linarith
    have hcmp := hdirected (-(r • qm)) (l • qp) (-r) (l + r) hlr
    rw [show -r + (l + r) = l from by ring, hP, hM] at hcmp
    have hdiff : l • qp - -(r • qm) = l • qp + r • qm := by abel
    rw [hdiff] at hcmp
    have hnorm : ‖l • qp + r • qm‖ ^ 2
        = l ^ 2 * ‖qp‖ ^ 2 + 2 * (l * r) * (inner ℝ qp qm : ℝ) + r ^ 2 * ‖qm‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        real_inner_smul_left, real_inner_smul_right]
      have h1 : (|l| * ‖qp‖) ^ 2 = l ^ 2 * ‖qp‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      have h2 : (|r| * ‖qm‖) ^ 2 = r ^ 2 * ‖qm‖ ^ 2 := by
        rw [mul_pow, sq_abs]
      rw [h1, h2]
      ring
    rw [hnorm] at hcmp
    have hclear : (l + r) * (l * ‖qp‖ ^ 2 + r * ‖qm‖ ^ 2)
        ≤ l ^ 2 * ‖qp‖ ^ 2 + 2 * (l * r) * (inner ℝ qp qm : ℝ) + r ^ 2 * ‖qm‖ ^ 2 := by
      have h0 : (0 : ℝ) < 2 * (l + r) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcmp h0.le
      have hrw : (B * (l + r) + (l ^ 2 * ‖qp‖ ^ 2 + 2 * (l * r) * (inner ℝ qp qm : ℝ)
          + r ^ 2 * ‖qm‖ ^ 2) / (2 * (l + r))) * (2 * (l + r))
          = B * (l + r) * (2 * (l + r)) + (l ^ 2 * ‖qp‖ ^ 2
            + 2 * (l * r) * (inner ℝ qp qm : ℝ) + r ^ 2 * ‖qm‖ ^ 2) := by
        field_simp
      rw [hrw] at hmul
      nlinarith [hmul]
    have hexp : ‖qp - qm‖ ^ 2
        = ‖qp‖ ^ 2 - 2 * (inner ℝ qp qm : ℝ) + ‖qm‖ ^ 2 := norm_sub_sq_real qp qm
    have hkey : l * r * ‖qp - qm‖ ^ 2 ≤ 0 := by
      rw [hexp]
      nlinarith [hclear]
    have hz : ‖qp - qm‖ ^ 2 ≤ 0 := by
      by_contra hcon
      have h1 : (0 : ℝ) < ‖qp - qm‖ ^ 2 := lt_of_not_ge hcon
      nlinarith [hkey, mul_pos (mul_pos hl hr) h1]
    have h3 : ‖qp - qm‖ ^ 2 = 0 := le_antisymm hz (sq_nonneg _)
    have h4 : ‖qp - qm‖ = 0 := by nlinarith [h3, norm_nonneg (qp - qm)]
    exact sub_eq_zero.mp (norm_eq_zero.mp h4)
  obtain ⟨q, hq1⟩ := hbwd 1 one_pos
  have hline : ∀ s : ℝ, V (toLp 2 (s • q, s)) = (B + ‖q‖ ^ 2 / 2) * s := by
    intro s
    rcases lt_trichotomy s 0 with hs | hs | hs
    · have hr : (0 : ℝ) < -s := by linarith
      obtain ⟨qm, hqm⟩ := hbwd (-s) hr
      obtain ⟨qp, hqp⟩ := hfwd 1 one_pos
      have h1 : qp = qm := hunique 1 (-s) one_pos hr qp qm hqp hqm
      have h2 : qp = q := hunique 1 1 one_pos one_pos qp q hqp hq1
      have h3 : qm = q := by rw [← h1, h2]
      rw [h3] at hqm
      rw [show -((-s) • q) = s • q from by module, show -(-s) = s from by ring] at hqm
      rw [hqm]
      ring
    · rw [hs]
      have h0 : (toLp 2 ((0 : ℝ) • q, (0 : ℝ)) : WithLp 2 (F × ℝ)) = 0 := by
        rw [zero_smul]
        simp
      rw [h0, hV0]
      ring
    · obtain ⟨qp, hqp⟩ := hfwd s hs
      have h2 : qp = q := hunique s 1 hs one_pos qp q hqp hq1
      rw [h2] at hqp
      rw [hqp]
      ring
  -- Step 11: `V` is affine, and hence so is `v`
  refine hreduce ⟨q, B - ‖q‖ ^ 2 / 2, 0, fun z => ?_⟩
  obtain ⟨x, hx⟩ : ∃ a : F, a = (ofLp z).1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ : ∃ a : ℝ, a = (ofLp z).2 := ⟨_, rfl⟩
  have hzeq : z = toLp 2 (x, t) := by
    rw [hx, ht, Prod.mk.eta, toLp_ofLp]
  obtain ⟨CQ, hCQ⟩ : ∃ c : ℝ, c = ‖x - t • q‖ ^ 2 := ⟨_, rfl⟩
  have hCQ0 : 0 ≤ CQ := by rw [hCQ]; positivity
  have hupper : V (toLp 2 (x, t))
      ≤ inner ℝ q x + (B - ‖q‖ ^ 2 / 2) * t := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨τ, hτ⟩ : ∃ a : ℝ, a = max 1 (CQ / ε) := ⟨_, rfl⟩
    have hτ1 : (1 : ℝ) ≤ τ := by rw [hτ]; exact le_max_left _ _
    have hτ0 : (0 : ℝ) < τ := by linarith
    have hτC : CQ / ε ≤ τ := by rw [hτ]; exact le_max_right _ _
    have hcmp := hdirected ((t - τ) • q) x (t - τ) τ hτ0
    rw [show t - τ + τ = t from by ring, hline (t - τ)] at hcmp
    have hsplit : x - (t - τ) • q = (x - t • q) + τ • q := by module
    rw [hsplit, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_right] at hcmp
    have habs : (|τ| * ‖q‖) ^ 2 = τ ^ 2 * ‖q‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [habs] at hcmp
    have hid : (B + ‖q‖ ^ 2 / 2) * (t - τ) + (B * τ
        + (‖x - t • q‖ ^ 2 + 2 * (τ * (inner ℝ (x - t • q) q : ℝ))
          + τ ^ 2 * ‖q‖ ^ 2) / (2 * τ))
        = inner ℝ q x + (B - ‖q‖ ^ 2 / 2) * t + ‖x - t • q‖ ^ 2 / (2 * τ) := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        real_inner_comm q x]
      field_simp
      ring
    have hCle : CQ / (2 * τ) ≤ ε := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * τ)]
      rw [div_le_iff₀ hε] at hτC
      linarith
    rw [← hCQ] at hid hcmp
    linarith [hcmp, hid, hCle]
  have hlower : inner ℝ q x + (B - ‖q‖ ^ 2 / 2) * t
      ≤ V (toLp 2 (x, t)) := by
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    obtain ⟨τ, hτ⟩ : ∃ a : ℝ, a = max 1 (CQ / ε) := ⟨_, rfl⟩
    have hτ1 : (1 : ℝ) ≤ τ := by rw [hτ]; exact le_max_left _ _
    have hτ0 : (0 : ℝ) < τ := by linarith
    have hτC : CQ / ε ≤ τ := by rw [hτ]; exact le_max_right _ _
    have hcmp := hdirected x ((t + τ) • q) t τ hτ0
    rw [hline (t + τ)] at hcmp
    have hsplit : (t + τ) • q - x = -((x - t • q) - τ • q) := by module
    rw [hsplit, norm_neg, norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      real_inner_smul_right] at hcmp
    have habs : (|τ| * ‖q‖) ^ 2 = τ ^ 2 * ‖q‖ ^ 2 := by rw [mul_pow, sq_abs]
    rw [habs] at hcmp
    have hid : (B + ‖q‖ ^ 2 / 2) * (t + τ) - (B * τ
        + (‖x - t • q‖ ^ 2 - 2 * (τ * (inner ℝ (x - t • q) q : ℝ))
          + τ ^ 2 * ‖q‖ ^ 2) / (2 * τ))
        = inner ℝ q x + (B - ‖q‖ ^ 2 / 2) * t - ‖x - t • q‖ ^ 2 / (2 * τ) := by
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        real_inner_comm q x]
      field_simp
      ring
    have hCle : CQ / (2 * τ) ≤ ε := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 2 * τ)]
      rw [div_le_iff₀ hε] at hτC
      linarith
    rw [← hCQ] at hid hcmp
    linarith [hcmp, hid, hCle]
  rw [hzeq]
  dsimp only
  rw [le_antisymm hupper hlower]
  ring
