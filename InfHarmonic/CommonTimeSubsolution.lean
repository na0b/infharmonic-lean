import InfHarmonic.SumRuleJets
import InfHarmonic.LimitSubClosedSuperjet
import InfHarmonic.SumRuleCommonTimeDirection
import InfHarmonic.PenalizedMaxConvergence
import InfHarmonic.SecondFDerivCompLinear
import InfHarmonic.QuarticFlatAtCentre
import InfHarmonic.PenalizedLiftGradientBlocks
import InfHarmonic.PenalizedLiftSecondDeriv
import InfHarmonic.SecondDerivAddFlat
import InfHarmonic.BilinearEvalContinuousAt
set_option maxHeartbeats 1600000
open Set Metric
open scoped Gradient
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Common-time subsolutions (paper Lemma 5.2): a weighted sum of a subsolution
of the limiting equation, taken at several spatial points sharing one time
variable, satisfies the operator inequality in the direction whose `i`-th
horizontal block is `θ i⁻¹ ∇_{y i} Φ` and whose time component is `1`. -/
theorem CommonTimeSubsolution (N : ℕ) (hN : 0 < N) (I : Set ℝ)
    (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : IsLimitSubOn {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ I} v)
    (θ : Fin N → ℝ) (hθ : ∀ i, 0 < θ i) (hθ1 : ∑ i, θ i = 1)
    (Φ : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) → ℝ)
    (Y₀ : PiLp 2 (fun _ : Fin N => F)) (t₀ : ℝ) (ht₀ : t₀ ∈ I)
    (hΦ : ContDiffAt ℝ 2 Φ (toLp 2 (Y₀, t₀)))
    (hmax : IsLocalMaxOn
      (fun W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) =>
        (∑ i, θ i * v (toLp 2 (ofLp (ofLp W).1 i, (ofLp W).2))) - Φ W)
      {W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) | (ofLp W).2 ∈ I}
      (toLp 2 (Y₀, t₀))) :
    0 ≤ iteratedFDeriv ℝ 2 Φ (toLp 2 (Y₀, t₀)) (fun _ =>
      toLp 2 (toLp 2 (fun i => (θ i)⁻¹ •
        ofLp (ofLp (∇ Φ (toLp 2 (Y₀, t₀)))).1 i), (1 : ℝ))) := by
  classical
  have hNR : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNR
  -- ===================== the two linear maps on the product space =====================
  -- `L` fuses the regrouping with the time average; the second ambient grouping
  -- `ℓ²(G × ℝ^N)` of the .tex is never needed as a type.
  obtain ⟨L, hL⟩ : ∃ L : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) →L[ℝ]
        WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ),
      ∀ W, L W = toLp 2 (toLp 2 (fun i => (ofLp (ofLp W i)).1),
        (N:ℝ)⁻¹ * ∑ i, (ofLp (ofLp W i)).2) := by
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun W => toLp 2 (toLp 2 (fun i => (ofLp (ofLp W i)).1),
          (N:ℝ)⁻¹ * ∑ i, (ofLp (ofLp W i)).2)
        map_add' := ?_
        map_smul' := ?_ }, fun W => rfl⟩
    · intro W W'
      rw [← WithLp.toLp_add]
      congr 1
      refine Prod.ext rfl ?_
      simp [Finset.sum_add_distrib, mul_add]
    · intro c W
      rw [← WithLp.toLp_smul]
      congr 1
      refine Prod.ext rfl ?_
      simp [Finset.mul_sum, mul_left_comm]
  -- `M` records the spread of the time coordinates about their average
  obtain ⟨M, hM⟩ : ∃ M : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) →L[ℝ]
        PiLp 2 (fun _ : Fin N => ℝ),
      ∀ W, M W = toLp 2 (fun i => (ofLp (ofLp W i)).2
        - (N:ℝ)⁻¹ * ∑ j, (ofLp (ofLp W j)).2) := by
    refine ⟨LinearMap.toContinuousLinearMap
      { toFun := fun W => toLp 2 (fun i => (ofLp (ofLp W i)).2
          - (N:ℝ)⁻¹ * ∑ j, (ofLp (ofLp W j)).2)
        map_add' := ?_
        map_smul' := ?_ }, fun W => rfl⟩
    · intro W W'
      rw [← WithLp.toLp_add]
      congr 1
      funext i
      simp [Finset.sum_add_distrib, mul_add]
      ring
    · intro c W
      rw [← WithLp.toLp_smul]
      congr 1
      funext i
      simp [Finset.mul_sum, mul_sub, mul_left_comm]
  -- the diagonal point of the product sitting over the contact point
  obtain ⟨D₀, hD₀⟩ : ∃ D : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)),
      D = toLp 2 (fun i => toLp 2 (ofLp Y₀ i, t₀)) := ⟨_, rfl⟩
  have hLD₀ : L D₀ = toLp 2 (Y₀, t₀) := by
    rw [hL, hD₀]
    congr 1
    refine Prod.ext rfl ?_
    simp
    field_simp
  -- ===================== the slab is open, and the component bounds =====================
  have hΩopen : IsOpen {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ I} := hv.1
  have hvc : ContinuousOn v {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ I} := hv.2.1
  -- `I` is open: it is the preimage of the slab under `t ↦ (0, t)`
  have hIopen : IsOpen I := by
    have hc : Continuous (fun t : ℝ => (toLp 2 ((0:F), t) : WithLp 2 (F × ℝ))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.continuous.comp
        (continuous_const.prodMk continuous_id)
    have he : I = (fun t : ℝ => (toLp 2 ((0:F), t) : WithLp 2 (F × ℝ))) ⁻¹'
        {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ I} := by ext t; simp
    rw [he]
    exact hΩopen.preimage hc
  have htimeF : ∀ z : WithLp 2 (F × ℝ), |(ofLp z).2| ≤ ‖z‖ := by
    intro z
    have h := WithLp.prod_norm_sq_eq_of_L2 z
    have e2 : (ofLp z).2 = z.snd := rfl
    rw [e2]
    have hb : |z.snd| = ‖z.snd‖ := (Real.norm_eq_abs _).symm
    rw [hb]
    nlinarith [norm_nonneg z, norm_nonneg z.fst, norm_nonneg z.snd]
  have htimeG : ∀ z : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ), |(ofLp z).2| ≤ ‖z‖ := by
    intro z
    have h := WithLp.prod_norm_sq_eq_of_L2 z
    have e2 : (ofLp z).2 = z.snd := rfl
    rw [e2]
    have hb : |z.snd| = ‖z.snd‖ := (Real.norm_eq_abs _).symm
    rw [hb]
    nlinarith [norm_nonneg z, norm_nonneg z.fst, norm_nonneg z.snd]
  have hco : ∀ (ζ : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ))) (j : Fin N),
      ‖ofLp ζ j‖ ≤ ‖ζ‖ := by
    intro ζ j
    have hpyth : (∑ i, ‖ofLp ζ i‖ ^ 2) = ‖ζ‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
      exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_self_eq_norm_sq])
    have h1 : ‖ofLp ζ j‖ ^ 2 ≤ ∑ i, ‖ofLp ζ i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin N => ‖ofLp ζ i‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ j)
    rw [hpyth] at h1
    nlinarith [norm_nonneg (ofLp ζ j), norm_nonneg ζ]
  -- ===================== the three radii =====================
  obtain ⟨ρ₁, hρ₁, hΦC2⟩ : ∃ ρ > 0, ∀ Z : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ),
      dist Z (toLp 2 (Y₀, t₀)) < ρ → ContDiffAt ℝ 2 Φ Z := by
    obtain ⟨ρ, hρ, hb⟩ := Metric.eventually_nhds_iff.mp (hΦ.eventually (by norm_num))
    exact ⟨ρ, hρ, fun Z hZ => hb hZ⟩
  have hDopen : IsOpen {W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) | (ofLp W).2 ∈ I} := by
    have hc : Continuous (fun W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) => (ofLp W).2) :=
      continuous_snd.comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : Fin N => F)) ℝ).continuous
    exact hIopen.preimage hc
  have hZ₀D : (toLp 2 (Y₀, t₀) : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ))
      ∈ {W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) | (ofLp W).2 ∈ I} := by
    simpa using ht₀
  rw [IsLocalMaxOn, IsMaxFilter, hDopen.nhdsWithin_eq hZ₀D] at hmax
  obtain ⟨ρ₂, hρ₂, hmaxb⟩ := Metric.eventually_nhds_iff.mp hmax
  obtain ⟨ρ₃, hρ₃, hIball⟩ := Metric.isOpen_iff.mp hIopen t₀ ht₀
  -- ===================== the working radius =====================
  obtain ⟨ρ, hρd⟩ : ∃ x : ℝ, x = min ρ₁ (min ρ₂ ρ₃) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρd]; exact lt_min hρ₁ (lt_min hρ₂ hρ₃)
  have hρ1' : ρ ≤ ρ₁ := by rw [hρd]; exact min_le_left _ _
  have hρ2' : ρ ≤ ρ₂ := by rw [hρd]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ3' : ρ ≤ ρ₃ := by rw [hρd]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨c, hcd⟩ : ∃ x : ℝ, x = ‖L‖ + 1 := ⟨_, rfl⟩
  have hc1 : 1 ≤ c := by rw [hcd]; linarith [norm_nonneg L]
  have hc0 : 0 < c := by linarith
  obtain ⟨r, hrd⟩ : ∃ x : ℝ, x = ρ / (2 * c) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrd]; positivity
  have hrc : c * r = ρ / 2 := by rw [hrd]; field_simp
  have hrρ : r < ρ := by nlinarith [hρ0, hc1, hrc, hr0]
  -- the two estimates the ball `closedBall D₀ r` buys
  have hLb : ∀ W : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)), ‖W - D₀‖ ≤ r →
      ‖L W - toLp 2 (Y₀, t₀)‖ < ρ := by
    intro W hW
    have h1 : L W - toLp 2 (Y₀, t₀) = L (W - D₀) := by rw [← hLD₀, ← map_sub]
    have h2 : ‖L (W - D₀)‖ ≤ ‖L‖ * ‖W - D₀‖ := L.le_opNorm _
    have h3 : ‖L‖ * ‖W - D₀‖ ≤ ‖L‖ * r :=
      mul_le_mul_of_nonneg_left hW (norm_nonneg L)
    have h4 : ‖L‖ * r ≤ c * r := by
      refine mul_le_mul_of_nonneg_right ?_ hr0.le
      rw [hcd]; linarith
    rw [h1]
    linarith [hrc, hρ0]
  have hcompt : ∀ W : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)), ‖W - D₀‖ ≤ r →
      ∀ i, ofLp W i ∈ {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ I} := by
    intro W hW i
    have h1 : ofLp W i - ofLp D₀ i = ofLp (W - D₀) i := rfl
    have h2 : ‖ofLp W i - ofLp D₀ i‖ ≤ ‖W - D₀‖ := by rw [h1]; exact hco (W - D₀) i
    have h3 : (ofLp (ofLp D₀ i)).2 = t₀ := by rw [hD₀]
    have h4 : |(ofLp (ofLp W i)).2 - t₀| ≤ ‖ofLp W i - ofLp D₀ i‖ := by
      have h5 := htimeF (ofLp W i - ofLp D₀ i)
      have h6 : (ofLp (ofLp W i - ofLp D₀ i)).2 = (ofLp (ofLp W i)).2 - t₀ := by
        rw [← h3]; rfl
      rwa [h6] at h5
    have h7 : (ofLp (ofLp W i)).2 ∈ Metric.ball t₀ ρ₃ := by
      simp only [Metric.mem_ball, Real.dist_eq]
      linarith [hrρ, hρ3']
    exact hIball h7
  -- ===================== Step 1: the strictified test =====================
  obtain ⟨hκcd, hκ1, hκ2⟩ := QuarticFlatAtCentre
    (toLp 2 (Y₀, t₀) : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ))
  obtain ⟨Φs, hΦs⟩ : ∃ f : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) → ℝ,
      f = fun Z => Φ Z + ‖Z - toLp 2 (Y₀, t₀)‖ ^ 4 := ⟨_, rfl⟩
  have hΦsC2 : ∀ Z : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ),
      dist Z (toLp 2 (Y₀, t₀)) < ρ₁ → ContDiffAt ℝ 2 Φs Z := by
    intro Z hZ
    rw [hΦs]
    exact (hΦC2 Z hZ).add hκcd.contDiffAt
  -- ===================== Step 2: the penalty and the objective =====================
  obtain ⟨χ, hχd⟩ : ∃ f : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) → ℝ,
      f = fun W => ‖M W‖ ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨Θ, hΘd⟩ : ∃ f : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) → ℝ,
      f = fun W : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) =>
        (∑ i, θ i * v (ofLp W i)) - Φs (L W) := ⟨_, rfl⟩
  have hχc : Continuous χ := by
    rw [hχd]
    exact (M.continuous.norm.pow 2).div_const _
  have hχ0 : ∀ W, 0 ≤ χ W := by intro W; rw [hχd]; positivity
  have hMD₀ : M D₀ = 0 := by
    have h1 : M D₀ = toLp 2 (fun _ : Fin N => (0:ℝ)) := by
      rw [hM, hD₀]
      congr 1
      funext i
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [← mul_assoc, inv_mul_cancel₀ hNne, one_mul, sub_self]
    rw [h1]
    rfl
  have hχD₀ : χ D₀ = 0 := by simp only [hχd, hMD₀]; simp
  -- continuity of the objective on the ball
  have hΘc : ContinuousOn Θ (Metric.closedBall D₀ r) := by
    rw [hΘd]
    refine ContinuousOn.sub ?_ ?_
    · refine continuousOn_finsetSum _ (fun i _ => ?_)
      refine ContinuousOn.mul continuousOn_const ?_
      refine ContinuousOn.comp hvc
        ((PiLp.continuous_apply (p := 2) (fun _ : Fin N => WithLp 2 (F × ℝ)) i).continuousOn)
        (fun W hW => hcompt W (by simpa [Metric.mem_closedBall, dist_eq_norm] using hW) i)
    · intro W hW
      refine ContinuousAt.continuousWithinAt ?_
      have hW' : ‖W - D₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hW
      have h1 : dist (L W) (toLp 2 (Y₀, t₀)) < ρ₁ := by
        rw [dist_eq_norm]; linarith [hLb W hW', hρ1']
      exact ((hΦsC2 (L W) h1).continuousAt).comp L.continuous.continuousAt
  -- ===================== the strict maximum on the zero set of the penalty ==============
  have hD₀mem : D₀ ∈ Metric.closedBall D₀ r := Metric.mem_closedBall_self hr0.le
  have hstrict : ∀ W ∈ Metric.closedBall D₀ r, χ W = 0 → W ≠ D₀ → Θ W < Θ D₀ := by
    intro W hW hχW hWne
    have hW' : ‖W - D₀‖ ≤ r := by simpa [Metric.mem_closedBall, dist_eq_norm] using hW
    -- all the time coordinates of `W` agree with their average
    have hMW : M W = 0 := by
      have hn : ‖M W‖ = 0 := by
        rw [hχd] at hχW
        nlinarith [norm_nonneg (M W)]
      exact norm_eq_zero.mp hn
    have hteq : ∀ i, (ofLp (ofLp W i)).2 = (N:ℝ)⁻¹ * ∑ j, (ofLp (ofLp W j)).2 := by
      intro i
      have h2 : ofLp (M W) i = 0 := by rw [hMW]; rfl
      rw [hM] at h2
      exact sub_eq_zero.mp h2
    -- so `W` is the diagonal lift of `L W`
    have hWcomp : ∀ i, ofLp W i
        = toLp 2 (ofLp (ofLp (L W)).1 i, (ofLp (L W)).2) := by
      intro i
      rw [hL]
      simp only
      rw [← hteq i]
    have hΘW : Θ W = ((∑ i, θ i * v (toLp 2 (ofLp (ofLp (L W)).1 i, (ofLp (L W)).2)))
        - Φ (L W)) - ‖L W - toLp 2 (Y₀, t₀)‖ ^ 4 := by
      rw [hΘd]
      simp only
      rw [hΦs]
      have : ∀ i, v (ofLp W i) = v (toLp 2 (ofLp (ofLp (L W)).1 i, (ofLp (L W)).2)) := by
        intro i; rw [hWcomp i]
      rw [Finset.sum_congr rfl (fun i _ => by rw [this i])]
      ring
    have hΘD₀ : Θ D₀ = (∑ i, θ i * v (toLp 2 (ofLp Y₀ i, t₀))) - Φ (toLp 2 (Y₀, t₀)) := by
      simp only [hΘd, hΦs]
      rw [hLD₀, hD₀]
      simp
    -- the ambient local maximum applies at `L W`
    have hdist : dist (L W) (toLp 2 (Y₀, t₀)) < ρ₂ := by
      rw [dist_eq_norm]; linarith [hLb W hW', hρ2']
    have hmx := hmaxb hdist
    simp only at hmx
    -- the quartic is strictly positive unless `L W` is the contact point
    have hLWne : L W ≠ toLp 2 (Y₀, t₀) := by
      intro hLW
      refine hWne ?_
      have h1 : ∀ i, ofLp W i = ofLp D₀ i := by
        intro i
        rw [hWcomp i, hLW, hD₀]
      have : ofLp W = ofLp D₀ := funext h1
      exact WithLp.ofLp_injective _ this
    have hq : 0 < ‖L W - toLp 2 (Y₀, t₀)‖ ^ 4 := by
      have : L W - toLp 2 (Y₀, t₀) ≠ 0 := sub_ne_zero.mpr hLWne
      have h2 : 0 < ‖L W - toLp 2 (Y₀, t₀)‖ := norm_pos_iff.mpr this
      positivity
    rw [hΘW, hΘD₀]
    linarith
  -- ===================== Step 3: the penalised maximisers =====================
  obtain ⟨lam, hlamd⟩ : ∃ f : ℕ → ℝ, f = fun m : ℕ => (m:ℝ) + 1 := ⟨_, rfl⟩
  have hlam0 : ∀ m, 0 < lam m := by
    intro m; rw [hlamd]; positivity
  have hlamtop : Filter.Tendsto lam Filter.atTop Filter.atTop := by
    rw [hlamd]
    exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hKcomp : IsCompact (Metric.closedBall D₀ r) := isCompact_closedBall _ _
  obtain ⟨Ws, hWsK, hWsmax⟩ : ∃ Ws : ℕ → PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)),
      (∀ m, Ws m ∈ Metric.closedBall D₀ r) ∧
        ∀ m, ∀ W ∈ Metric.closedBall D₀ r,
          Θ W - lam m * χ W ≤ Θ (Ws m) - lam m * χ (Ws m) := by
    have hex : ∀ m : ℕ, ∃ W ∈ Metric.closedBall D₀ r,
        IsMaxOn (fun U => Θ U - lam m * χ U) (Metric.closedBall D₀ r) W := fun m =>
      hKcomp.exists_isMaxOn ⟨D₀, hD₀mem⟩
        (hΘc.sub (continuousOn_const.mul hχc.continuousOn))
    choose Ws hWsK hWsmax using hex
    exact ⟨Ws, hWsK, fun m W hW => hWsmax m hW⟩
  have hconv : Filter.Tendsto Ws Filter.atTop (nhds D₀) :=
    PenalizedMaxConvergence (Metric.closedBall D₀ r) hKcomp Θ χ hΘc hχc.continuousOn
      (fun k _ => hχ0 k) D₀ hD₀mem hχD₀ hstrict lam hlam0 hlamtop Ws hWsK hWsmax
  obtain ⟨m₀, hm₀⟩ := Metric.tendsto_atTop.mp hconv r hr0
  -- ===================== Step 4: the sum-rule direction as a field ====================
  -- `ξ Z` is the product direction the sum rule produces when the gradient is `∇Φs Z`;
  -- `η Z` is its image under `L`.  Every time coordinate of `ξ Z` is `1`, so `M` kills
  -- it: this is the kernel condition the penalty needs.
  obtain ⟨ξ, hξd⟩ : ∃ f : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) →
        PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)),
      f = fun Z => toLp 2 (fun i => toLp 2 ((θ i)⁻¹ •
        ofLp (ofLp (∇ Φs Z)).1 i, (1:ℝ))) := ⟨_, rfl⟩
  obtain ⟨η, hηd⟩ : ∃ f : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) →
        WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ),
      f = fun Z => toLp 2 (toLp 2 (fun i => (θ i)⁻¹ •
        ofLp (ofLp (∇ Φs Z)).1 i), (1:ℝ)) := ⟨_, rfl⟩
  have hξ2 : ∀ Z j, (ofLp (ofLp (ξ Z) j)).2 = (1:ℝ) := by
    intro Z j; rw [hξd]
  have hξsum : ∀ Z, ∑ j, (ofLp (ofLp (ξ Z) j)).2 = (N:ℝ) := by
    intro Z
    simp only [hξ2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one]
  have hMξ : ∀ Z, M (ξ Z) = 0 := by
    intro Z
    have h1 : M (ξ Z) = toLp 2 (fun _ : Fin N => (0:ℝ)) := by
      rw [hM]
      congr 1
      funext i
      rw [hξ2 Z i, hξsum Z, inv_mul_cancel₀ hNne, sub_self]
    rw [h1]; rfl
  have hLη : ∀ Z, L (ξ Z) = η Z := by
    intro Z
    rw [hL, hηd]
    congr 1
    refine Prod.ext ?_ ?_
    · show (toLp 2 (fun i => (ofLp (ofLp (ξ Z) i)).1) : PiLp 2 (fun _ : Fin N => F))
        = toLp 2 (fun i => (θ i)⁻¹ • ofLp (ofLp (∇ Φs Z)).1 i)
      congr 1
      funext i
      rw [hξd]
    · show (N:ℝ)⁻¹ * ∑ j, (ofLp (ofLp (ξ Z) j)).2 = 1
      rw [hξsum Z, inv_mul_cancel₀ hNne]
  -- ===================== Step 5: the inequality along the sequence ====================
  have hkey : ∀ m : ℕ, m₀ ≤ m →
      0 ≤ fderiv ℝ (fderiv ℝ Φs) (L (Ws m)) (η (L (Ws m))) (η (L (Ws m))) := by
    intro m hm
    have hWr : ‖Ws m - D₀‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hWsK m
    have hWrlt : ‖Ws m - D₀‖ < r := by
      have h := hm₀ m hm
      rwa [dist_eq_norm] at h
    have hLWd : dist (L (Ws m)) (toLp 2 (Y₀, t₀)) < ρ₁ := by
      rw [dist_eq_norm]
      linarith [hLb (Ws m) hWr, hρ1']
    have hΦsAt : ContDiffAt ℝ 2 Φs (L (Ws m)) := hΦsC2 _ hLWd
    -- the penalised test function at level `lam m`
    obtain ⟨Ψ, hΨd⟩ : ∃ f : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) → ℝ,
        f = fun U => Φs (L U) + lam m * (‖M U‖ ^ 2 / 2) := ⟨_, rfl⟩
    have hΨC2 : ContDiffAt ℝ 2 Ψ (Ws m) := by
      rw [hΨd]
      refine ContDiffAt.add (ContDiffAt.comp _ hΦsAt (L.contDiff (n := 2)).contDiffAt) ?_
      exact (contDiff_const.mul
        (((contDiff_norm_sq ℝ).div_const 2).comp (M.contDiff (n := 2)))).contDiffAt
    -- interiority upgrades the constrained maximum to a local one
    have hlocmax : IsLocalMax
        (fun Y : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)) =>
          (∑ i, θ i * v (ofLp Y i)) - Ψ Y) (Ws m) := by
      have hball : Metric.ball D₀ r ∈ nhds (Ws m) :=
        Metric.isOpen_ball.mem_nhds
          (by simpa [Metric.mem_ball, dist_eq_norm] using hWrlt)
      filter_upwards [hball] with W hW
      have h1 := hWsmax m W (Metric.ball_subset_closedBall hW)
      have e1 : ∀ U : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)),
          Θ U - lam m * χ U = (∑ i, θ i * v (ofLp U i)) - Ψ U := by
        intro U
        simp only [hΘd, hΨd, hχd]
        ring
      rw [e1 W, e1 (Ws m)] at h1
      exact h1
    have hsr := SumRuleCommonTimeDirection N {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ I}
      v hv θ hθ Ψ (Ws m) (hcompt (Ws m) hWr) hΨC2 hlocmax
    rw [hΨd] at hsr
    -- the penalty is invisible both to the direction and to the second derivative
    have hgb := PenalizedLiftGradientBlocks N L hL M hM Φs (lam m) (Ws m) hΦsAt
    have hdir : (toLp 2 (fun i => toLp 2 ((θ i)⁻¹ •
          (ofLp (ofLp (∇ (fun U => Φs (L U) + lam m * (‖M U‖ ^ 2 / 2)) (Ws m)) i)).1,
          (1:ℝ))) : PiLp 2 (fun _ : Fin N => WithLp 2 (F × ℝ)))
        = ξ (L (Ws m)) := by
      rw [hξd]
      congr 1
      funext i
      rw [hgb i]
    rw [hdir, PenalizedLiftSecondDeriv L M Φs (lam m) (Ws m) (ξ (L (Ws m))) hΦsAt
      (hMξ _), hLη] at hsr
    exact hsr
  -- ===================== Step 6: passing to the limit =====================
  have hΦsAt0 : ContDiffAt ℝ 2 Φs (toLp 2 (Y₀, t₀)) := hΦsC2 _ (by simpa using hρ₁)
  -- the quartic is flat at the centre, so `Φs` and `Φ` share their jet there
  obtain ⟨hflat1, hflat2⟩ := SecondDerivAddFlat Φ
    (fun Z : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) => ‖Z - toLp 2 (Y₀, t₀)‖ ^ 4)
    (toLp 2 (Y₀, t₀)) hΦ hκcd hκ1 hκ2
  have hfd1 : fderiv ℝ Φs (toLp 2 (Y₀, t₀)) = fderiv ℝ Φ (toLp 2 (Y₀, t₀)) := by
    rw [hΦs]; exact hflat1
  have hfd2 : fderiv ℝ (fderiv ℝ Φs) (toLp 2 (Y₀, t₀))
      = fderiv ℝ (fderiv ℝ Φ) (toLp 2 (Y₀, t₀)) := by
    rw [hΦs]; exact hflat2
  have hgr0 : ∇ Φs (toLp 2 (Y₀, t₀)) = ∇ Φ (toLp 2 (Y₀, t₀)) := by
    simp only [gradient, hfd1]
  -- continuity of the second-order data and of the direction at the centre
  have hcont1 : ContinuousAt (fderiv ℝ Φs) (toLp 2 (Y₀, t₀)) :=
    hΦsAt0.continuousAt_fderiv (by norm_num)
  have hcont2 : ContinuousAt (fderiv ℝ (fderiv ℝ Φs)) (toLp 2 (Y₀, t₀)) :=
    (hΦsAt0.fderiv_right (m := 1) le_rfl).continuousAt_fderiv (by norm_num)
  have hgradc : ContinuousAt (fun Z => ∇ Φs Z) (toLp 2 (Y₀, t₀)) := by
    simp only [gradient]
    exact (InnerProductSpace.toDual ℝ
      (WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ))).symm.continuous.continuousAt.comp hcont1
  have hDcont : Continuous (fun W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) =>
      (toLp 2 (toLp 2 (fun i => (θ i)⁻¹ • ofLp (ofLp W).1 i), (1:ℝ))
        : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ))) := by
    have h1 : Continuous (fun W : WithLp 2 (PiLp 2 (fun _ : Fin N => F) × ℝ) =>
        (ofLp W).1) :=
      continuous_fst.comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : Fin N => F)) ℝ).continuous
    have h2 : Continuous (fun Y : PiLp 2 (fun _ : Fin N => F) =>
        (toLp 2 (fun i => (θ i)⁻¹ • ofLp Y i) : PiLp 2 (fun _ : Fin N => F))) :=
      (PiLp.continuous_toLp 2 (fun _ : Fin N => F)).comp
        (continuous_pi fun i =>
          (PiLp.continuous_apply 2 (fun _ : Fin N => F) i).const_smul ((θ i)⁻¹))
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ
      (PiLp 2 (fun _ : Fin N => F)) ℝ).symm.continuous.comp
      ((h2.comp h1).prodMk continuous_const)
  have hηc : ContinuousAt η (toLp 2 (Y₀, t₀)) := by
    rw [hηd]
    exact hDcont.continuousAt.comp hgradc
  have hLWs : Filter.Tendsto (fun m => L (Ws m)) Filter.atTop (nhds (toLp 2 (Y₀, t₀))) := by
    rw [← hLD₀]
    exact L.continuous.continuousAt.tendsto.comp hconv
  -- the second derivative and the direction converge jointly, and evaluation is continuous
  have hHc : ContinuousAt (fun Z => fderiv ℝ (fderiv ℝ Φs) Z (η Z) (η Z))
      (toLp 2 (Y₀, t₀)) :=
    BilinearEvalContinuousAt (fun Z => fderiv ℝ (fderiv ℝ Φs) Z) η (toLp 2 (Y₀, t₀))
      hcont2 hηc
  have hlim := Filter.Tendsto.comp hHc hLWs
  have hnonneg : (0:ℝ) ≤ fderiv ℝ (fderiv ℝ Φs) (toLp 2 (Y₀, t₀))
      (η (toLp 2 (Y₀, t₀))) (η (toLp 2 (Y₀, t₀))) := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop m₀] with m hm
    exact hkey m hm
  -- the limit is the goal
  rw [iteratedFDeriv_two_apply]
  have hηgoal : η (toLp 2 (Y₀, t₀)) = toLp 2 (toLp 2 (fun i => (θ i)⁻¹ •
      ofLp (ofLp (∇ Φ (toLp 2 (Y₀, t₀)))).1 i), (1:ℝ)) := by
    simp only [hηd, hgr0]
  rw [← hfd2, ← hηgoal]
  exact hnonneg
