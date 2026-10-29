import InfHarmonic.ConeComparison
import InfHarmonic.ConeSlopeLimitEq
import InfHarmonic.InfHarmonicLocLipschitz
import InfHarmonic.InfHarmonicRescale
import InfHarmonic.InfHarmonicNormalize
import InfHarmonic.InfHarmonicStability
open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Proposition 2.5: at a fixed center, every locally uniform limit of the
affine blow-ups of an infinity-harmonic function is linear, and such limits
exist along subsequences. -/
theorem AffineBlowups (D : Set E) (w : E → ℝ) (hw : IsInfHarmonicOn D w)
    (z : E) (hz : z ∈ D) :
    (∀ (ρ : ℕ → ℝ) (V : E → ℝ), (∀ i, 0 < ρ i) → Tendsto ρ atTop (𝓝 0) →
        (∀ K : Set E, IsCompact K →
          TendstoUniformlyOn (fun i Y => (w (z + ρ i • Y) - w z) / ρ i) V atTop K) →
        ∃ L : E →L[ℝ] ℝ, ∀ Y, V Y = L Y) ∧
      (∀ ρ : ℕ → ℝ, (∀ i, 0 < ρ i) → Tendsto ρ atTop (𝓝 0) →
        ∃ (ι : ℕ → ℕ) (V : E → ℝ), StrictMono ι ∧
          ∀ K : Set E, IsCompact K →
            TendstoUniformlyOn (fun i Y => (w (z + ρ (ι i) • Y) - w z) / ρ (ι i)) V atTop K) := by
  have hDopen : IsOpen D := hw.1.1
  have hcw : ContinuousOn w D := hw.1.2.1
  -- Step 0: a radius `σ > 0` with `closedBall z (2σ) ⊆ D`.
  obtain ⟨σ, hσ, hball⟩ : ∃ σ : ℝ, 0 < σ ∧ closedBall z (2 * σ) ⊆ D := by
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hDopen z hz
    refine ⟨ε / 4, by positivity, fun x hx => hεD ?_⟩
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  -- Step 1: `w` is `Λ`-Lipschitz on `closedBall z σ` for a finite `Λ ≥ 0`.
  obtain ⟨Λ, hΛ0, hlipw⟩ : ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∀ a ∈ closedBall z σ, ∀ b ∈ closedBall z σ, |w a - w b| ≤ Λ * ‖a - b‖ := by
    have hKcomp : IsCompact (closedBall z (2 * σ)) := isCompact_closedBall _ _
    have hKne : (closedBall z (2 * σ)).Nonempty := ⟨z, mem_closedBall_self (by positivity)⟩
    have hcon : ContinuousOn w (closedBall z (2 * σ)) := hcw.mono hball
    obtain ⟨p, hp, hpmax⟩ := hKcomp.exists_isMaxOn hKne hcon
    obtain ⟨q, hq, hqmin⟩ := hKcomp.exists_isMinOn hKne hcon
    have hqp : w q ≤ w p := hpmax hq
    refine ⟨(w p - w q) / σ, div_nonneg (by linarith) hσ.le, ?_⟩
    · refine InfHarmonicLocLipschitz D w hw z σ σ ((w p - w q) / σ) hσ.le hσ ?_ ?_
      · rw [show σ + σ = 2 * σ by ring]; exact hball
      · intro a ha b hb
        rw [show σ + σ = 2 * σ by ring] at ha hb
        have h1 : w a ≤ w p := hpmax ha
        have h2 : w q ≤ w b := hqmin hb
        have h3 : w b ≤ w p := hpmax hb
        have h4 : w q ≤ w a := hqmin ha
        rw [div_mul_cancel₀ _ (ne_of_gt hσ)]
        rw [abs_le]
        constructor <;> linarith
  -- Step 2: the blow-up bounds.
  have hmemball : ∀ (ρ R : ℝ), 0 < ρ → ρ * R ≤ σ →
      ∀ Y ∈ closedBall (0 : E) R, z + ρ • Y ∈ closedBall z σ := by
    intro ρ R hρ hρR Y hY
    rw [mem_closedBall, dist_zero_right] at hY
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hρ]
    calc ρ * ‖Y‖ ≤ ρ * R := mul_le_mul_of_nonneg_left hY hρ.le
      _ ≤ σ := hρR
  have hblip : ∀ (ρ R : ℝ), 0 < ρ → ρ * R ≤ σ →
      ∀ Y ∈ closedBall (0 : E) R, ∀ Y' ∈ closedBall (0 : E) R,
        dist ((w (z + ρ • Y) - w z) / ρ) ((w (z + ρ • Y') - w z) / ρ) ≤ Λ * dist Y Y' := by
    intro ρ R hρ hρR Y hY Y' hY'
    have h := hlipw _ (hmemball ρ R hρ hρR Y hY) _ (hmemball ρ R hρ hρR Y' hY')
    have hd : ‖z + ρ • Y - (z + ρ • Y')‖ = ρ * ‖Y - Y'‖ := by
      rw [show z + ρ • Y - (z + ρ • Y') = ρ • (Y - Y') by rw [smul_sub]; abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos hρ]
    rw [hd] at h
    rw [Real.dist_eq, div_sub_div_same, sub_sub_sub_cancel_right, dist_eq_norm, abs_div,
      abs_of_pos hρ, div_le_iff₀ hρ]
    calc |w (z + ρ • Y) - w (z + ρ • Y')| ≤ Λ * (ρ * ‖Y - Y'‖) := h
      _ = Λ * ‖Y - Y'‖ * ρ := by ring
  have hV0 : ∀ ρ : ℝ, (w (z + ρ • (0 : E)) - w z) / ρ = 0 := by intro ρ; simp
  -- ===================== PART (2): Arzela-Ascoli =====================
  have part2 : ∀ ρ : ℕ → ℝ, (∀ i, 0 < ρ i) → Tendsto ρ atTop (𝓝 0) →
      ∃ (ι : ℕ → ℕ) (V : E → ℝ), StrictMono ι ∧
        ∀ K : Set E, IsCompact K →
          TendstoUniformlyOn (fun i Y => (w (z + ρ (ι i) • Y) - w z) / ρ (ι i)) V atTop K := by
    intro ρ hρpos hρ0
    -- (a) each blow-up extends to a globally `Λ`-Lipschitz function agreeing with it on
    -- the ball of radius `σ / ρ i`.
    have hRpos : ∀ i, 0 < σ / ρ i := fun i => div_pos hσ (hρpos i)
    have hRprod : ∀ i, ρ i * (σ / ρ i) ≤ σ := by
      intro i; rw [mul_div_cancel₀ _ (ne_of_gt (hρpos i))]
    have hext : ∀ i : ℕ, ∃ g : E → ℝ, LipschitzWith (Real.toNNReal Λ) g ∧
        EqOn (fun Y => (w (z + ρ i • Y) - w z) / ρ i) g (closedBall (0 : E) (σ / ρ i)) := by
      intro i
      refine LipschitzOnWith.extend_real (K := Real.toNNReal Λ) (LipschitzOnWith.of_dist_le_mul ?_)
      intro Y hY Y' hY'
      rw [Real.coe_toNNReal Λ hΛ0]
      exact hblip (ρ i) (σ / ρ i) (hρpos i) (hRprod i) Y hY Y' hY'
    choose u hulip hueq using hext
    have hΛc : (Real.toNNReal Λ : ℝ) = Λ := Real.coe_toNNReal Λ hΛ0
    have hudist : ∀ (i : ℕ) (a b : E), |u i a - u i b| ≤ Λ * ‖a - b‖ := by
      intro i a b
      have := (hulip i).dist_le_mul a b
      rw [hΛc, Real.dist_eq, dist_eq_norm] at this
      exact this
    have hu0 : ∀ i, u i 0 = 0 := by
      intro i
      have h := hueq i (mem_closedBall_self (hRpos i).le)
      rw [← h]
      exact hV0 (ρ i)
    have hubd : ∀ (i : ℕ) (Y : E), |u i Y| ≤ Λ * ‖Y‖ := by
      intro i Y
      have := hudist i Y 0
      rw [hu0, sub_zero, sub_zero] at this
      exact this
    -- (b) a countable dense set, and the diagonal extraction via product compactness
    obtain ⟨Q, hQ⟩ := TopologicalSpace.exists_dense_seq E
    obtain ⟨ι, g, hιmono, hgconv⟩ : ∃ (ι : ℕ → ℕ) (g : ℕ → ℝ), StrictMono ι ∧
        ∀ k, Tendsto (fun j => u (ι j) (Q k)) atTop (𝓝 (g k)) := by
      have hcomp : IsCompact (univ.pi (fun k : ℕ => Icc (-(Λ * ‖Q k‖)) (Λ * ‖Q k‖))) :=
        isCompact_univ_pi fun k => isCompact_Icc
      have hmem : ∀ i : ℕ, (fun k => u i (Q k))
          ∈ univ.pi (fun k : ℕ => Icc (-(Λ * ‖Q k‖)) (Λ * ‖Q k‖)) := by
        intro i k _
        exact abs_le.mp (hubd i (Q k))
      obtain ⟨gg, -, ι, hι, htend⟩ := hcomp.isSeqCompact hmem
      exact ⟨ι, gg, hι, fun k => ((continuous_apply k).continuousAt.tendsto).comp htend⟩
    -- (c) the limit function, by a Cauchy estimate against the dense set
    have hcauchy : ∀ Y : E, CauchySeq (fun j => u (ι j) Y) := by
      intro Y
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨k, hk⟩ : ∃ k, dist Y (Q k) < ε / (3 * (Λ + 1)) :=
        Metric.denseRange_iff.mp hQ Y _ (by positivity)
      obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp (hgconv k).cauchySeq (ε / 3) (by positivity)
      refine ⟨N, fun m hm n hn => ?_⟩
      have h1 : |u (ι m) Y - u (ι m) (Q k)| ≤ Λ * ‖Y - Q k‖ := hudist _ _ _
      have h2 : |u (ι n) (Q k) - u (ι n) Y| ≤ Λ * ‖Q k - Y‖ := hudist _ _ _
      have h3 : |u (ι m) (Q k) - u (ι n) (Q k)| < ε / 3 := by
        have := hN m hm n hn; rwa [Real.dist_eq] at this
      have hsym : ‖Q k - Y‖ = ‖Y - Q k‖ := by rw [← norm_neg]; simp
      have hd : ‖Y - Q k‖ < ε / (3 * (Λ + 1)) := by rwa [dist_eq_norm] at hk
      have hb : Λ * ‖Y - Q k‖ ≤ ε / 3 := by
        have hpos : (0:ℝ) < 3 * (Λ + 1) := by positivity
        have : Λ * ‖Y - Q k‖ ≤ Λ * (ε / (3 * (Λ + 1))) :=
          mul_le_mul_of_nonneg_left hd.le hΛ0
        refine this.trans ?_
        rw [show Λ * (ε / (3 * (Λ + 1))) = Λ * ε / (3 * (Λ + 1)) by ring, div_le_iff₀ hpos]
        nlinarith [hε.le, hΛ0]
      rw [hsym] at h2
      rw [Real.dist_eq]
      calc |u (ι m) Y - u (ι n) Y|
          ≤ |u (ι m) Y - u (ι m) (Q k)| + |u (ι m) (Q k) - u (ι n) (Q k)|
            + |u (ι n) (Q k) - u (ι n) Y| := by
            linarith [abs_sub_le (u (ι m) Y) (u (ι m) (Q k)) (u (ι n) (Q k)),
              abs_sub_le (u (ι m) Y) (u (ι n) (Q k)) (u (ι n) Y)]
        _ < ε := by linarith
    choose V hVconv using fun Y => cauchySeq_tendsto_of_complete (hcauchy Y)
    -- (d) `V` is `Λ`-Lipschitz
    have hVlipg : ∀ a b : E, |V a - V b| ≤ Λ * ‖a - b‖ := by
      intro a b
      have hT : Tendsto (fun j => |u (ι j) a - u (ι j) b|) atTop (𝓝 |V a - V b|) :=
        (continuous_abs.continuousAt.tendsto).comp ((hVconv a).sub (hVconv b))
      exact le_of_tendsto hT (Eventually.of_forall fun j => hudist _ _ _)
    -- (e) equi-Lipschitz plus pointwise convergence gives uniform convergence on compacts
    have huuc : ∀ K : Set E, IsCompact K →
        TendstoUniformlyOn (fun j => u (ι j)) V atTop K := by
      intro K hK
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hηpos : 0 < ε / (3 * (Λ + 1)) := by positivity
      obtain ⟨N, -, hNfin, hcov⟩ := finite_cover_balls_of_compact (s := K) hK hηpos
      have hfin : ∀ᶠ j in atTop, ∀ b ∈ N, dist (V b) (u (ι j) b) < ε / 3 := by
        rw [eventually_all_finite hNfin]
        intro b _
        filter_upwards [Metric.tendsto_nhds.mp (hVconv b) (ε / 3) (by positivity)] with j hj
        rwa [dist_comm]
      filter_upwards [hfin] with j hj Y hY
      obtain ⟨b, hbN, hbY⟩ : ∃ b ∈ N, Y ∈ ball b (ε / (3 * (Λ + 1))) := by
        simpa using hcov hY
      have hd : ‖Y - b‖ < ε / (3 * (Λ + 1)) := by rwa [mem_ball, dist_eq_norm] at hbY
      have h1 : |V Y - V b| ≤ Λ * ‖Y - b‖ := hVlipg Y b
      have h2 : |u (ι j) b - u (ι j) Y| ≤ Λ * ‖Y - b‖ := by
        have := hudist (ι j) b Y
        rwa [show ‖b - Y‖ = ‖Y - b‖ by rw [← norm_neg]; simp] at this
      have h3 : |V b - u (ι j) b| < ε / 3 := by
        have := hj b hbN; rwa [Real.dist_eq] at this
      have hb : Λ * ‖Y - b‖ ≤ ε / 3 := by
        have hpos : (0:ℝ) < 3 * (Λ + 1) := by positivity
        refine (mul_le_mul_of_nonneg_left hd.le hΛ0).trans ?_
        rw [show Λ * (ε / (3 * (Λ + 1))) = Λ * ε / (3 * (Λ + 1)) by ring, div_le_iff₀ hpos]
        nlinarith [hε.le, hΛ0]
      rw [Real.dist_eq]
      calc |V Y - u (ι j) Y|
          ≤ |V Y - V b| + |V b - u (ι j) b| + |u (ι j) b - u (ι j) Y| := by
            linarith [abs_sub_le (V Y) (V b) (u (ι j) b),
              abs_sub_le (V Y) (u (ι j) b) (u (ι j) Y)]
        _ < ε := by linarith
    -- (f) transfer from the extensions back to the blow-ups
    refine ⟨ι, V, hιmono, fun K hK => ?_⟩
    obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall (0 : E)
    have hKR : K ⊆ closedBall (0 : E) (max R0 1) :=
      hR0.trans (closedBall_subset_closedBall (le_max_left _ _))
    have hRge1 : (1 : ℝ) ≤ max R0 1 := le_max_right _ _
    have hρι : Tendsto (fun j => ρ (ι j)) atTop (𝓝 0) := hρ0.comp hιmono.tendsto_atTop
    have hev : ∀ᶠ j in atTop, max R0 1 ≤ σ / ρ (ι j) := by
      have hpos : 0 < σ / max R0 1 := by positivity
      filter_upwards [Metric.tendsto_nhds.mp hρι (σ / max R0 1) hpos] with j hj
      rw [Real.dist_eq, sub_zero, abs_of_pos (hρpos (ι j))] at hj
      rw [le_div_iff₀ (hρpos (ι j))]
      rw [lt_div_iff₀ (by linarith : (0:ℝ) < max R0 1)] at hj
      linarith
    refine (huuc K hK).congr ?_
    filter_upwards [hev] with j hj Y hY
    exact (hueq (ι j) (closedBall_subset_closedBall hj (hKR hY))).symm
  -- ===================== PART (1) =====================
  -- A restriction lemma: infinity-harmonicity passes to open subsets.
  have hrestrict : ∀ (Ω Ω' : Set E) (f : E → ℝ), IsInfHarmonicOn Ω f → IsOpen Ω' → Ω' ⊆ Ω →
      IsInfHarmonicOn Ω' f := by
    intro Ω Ω' f hf hΩ' hsubΩ
    have hc : ContinuousOn f Ω := hf.1.2.1
    refine ⟨⟨hΩ', hc.mono hsubΩ, ?_⟩, ⟨hΩ', hc.mono hsubΩ, ?_⟩⟩
    · intro ζ hζ φ hφ hmax
      refine hf.1.2.2 ζ (hsubΩ hζ) φ hφ ?_
      have h : IsLocalMax (fun x => f x - φ x) ζ := by
        rw [IsLocalMaxOn, IsMaxFilter, hΩ'.nhdsWithin_eq hζ] at hmax; exact hmax
      exact h.on Ω
    · intro ζ hζ φ hφ hmin
      refine hf.2.2.2 ζ (hsubΩ hζ) φ hφ ?_
      have h : IsLocalMin (fun x => f x - φ x) ζ := by
        rw [IsLocalMinOn, IsMinFilter, hΩ'.nhdsWithin_eq hζ] at hmin; exact hmin
      exact h.on Ω
  -- a tail of a locally uniformly convergent sequence converges to the same limit
  have htail : ∀ (F : ℕ → E → ℝ) (f : E → ℝ) (s : Set E) (m : ℕ),
      TendstoUniformlyOn F f atTop s → TendstoUniformlyOn (fun j => F (j + m)) f atTop s := by
    intro F f s m h
    rw [Metric.tendstoUniformlyOn_iff] at h ⊢
    intro ε hε
    exact (tendsto_add_atTop_nat m).eventually (h ε hε)
  refine ⟨?_, part2⟩
  intro ρ V hρpos hρ0 huc
  -- eventual admissibility of a radius
  have hevR : ∀ R : ℝ, 0 < R → ∀ᶠ i in atTop, ρ i * R ≤ σ := by
    intro R hR
    filter_upwards [Metric.tendsto_nhds.mp hρ0 (σ / R) (by positivity)] with i hi
    rw [Real.dist_eq, sub_zero, abs_of_pos (hρpos i)] at hi
    rw [← le_div_iff₀ hR] at *
    exact hi.le
  -- (A) `V` is `Λ`-Lipschitz and vanishes at the origin
  have hVlip : ∀ a b : E, |V a - V b| ≤ Λ * ‖a - b‖ := by
    intro a b
    have hR : (0:ℝ) < max (max ‖a‖ ‖b‖) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have ha : a ∈ closedBall (0:E) (max (max ‖a‖ ‖b‖) 1) := by
      rw [mem_closedBall, dist_zero_right]
      exact le_trans (le_max_left _ _) (le_max_left _ _)
    have hb : b ∈ closedBall (0:E) (max (max ‖a‖ ‖b‖) 1) := by
      rw [mem_closedBall, dist_zero_right]
      exact le_trans (le_max_right _ _) (le_max_left _ _)
    have hucR := huc _ (isCompact_closedBall (0:E) (max (max ‖a‖ ‖b‖) 1))
    have hT : Tendsto (fun i => |(w (z + ρ i • a) - w z) / ρ i
        - (w (z + ρ i • b) - w z) / ρ i|) atTop (𝓝 |V a - V b|) :=
      (continuous_abs.continuousAt.tendsto).comp
        ((hucR.tendsto_at ha).sub (hucR.tendsto_at hb))
    refine le_of_tendsto hT ?_
    filter_upwards [hevR _ hR] with i hi
    have := hblip (ρ i) (max (max ‖a‖ ‖b‖) 1) (hρpos i) hi a ha b hb
    rwa [Real.dist_eq, dist_eq_norm] at this
  have hVcont : Continuous V := by
    refine LipschitzWith.continuous (K := Real.toNNReal Λ) ?_
    refine LipschitzWith.of_dist_le_mul ?_
    intro a b
    rw [Real.coe_toNNReal Λ hΛ0, Real.dist_eq, dist_eq_norm]
    exact hVlip a b
  have hV0' : V 0 = 0 := by
    have hucR := huc _ (isCompact_closedBall (0:E) 1)
    have h := hucR.tendsto_at (mem_closedBall_self zero_le_one)
    have hz : ∀ i, (w (z + ρ i • (0:E)) - w z) / ρ i = 0 := fun i => hV0 (ρ i)
    simp only [hz] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  -- (C) Step 4: `V` is infinity-harmonic on all of `E`
  have hVharm : IsInfHarmonicOn (univ : Set E) V := by
    have hpre : ∀ i : ℕ, IsInfHarmonicOn ((fun Y : E => z + ρ i • Y) ⁻¹' D)
        (fun Y : E => (w (z + ρ i • Y) - w z) / ρ i) := fun i =>
      InfHarmonicNormalize _ _ (InfHarmonicRescale D w hw z (ρ i) (hρpos i)) (w z) (ρ i)
        (hρpos i)
    have hsubpre : ∀ (i : ℕ) (R : ℝ), ρ i * R ≤ σ →
        ball (0:E) R ⊆ (fun Y : E => z + ρ i • Y) ⁻¹' D := by
      intro i R hi Y hY
      rw [mem_ball, dist_zero_right] at hY
      refine hball (closedBall_subset_closedBall (by linarith : σ ≤ 2 * σ) ?_)
      exact hmemball (ρ i) R (hρpos i) hi Y
        (by rw [mem_closedBall, dist_zero_right]; exact hY.le)
    have hballharm : ∀ R : ℝ, 0 < R → IsInfHarmonicOn (ball (0:E) R) V := by
      intro R hR
      obtain ⟨i₀, hi₀⟩ := eventually_atTop.mp (hevR R hR)
      refine InfHarmonicStability (ball (0:E) R) isOpen_ball
        (fun j Y => (w (z + ρ (j + i₀) • Y) - w z) / ρ (j + i₀)) V ?_ ?_
      · intro j
        exact hrestrict _ _ _ (hpre (j + i₀)) isOpen_ball
          (hsubpre (j + i₀) R (hi₀ (j + i₀) (by omega)))
      · intro K _ hK
        exact htail (fun i Y => (w (z + ρ i • Y) - w z) / ρ i) V K i₀ (huc K hK)
    refine ⟨⟨isOpen_univ, hVcont.continuousOn, ?_⟩, ⟨isOpen_univ, hVcont.continuousOn, ?_⟩⟩
    · intro ζ _ φ hφ hmax
      have hR : (0:ℝ) < ‖ζ‖ + 1 := by positivity
      have hζ : ζ ∈ ball (0:E) (‖ζ‖ + 1) := by rw [mem_ball, dist_zero_right]; linarith
      refine (hballharm _ hR).1.2.2 ζ hζ φ hφ ?_
      have h : IsLocalMax (fun x => V x - φ x) ζ := by
        rw [IsLocalMaxOn, IsMaxFilter, nhdsWithin_univ] at hmax; exact hmax
      exact h.on _
    · intro ζ _ φ hφ hmin
      have hR : (0:ℝ) < ‖ζ‖ + 1 := by positivity
      have hζ : ζ ∈ ball (0:E) (‖ζ‖ + 1) := by rw [mem_ball, dist_zero_right]; linarith
      refine (hballharm _ hR).2.2.2 ζ hζ φ hφ ?_
      have h : IsLocalMin (fun x => V x - φ x) ζ := by
        rw [IsLocalMinOn, IsMinFilter, nhdsWithin_univ] at hmin; exact hmin
      exact h.on _
  -- (D) Step 5: the common slope limit of `w` at `z`, and the cone bound for `V`
  obtain ⟨Ls, hLs0, hLsU, hLsL⟩ := ConeSlopeLimitEq D w hw z hz
  have hballD : ∀ r : ℝ, r ≤ σ → closedBall z r ⊆ D := fun r hrσ =>
    (closedBall_subset_closedBall (by linarith)).trans hball
  have htendU : ∀ R : ℝ, 0 < R →
      Tendsto (fun i => ConeSlopeUpper w z (ρ i * R)) atTop (𝓝 Ls) := by
    intro R hR
    refine hLsU.comp ?_
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using hρ0.mul_const R,
      Eventually.of_forall fun i => mul_pos (hρpos i) hR⟩
  have htendL : ∀ R : ℝ, 0 < R →
      Tendsto (fun i => ConeSlopeLower w z (ρ i * R)) atTop (𝓝 Ls) := by
    intro R hR
    refine hLsL.comp ?_
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using hρ0.mul_const R,
      Eventually.of_forall fun i => mul_pos (hρpos i) hR⟩
  have hcone : ∀ Y : E, |V Y| ≤ Ls * ‖Y‖ := by
    intro Y
    have hR : (0:ℝ) < max ‖Y‖ 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hYR : Y ∈ closedBall (0:E) (max ‖Y‖ 1) := by
      rw [mem_closedBall, dist_zero_right]; exact le_max_left _ _
    have hptw := (huc _ (isCompact_closedBall (0:E) (max ‖Y‖ 1))).tendsto_at hYR
    have hZmem : ∀ i : ℕ, ρ i * max ‖Y‖ 1 ≤ σ →
        z + ρ i • Y ∈ closedBall z (ρ i * max ‖Y‖ 1) := by
      intro i hi
      rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_of_pos (hρpos i)]
      exact mul_le_mul_of_nonneg_left (le_max_left _ _) (hρpos i).le
    have hnrm : ∀ i : ℕ, ‖z + ρ i • Y - z‖ = ρ i * ‖Y‖ := by
      intro i
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (hρpos i)]
    have hupper : V Y ≤ Ls * ‖Y‖ := by
      refine le_of_tendsto_of_tendsto hptw ((htendU _ hR).mul_const ‖Y‖) ?_
      filter_upwards [hevR _ hR] with i hi
      obtain ⟨hup, -, -⟩ := ConeComparison D w hw z (ρ i * max ‖Y‖ 1)
        (mul_pos (hρpos i) hR) (hballD _ hi)
      have h := hup _ (hZmem i hi)
      rw [hnrm i] at h
      rw [div_le_iff₀ (hρpos i)]
      calc w (z + ρ i • Y) - w z
          ≤ ConeSlopeUpper w z (ρ i * max ‖Y‖ 1) * (ρ i * ‖Y‖) := h
        _ = ConeSlopeUpper w z (ρ i * max ‖Y‖ 1) * ‖Y‖ * ρ i := by ring
    have hlower : -V Y ≤ Ls * ‖Y‖ := by
      refine le_of_tendsto_of_tendsto hptw.neg ((htendL _ hR).mul_const ‖Y‖) ?_
      filter_upwards [hevR _ hR] with i hi
      obtain ⟨-, hlo, -⟩ := ConeComparison D w hw z (ρ i * max ‖Y‖ 1)
        (mul_pos (hρpos i) hR) (hballD _ hi)
      have h := hlo _ (hZmem i hi)
      rw [hnrm i] at h
      rw [neg_div' , div_le_iff₀ (hρpos i)]
      calc -(w (z + ρ i • Y) - w z)
          ≤ ConeSlopeLower w z (ρ i * max ‖Y‖ 1) * (ρ i * ‖Y‖) := h
        _ = ConeSlopeLower w z (ρ i * max ‖Y‖ 1) * ‖Y‖ * ρ i := by ring
    exact abs_le.mpr ⟨by linarith, hupper⟩
  -- (E) Step 6: every cone slope of `V` is at most `Ls`, hence `V` is globally
  -- `Ls`-Lipschitz.
  have hslopebd : ∀ (q : E) (T0 : ℝ), 0 < T0 →
      ConeSlopeUpper V q T0 ≤ Ls ∧ ConeSlopeLower V q T0 ≤ Ls := by
    intro q T0 hT0
    have hlim : Tendsto (fun T : ℝ => (Ls * (T + ‖q‖) + |V q|) / T) atTop (𝓝 Ls) := by
      have hcg : ∀ᶠ T : ℝ in atTop,
          (Ls * (T + ‖q‖) + |V q|) / T = Ls + (Ls * ‖q‖ + |V q|) / T := by
        filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
        field_simp
        ring
      rw [tendsto_congr' hcg]
      simpa using tendsto_const_nhds.add
        (Tendsto.const_div_atTop (tendsto_id (α := ℝ)) (Ls * ‖q‖ + |V q|))
    have hbdU : ∀ T : ℝ, 0 < T → ConeSlopeUpper V q T ≤ (Ls * (T + ‖q‖) + |V q|) / T := by
      intro T hT
      simp only [ConeSlopeUpper]
      refine csSup_le ⟨(V (q + 0) - V q) / T, ⟨0, mem_closedBall_self hT.le, rfl⟩⟩ ?_
      rintro x ⟨h, hh, rfl⟩
      show (V (q + h) - V q) / T ≤ (Ls * (T + ‖q‖) + |V q|) / T
      rw [mem_closedBall, dist_zero_right] at hh
      have h1 : |V (q + h)| ≤ Ls * ‖q + h‖ := hcone _
      have h2 : ‖q + h‖ ≤ ‖q‖ + T := le_trans (norm_add_le _ _) (by linarith)
      have h3 : Ls * ‖q + h‖ ≤ Ls * (‖q‖ + T) := mul_le_mul_of_nonneg_left h2 hLs0
      have h4 : -|V q| ≤ V q := neg_abs_le _
      gcongr
      have := abs_le.mp h1
      linarith [this.2]
    have hbdL : ∀ T : ℝ, 0 < T → ConeSlopeLower V q T ≤ (Ls * (T + ‖q‖) + |V q|) / T := by
      intro T hT
      simp only [ConeSlopeLower]
      refine csSup_le ⟨(-(V (q + 0) - V q)) / T, ⟨0, mem_closedBall_self hT.le, rfl⟩⟩ ?_
      rintro x ⟨h, hh, rfl⟩
      show (-(V (q + h) - V q)) / T ≤ (Ls * (T + ‖q‖) + |V q|) / T
      rw [mem_closedBall, dist_zero_right] at hh
      have h1 : |V (q + h)| ≤ Ls * ‖q + h‖ := hcone _
      have h2 : ‖q + h‖ ≤ ‖q‖ + T := le_trans (norm_add_le _ _) (by linarith)
      have h3 : Ls * ‖q + h‖ ≤ Ls * (‖q‖ + T) := mul_le_mul_of_nonneg_left h2 hLs0
      have h4 : V q ≤ |V q| := le_abs_self _
      gcongr
      have := abs_le.mp h1
      linarith [this.1]
    have hmono : ∀ T : ℝ, T0 ≤ T → ConeSlopeUpper V q T0 ≤ ConeSlopeUpper V q T
        ∧ ConeSlopeLower V q T0 ≤ ConeSlopeLower V q T := by
      intro T hT
      obtain ⟨-, -, hm⟩ := ConeComparison univ V hVharm q T0 hT0 (subset_univ _)
      exact hm T hT (subset_univ _)
    constructor
    · refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop T0, eventually_gt_atTop (0:ℝ)] with T hT hTpos
      exact le_trans (hmono T hT).1 (hbdU T hTpos)
    · refine ge_of_tendsto hlim ?_
      filter_upwards [eventually_ge_atTop T0, eventually_gt_atTop (0:ℝ)] with T hT hTpos
      exact le_trans (hmono T hT).2 (hbdL T hTpos)
  have hglob : ∀ Q q : E, |V Q - V q| ≤ Ls * ‖Q - q‖ := by
    intro Q q
    rcases eq_or_ne Q q with rfl | hne
    · simp
    · have hT0 : (0:ℝ) < ‖Q - q‖ := by
        rw [norm_pos_iff]; exact sub_ne_zero_of_ne hne
      obtain ⟨hup, hlo, -⟩ := ConeComparison univ V hVharm q (‖Q - q‖) hT0 (subset_univ _)
      have hQmem : Q ∈ closedBall q ‖Q - q‖ := by
        rw [mem_closedBall, dist_eq_norm]
      have h1 := hup Q hQmem
      have h2 := hlo Q hQmem
      obtain ⟨hsU, hsL⟩ := hslopebd q (‖Q - q‖) hT0
      have h3 : ConeSlopeUpper V q ‖Q - q‖ * ‖Q - q‖ ≤ Ls * ‖Q - q‖ :=
        mul_le_mul_of_nonneg_right hsU hT0.le
      have h4 : ConeSlopeLower V q ‖Q - q‖ * ‖Q - q‖ ≤ Ls * ‖Q - q‖ :=
        mul_le_mul_of_nonneg_right hsL hT0.le
      exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the cone slopes of `w` at `z` are attained (continuous function on a compact ball)
  have hmemD : ∀ (r : ℝ), r ≤ σ → ∀ h ∈ closedBall (0:E) r, z + h ∈ D := by
    intro r hrσ h hh
    rw [mem_closedBall, dist_zero_right] at hh
    exact hballD r hrσ (by rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]; exact hh)
  have hcontshift : ∀ (r : ℝ), r ≤ σ →
      ContinuousOn (fun h : E => w (z + h)) (closedBall (0:E) r) := by
    intro r hrσ
    exact hcw.comp (by fun_prop) fun h hh => hmemD r hrσ h hh
  have hattw : ∀ r : ℝ, 0 < r → r ≤ σ →
      (∃ k : E, ‖k‖ ≤ r ∧ (w (z + k) - w z) / r = ConeSlopeUpper w z r) := by
    intro r hr hrσ
    have hKc : IsCompact (closedBall (0:E) r) := isCompact_closedBall _ _
    have hKn : (closedBall (0:E) r).Nonempty := ⟨0, mem_closedBall_self hr.le⟩
    have hcf : ContinuousOn (fun h : E => (w (z + h) - w z) / r) (closedBall (0:E) r) :=
      ((hcontshift r hrσ).sub continuousOn_const).div_const _
    obtain ⟨k, hk, hkmax⟩ := hKc.exists_isMaxOn hKn hcf
    refine ⟨k, by rw [mem_closedBall, dist_zero_right] at hk; exact hk, ?_⟩
    have hg : IsGreatest ((fun h : E => (w (z + h) - w z) / r) '' closedBall (0:E) r)
        ((w (z + k) - w z) / r) := by
      refine ⟨⟨k, hk, rfl⟩, ?_⟩
      rintro x ⟨h, hh, rfl⟩
      exact hkmax hh
    simp only [ConeSlopeUpper]
    exact hg.csSup_eq.symm
  have hattwL : ∀ r : ℝ, 0 < r → r ≤ σ →
      (∃ k : E, ‖k‖ ≤ r ∧ (-(w (z + k) - w z)) / r = ConeSlopeLower w z r) := by
    intro r hr hrσ
    have hKc : IsCompact (closedBall (0:E) r) := isCompact_closedBall _ _
    have hKn : (closedBall (0:E) r).Nonempty := ⟨0, mem_closedBall_self hr.le⟩
    have hcf : ContinuousOn (fun h : E => (-(w (z + h) - w z)) / r) (closedBall (0:E) r) :=
      (((hcontshift r hrσ).sub continuousOn_const).neg).div_const _
    obtain ⟨k, hk, hkmax⟩ := hKc.exists_isMaxOn hKn hcf
    refine ⟨k, by rw [mem_closedBall, dist_zero_right] at hk; exact hk, ?_⟩
    have hg : IsGreatest ((fun h : E => (-(w (z + h) - w z)) / r) '' closedBall (0:E) r)
        ((-(w (z + k) - w z)) / r) := by
      refine ⟨⟨k, hk, rfl⟩, ?_⟩
      rintro x ⟨h, hh, rfl⟩
      exact hkmax hh
    simp only [ConeSlopeLower]
    exact hg.csSup_eq.symm
  -- Step 8 input: the extreme values `Ls * R` and `-(Ls * S)` are attained by `V`.
  have hattV : ∀ R : ℝ, 0 < R → ∃ x : E, ‖x‖ ≤ R ∧ V x = Ls * R := by
    intro R hR
    obtain ⟨Y, hYmem, hYeq⟩ : ∃ Y : ℕ → E, (∀ i, ‖Y i‖ ≤ R) ∧ ∀ i, ρ i * R ≤ σ →
        (w (z + ρ i • Y i) - w z) / ρ i = ConeSlopeUpper w z (ρ i * R) * R := by
      have hch : ∀ i : ℕ, ∃ y : E, ‖y‖ ≤ R ∧ (ρ i * R ≤ σ →
          (w (z + ρ i • y) - w z) / ρ i = ConeSlopeUpper w z (ρ i * R) * R) := by
        intro i
        by_cases hi : ρ i * R ≤ σ
        · obtain ⟨k, hk, hkeq⟩ := hattw (ρ i * R) (mul_pos (hρpos i) hR) hi
          refine ⟨(ρ i)⁻¹ • k, ?_, fun _ => ?_⟩
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos i)),
              inv_mul_le_iff₀ (hρpos i)]
            calc ‖k‖ ≤ ρ i * R := hk
              _ = ρ i * R := rfl
          · rw [smul_inv_smul₀ (ne_of_gt (hρpos i))]
            rw [← hkeq]
            field_simp
        · exact ⟨0, by simpa using hR.le, fun h => absurd h hi⟩
      choose Y h1 h2 using hch
      exact ⟨Y, h1, h2⟩
    have hVYtend : Tendsto (fun i => V (Y i)) atTop (𝓝 (Ls * R)) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hucR := huc _ (isCompact_closedBall (0:E) R)
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hucR (ε / 2) (by positivity),
        Metric.tendsto_nhds.mp ((htendU R hR).mul_const R) (ε / 2) (by positivity),
        hevR R hR] with i hi1 hi2 hi3
      have hmem : Y i ∈ closedBall (0:E) R := by
        rw [mem_closedBall, dist_zero_right]; exact hYmem i
      have ha : dist (V (Y i)) ((w (z + ρ i • Y i) - w z) / ρ i) < ε / 2 := hi1 (Y i) hmem
      rw [hYeq i hi3] at ha
      calc dist (V (Y i)) (Ls * R)
          ≤ dist (V (Y i)) (ConeSlopeUpper w z (ρ i * R) * R)
            + dist (ConeSlopeUpper w z (ρ i * R) * R) (Ls * R) := dist_triangle _ _ _
        _ < ε := by linarith
    obtain ⟨x, hx, hxmax⟩ := (isCompact_closedBall (0:E) R).exists_isMaxOn
      ⟨0, mem_closedBall_self hR.le⟩ hVcont.continuousOn
    have hxn : ‖x‖ ≤ R := by rw [mem_closedBall, dist_zero_right] at hx; exact hx
    refine ⟨x, hxn, ?_⟩
    have hle : V x ≤ Ls * R := by
      have h1 : V x ≤ Ls * ‖x‖ := (abs_le.mp (hcone x)).2
      nlinarith [hLs0, hxn, norm_nonneg x]
    have hge : Ls * R ≤ V x := by
      refine le_of_tendsto hVYtend (Eventually.of_forall fun i => ?_)
      exact hxmax (by rw [mem_closedBall, dist_zero_right]; exact hYmem i)
    linarith
  have hattVL : ∀ S : ℝ, 0 < S → ∃ y : E, ‖y‖ ≤ S ∧ V y = -(Ls * S) := by
    intro S hS
    obtain ⟨Y, hYmem, hYeq⟩ : ∃ Y : ℕ → E, (∀ i, ‖Y i‖ ≤ S) ∧ ∀ i, ρ i * S ≤ σ →
        (w (z + ρ i • Y i) - w z) / ρ i = -(ConeSlopeLower w z (ρ i * S) * S) := by
      have hch : ∀ i : ℕ, ∃ y : E, ‖y‖ ≤ S ∧ (ρ i * S ≤ σ →
          (w (z + ρ i • y) - w z) / ρ i = -(ConeSlopeLower w z (ρ i * S) * S)) := by
        intro i
        by_cases hi : ρ i * S ≤ σ
        · obtain ⟨k, hk, hkeq⟩ := hattwL (ρ i * S) (mul_pos (hρpos i) hS) hi
          refine ⟨(ρ i)⁻¹ • k, ?_, fun _ => ?_⟩
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hρpos i)),
              inv_mul_le_iff₀ (hρpos i)]
            exact hk
          · rw [smul_inv_smul₀ (ne_of_gt (hρpos i))]
            rw [← hkeq]
            field_simp
        · exact ⟨0, by simpa using hS.le, fun h => absurd h hi⟩
      choose Y h1 h2 using hch
      exact ⟨Y, h1, h2⟩
    have hVYtend : Tendsto (fun i => V (Y i)) atTop (𝓝 (-(Ls * S))) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      have hucR := huc _ (isCompact_closedBall (0:E) S)
      filter_upwards [Metric.tendstoUniformlyOn_iff.mp hucR (ε / 2) (by positivity),
        Metric.tendsto_nhds.mp (((htendL S hS).mul_const S).neg) (ε / 2) (by positivity),
        hevR S hS] with i hi1 hi2 hi3
      have hmem : Y i ∈ closedBall (0:E) S := by
        rw [mem_closedBall, dist_zero_right]; exact hYmem i
      have ha : dist (V (Y i)) ((w (z + ρ i • Y i) - w z) / ρ i) < ε / 2 := hi1 (Y i) hmem
      rw [hYeq i hi3] at ha
      calc dist (V (Y i)) (-(Ls * S))
          ≤ dist (V (Y i)) (-(ConeSlopeLower w z (ρ i * S) * S))
            + dist (-(ConeSlopeLower w z (ρ i * S) * S)) (-(Ls * S)) := dist_triangle _ _ _
        _ < ε := by linarith
    obtain ⟨y, hy, hymin⟩ := (isCompact_closedBall (0:E) S).exists_isMinOn
      ⟨0, mem_closedBall_self hS.le⟩ hVcont.continuousOn
    have hyn : ‖y‖ ≤ S := by rw [mem_closedBall, dist_zero_right] at hy; exact hy
    refine ⟨y, hyn, ?_⟩
    have hge : -(Ls * S) ≤ V y := by
      have h1 : -(Ls * ‖y‖) ≤ V y := (abs_le.mp (hcone y)).1
      nlinarith [hLs0, hyn, norm_nonneg y]
    have hle : V y ≤ -(Ls * S) := by
      refine ge_of_tendsto hVYtend (Eventually.of_forall fun i => ?_)
      exact hymin (by rw [mem_closedBall, dist_zero_right]; exact hYmem i)
    linarith
  -- Step 7: the degenerate case `Ls = 0`.
  rcases eq_or_lt_of_le hLs0 with hLseq | hLspos
  · refine ⟨0, fun Y => ?_⟩
    have := hcone Y
    rw [← hLseq] at this
    simp only [zero_mul, abs_nonpos_iff] at this
    simp [this]
  -- Step 8: `Ls > 0`; a distinguished unit direction.
  -- the equality chain forces the extremal competitors onto a single ray
  have hray : ∀ (R S : ℝ), 0 < R → 0 < S → ∀ x y : E, ‖x‖ ≤ R → ‖y‖ ≤ S →
      V x = Ls * R → V y = -(Ls * S) → ‖x‖ = R ∧ ‖y‖ = S ∧ ‖x + -y‖ = ‖x‖ + ‖-y‖ := by
    intro R S hR hS x y hxn hyn hxv hyv
    have h1 : |V x - V y| ≤ Ls * ‖x - y‖ := hglob x y
    have h2 : V x - V y = Ls * (R + S) := by rw [hxv, hyv]; ring
    have h3 : Ls * (R + S) ≤ Ls * ‖x - y‖ := by
      have := (abs_le.mp h1).2
      linarith
    have h4 : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := by
      calc ‖x - y‖ = ‖x + -y‖ := by rw [sub_eq_add_neg]
        _ ≤ ‖x‖ + ‖-y‖ := norm_add_le _ _
        _ = ‖x‖ + ‖y‖ := by rw [norm_neg]
    have h5 : Ls * ‖x - y‖ ≤ Ls * (‖x‖ + ‖y‖) := mul_le_mul_of_nonneg_left h4 hLs0
    have h6 : Ls * (‖x‖ + ‖y‖) ≤ Ls * (R + S) :=
      mul_le_mul_of_nonneg_left (by linarith) hLs0
    have heqs : ‖x‖ + ‖y‖ = R + S := by
      have := le_antisymm (by linarith : Ls * (‖x‖ + ‖y‖) ≤ Ls * (R + S))
        (by linarith : Ls * (R + S) ≤ Ls * (‖x‖ + ‖y‖))
      exact mul_left_cancel₀ (ne_of_gt hLspos) this
    have hxR : ‖x‖ = R := by linarith [heqs, hxn, hyn]
    have hyS : ‖y‖ = S := by linarith [heqs, hxn, hyn]
    refine ⟨hxR, hyS, ?_⟩
    have h7 : Ls * (‖x‖ + ‖y‖) ≤ Ls * ‖x - y‖ := by rw [hxR, hyS]; linarith
    have h8 : ‖x‖ + ‖y‖ ≤ ‖x - y‖ := le_of_mul_le_mul_left (by linarith) hLspos
    have h9 : ‖x + -y‖ = ‖x - y‖ := by rw [sub_eq_add_neg]
    rw [h9, norm_neg]
    linarith [h4, h8]
  obtain ⟨y1, hy1n, hy1v⟩ := hattVL 1 one_pos
  obtain ⟨x1, hx1n, hx1v⟩ := hattV 1 one_pos
  obtain ⟨hx1R, hy1S, htri1⟩ := hray 1 1 one_pos one_pos x1 y1 hx1n hy1n hx1v hy1v
  have hen : ‖(-y1 : E)‖ = 1 := by rw [norm_neg]; exact hy1S
  have hx1e : x1 = -y1 := by
    have h := norm_add_eq_iff_real.mp htri1
    rw [norm_neg, hy1S, one_smul, hx1R, one_smul] at h
    exact h
  -- `V` is linear with slope `Ls` along the ray through `e = -y1`
  have hVray : ∀ τ : ℝ, V (τ • (-y1 : E)) = Ls * τ := by
    intro τ
    rcases lt_trichotomy τ 0 with hτ | hτ | hτ
    · obtain ⟨yS, hySn, hySv⟩ := hattVL (-τ) (by linarith)
      obtain ⟨-, hySS, htri⟩ := hray 1 (-τ) one_pos (by linarith) x1 yS hx1n hySn hx1v hySv
      have h := norm_add_eq_iff_real.mp htri
      rw [norm_neg, hySS, hx1R, one_smul, hx1e] at h
      have hyS : yS = τ • (-y1 : E) := by
        have h2 : -yS = (-τ) • (-y1 : E) := h.symm
        have h3 : yS = -((-τ) • (-y1 : E)) := by rw [← h2]; simp
        rw [h3]; module
      rw [← hyS, hySv]; ring
    · rw [hτ]; simpa using hV0'
    · obtain ⟨xR, hxRn, hxRv⟩ := hattV τ hτ
      obtain ⟨hxRR, -, htri⟩ := hray τ 1 hτ one_pos xR y1 hxRn hy1n hxRv hy1v
      have h := norm_add_eq_iff_real.mp htri
      rw [norm_neg, hy1S, one_smul, hxRR] at h
      rw [← h, hxRv]
  -- Step 9: `V` is the continuous linear functional `Ls * ⟪e, ·⟫`.
  refine ⟨Ls • innerSL ℝ (-y1 : E), fun Y => ?_⟩
  have hbound : ∀ τ : ℝ, |V Y - Ls * τ| ≤ Ls * ‖Y - τ • (-y1 : E)‖ := by
    intro τ
    have h := hglob Y (τ • (-y1 : E))
    rwa [hVray τ] at h
  have hsq : ∀ τ : ℝ, ‖Y - τ • (-y1 : E)‖ ^ 2
      = ‖Y‖ ^ 2 - 2 * τ * (inner ℝ (-y1 : E) Y : ℝ) + τ ^ 2 := by
    intro τ
    rw [norm_sub_sq_real, norm_smul, real_inner_smul_right, hen]
    simp [real_inner_comm Y (-y1 : E)]
    ring
  have hdiv : Tendsto (fun τ : ℝ => Ls * ‖Y‖ ^ 2 / (2 * τ)) atTop (𝓝 0) :=
    Tendsto.const_div_atTop (Tendsto.const_mul_atTop two_pos (tendsto_id (α := ℝ))) _
  -- the lower bound, letting `τ → +∞`
  have hge : Ls * (inner ℝ (-y1 : E) Y : ℝ) ≤ V Y := by
    refine le_of_tendsto (?_ : Tendsto
      (fun τ : ℝ => Ls * (inner ℝ (-y1 : E) Y : ℝ) - Ls * ‖Y‖ ^ 2 / (2 * τ)) atTop
      (𝓝 (Ls * (inner ℝ (-y1 : E) Y : ℝ)))) ?_
    · simpa using tendsto_const_nhds.sub hdiv
    · filter_upwards [eventually_gt_atTop (0:ℝ),
        eventually_ge_atTop (|(inner ℝ (-y1 : E) Y : ℝ)| + 1)] with τ hτ hτ2
      have hnn : 0 ≤ τ - (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * τ) := by
        have h1 : (inner ℝ (-y1 : E) Y : ℝ) ≤ |(inner ℝ (-y1 : E) Y : ℝ)| := le_abs_self _
        have h2 : (0:ℝ) ≤ ‖Y‖ ^ 2 / (2 * τ) := by positivity
        linarith
      have hle : ‖Y - τ • (-y1 : E)‖ ≤ τ - (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * τ) := by
        have hkey : ‖Y - τ • (-y1 : E)‖ ^ 2
            ≤ (τ - (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * τ)) ^ 2 := by
          rw [hsq τ]
          have hid : (τ - (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * τ)) ^ 2
              - (‖Y‖ ^ 2 - 2 * τ * (inner ℝ (-y1 : E) Y : ℝ) + τ ^ 2)
              = ((inner ℝ (-y1 : E) Y : ℝ) - ‖Y‖ ^ 2 / (2 * τ)) ^ 2 := by
            field_simp; ring
          nlinarith [sq_nonneg ((inner ℝ (-y1 : E) Y : ℝ) - ‖Y‖ ^ 2 / (2 * τ)), hid]
        nlinarith [norm_nonneg (Y - τ • (-y1 : E)), hnn, hkey]
      have h3 := (abs_le.mp (hbound τ)).1
      have h4 : Ls * ‖Y - τ • (-y1 : E)‖
          ≤ Ls * (τ - (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * τ)) :=
        mul_le_mul_of_nonneg_left hle hLs0
      have h5 : Ls * (τ - (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * τ))
          = Ls * τ - Ls * (inner ℝ (-y1 : E) Y : ℝ) + Ls * ‖Y‖ ^ 2 / (2 * τ) := by ring
      linarith
  -- the upper bound, letting `τ = -s` with `s → +∞`
  have hle' : V Y ≤ Ls * (inner ℝ (-y1 : E) Y : ℝ) := by
    refine ge_of_tendsto (?_ : Tendsto
      (fun s : ℝ => Ls * (inner ℝ (-y1 : E) Y : ℝ) + Ls * ‖Y‖ ^ 2 / (2 * s)) atTop
      (𝓝 (Ls * (inner ℝ (-y1 : E) Y : ℝ)))) ?_
    · simpa using tendsto_const_nhds.add hdiv
    · filter_upwards [eventually_gt_atTop (0:ℝ),
        eventually_ge_atTop (|(inner ℝ (-y1 : E) Y : ℝ)| + 1)] with s hs hs2
      have hnn : 0 ≤ s + (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s) := by
        have h1 : -|(inner ℝ (-y1 : E) Y : ℝ)| ≤ (inner ℝ (-y1 : E) Y : ℝ) := neg_abs_le _
        have h2 : (0:ℝ) ≤ ‖Y‖ ^ 2 / (2 * s) := by positivity
        linarith
      have hle : ‖Y - (-s) • (-y1 : E)‖
          ≤ s + (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s) := by
        have hkey : ‖Y - (-s) • (-y1 : E)‖ ^ 2
            ≤ (s + (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s)) ^ 2 := by
          rw [hsq (-s)]
          have hid : (s + (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s)) ^ 2
              - (‖Y‖ ^ 2 - 2 * (-s) * (inner ℝ (-y1 : E) Y : ℝ) + (-s) ^ 2)
              = ((inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s)) ^ 2 := by
            field_simp; ring
          nlinarith [sq_nonneg ((inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s)), hid]
        nlinarith [norm_nonneg (Y - (-s) • (-y1 : E)), hnn, hkey]
      have h3 := (abs_le.mp (hbound (-s))).2
      have h4 : Ls * ‖Y - (-s) • (-y1 : E)‖
          ≤ Ls * (s + (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s)) :=
        mul_le_mul_of_nonneg_left hle hLs0
      have h5 : Ls * (s + (inner ℝ (-y1 : E) Y : ℝ) + ‖Y‖ ^ 2 / (2 * s))
          = Ls * s + Ls * (inner ℝ (-y1 : E) Y : ℝ) + Ls * ‖Y‖ ^ 2 / (2 * s) := by ring
      linarith
  have hVY : V Y = Ls * (inner ℝ (-y1 : E) Y : ℝ) := le_antisymm hle' hge
  rw [hVY]
  simp
