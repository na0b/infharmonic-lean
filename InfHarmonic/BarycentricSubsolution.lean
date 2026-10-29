module

public import InfHarmonic.CommonTimeSubsolution
public import InfHarmonic.BaryEnvDuality
public import InfHarmonic.BaryTestDirections
public import InfHarmonic.BaryTestSecondVariation

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A barycentric subsolution (paper Corollary 5.3): the barycentric envelope at
the running time of a subsolution of the limiting equation with subquadratic
spatial growth is again a subsolution, and so is that envelope minus any
constant multiple of the time. -/
theorem BarycentricSubsolution (f : WithLp 2 (F × ℝ) → ℝ)
    (hf : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} f)
    (hgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) f) (c : ℝ) :
    IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2}
      (fun z => BaryEnv f (ofLp z).2 z - c * (ofLp z).2) := by
  classical
  -- `BaryEnvDuality` is stated for a Borel-measurable `F`, because one of its clauses
  -- speaks about probability measures.  This node's statement carries no measurable
  -- structure, and none is needed: give `F` its Borel σ-algebra locally.  Nothing about
  -- the clauses used below depends on the choice, and the conclusion never mentions it.
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  -- the hypotheses of the duality lemma hold with the open time set `I = (0, ∞)`
  have hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.Ioi 0) :=
    hf.2.1
  obtain ⟨hattain, _, hconv, _, _⟩ :=
    BaryEnvDuality (Set.Ioi (0:ℝ)) isOpen_Ioi f hcont hgrow
  -- ===================== Step 1: the defining supremum dominates =====================
  have hdom : ∀ t : ℝ, 0 < t → ∀ (x : F) (m : ℕ) (θ' : Fin m → ℝ) (y' : Fin m → F),
      IsBaryConfig m θ' y' x →
      (∑ i, θ' i * f (toLp 2 (y' i, t))) - BaryRadius m θ' y' x ^ 2 / (2 * t)
        ≤ BaryEnv f t (toLp 2 (x, t)) := by
    intro t ht x m θ' y' hcfg
    -- the one-variable function whose convex combinations the envelope dominates
    obtain ⟨h, hh⟩ : ∃ g : F → ℝ, g = fun y => f (toLp 2 (y, t)) - ‖y - x‖ ^ 2 / (2 * t) :=
      ⟨_, rfl⟩
    -- `h` is continuous, because `f` is continuous on the slab and `t > 0`
    have hmap : Continuous (fun y : F => (toLp 2 (y, t) : WithLp 2 (F × ℝ))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hmaps : ∀ y : F, (toLp 2 (y, t) : WithLp 2 (F × ℝ))
        ∈ {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} := fun y => ht
    have hfc : ContinuousOn (fun y : F => f (toLp 2 (y, t))) Set.univ :=
      ContinuousOn.comp hcont hmap.continuousOn (fun y _ => hmaps y)
    have hhc : ContinuousOn h Set.univ := by
      rw [hh]
      exact hfc.sub (((continuous_id.sub continuous_const).norm.pow 2).div_const _).continuousOn
    -- far out, `h` is nonpositive, by subquadratic growth
    obtain ⟨M, hM0, hMb⟩ := hgrow {t} (by simpa using ht) isCompact_singleton
      (1 / (16 * t)) (by positivity)
    obtain ⟨M', hM'⟩ : ∃ r : ℝ, r = max M (2 * ‖x‖) := ⟨_, rfl⟩
    have hM'0 : 0 < M' := by rw [hM']; exact lt_max_of_lt_left hM0
    have hfar : ∀ y : F, M' ≤ ‖y‖ → h y ≤ 0 := by
      intro y hy
      have hyM : M ≤ ‖y‖ := le_trans (by rw [hM']; exact le_max_left _ _) hy
      have hx2 : 2 * ‖x‖ ≤ ‖y‖ := le_trans (by rw [hM']; exact le_max_right _ _) hy
      have hb : |f (toLp 2 (y, t))| ≤ 1 / (16 * t) * ‖y‖ ^ 2 :=
        hMb (toLp 2 (y, t)) hyM (by simp)
      have hb' : f (toLp 2 (y, t)) ≤ 1 / (16 * t) * ‖y‖ ^ 2 := (abs_le.mp hb).2
      have h16 : (0:ℝ) < 16 * t := by linarith
      have hb2 : f (toLp 2 (y, t)) * (16 * t) ≤ ‖y‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hb' h16.le
        calc f (toLp 2 (y, t)) * (16 * t)
            ≤ 1 / (16 * t) * ‖y‖ ^ 2 * (16 * t) := hmul
          _ = ‖y‖ ^ 2 := by field_simp
      have hd : ‖y‖ / 2 ≤ ‖y - x‖ := by
        have h1 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := by
          simpa using norm_sub_norm_le y x
        linarith
      have hd2 : ‖y‖ ^ 2 / 4 ≤ ‖y - x‖ ^ 2 := by
        have hy0 : (0:ℝ) ≤ ‖y‖ / 2 := by positivity
        have hmm := mul_le_mul hd hd hy0 (norm_nonneg (y - x))
        nlinarith [hmm]
      rw [hh]
      have h2t : (0:ℝ) < 2 * t := by linarith
      rw [sub_nonpos, le_div_iff₀ h2t]
      linarith [hb2, hd2, sq_nonneg ‖y‖]
    -- near the origin, `h` is bounded above by compactness
    obtain ⟨y₁, hy₁mem, hy₁max⟩ := (isCompact_closedBall (0:F) M').exists_isMaxOn
      ⟨0, by simpa using hM'0.le⟩ (hhc.mono (Set.subset_univ _))
    obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = max 0 (h y₁) := ⟨_, rfl⟩
    have hC : ∀ y : F, h y ≤ C := by
      intro y
      rcases le_or_gt M' ‖y‖ with hy | hy
      · exact le_trans (hfar y hy) (by rw [hCd]; exact le_max_left _ _)
      · have hmem : y ∈ Metric.closedBall (0:F) M' := by
          simpa using hy.le
        exact le_trans (hy₁max hmem) (by rw [hCd]; exact le_max_right _ _)
    -- every configuration value is a convex combination of values of `h`
    have hconv : ∀ (m' : ℕ) (θ'' : Fin m' → ℝ) (y'' : Fin m' → F),
        IsBaryConfig m' θ'' y'' x →
        (∑ i, θ'' i * f (toLp 2 (y'' i, t))) - BaryRadius m' θ'' y'' x ^ 2 / (2 * t) ≤ C := by
      intro m' θ'' y'' hc
      obtain ⟨hpos, hsum1, _⟩ := hc
      have hrad : BaryRadius m' θ'' y'' x ^ 2 = ∑ i, θ'' i * ‖y'' i - x‖ ^ 2 := by
        rw [BaryRadius, Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (hpos i).le (by positivity)
      rw [hrad]
      have hsplit : (∑ i, θ'' i * f (toLp 2 (y'' i, t)))
          - (∑ i, θ'' i * ‖y'' i - x‖ ^ 2) / (2 * t) = ∑ i, θ'' i * h (y'' i) := by
        rw [hh, Finset.sum_div, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
      rw [hsplit]
      calc ∑ i, θ'' i * h (y'' i) ≤ ∑ i : Fin m', θ'' i * C :=
            Finset.sum_le_sum fun i _ =>
              mul_le_mul_of_nonneg_left (hC (y'' i)) (hpos i).le
        _ = C := by rw [← Finset.sum_mul, hsum1, one_mul]
    -- so the defining set is bounded above and contains our number
    refine le_csSup ⟨C, ?_⟩ ⟨m, θ', y', hcfg, rfl⟩
    rintro w ⟨m', θ'', y'', hc, rfl⟩
    exact hconv m' θ'' y'' hc
  refine ⟨hf.1, ?_, ?_⟩
  · -- ===================== Step 2: continuity of `V` on `Ω` =====================
    intro z₀ hz₀
    refine ContinuousAt.continuousWithinAt ?_
    have hz₀' : (ofLp z₀).2 ∈ Set.Ioi (0:ℝ) := hz₀
    have h1 : ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => BaryEnv f p.1 p.2)
        ((ofLp z₀).2, z₀) := hconv _ hz₀ z₀ hz₀'
    have h2 : Continuous (fun z : WithLp 2 (F × ℝ) => ((ofLp z).2, z)) :=
      ((continuous_snd.comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous).prodMk continuous_id)
    have h3 : ContinuousAt (fun z : WithLp 2 (F × ℝ) => BaryEnv f (ofLp z).2 z) z₀ := by
      have h := Filter.Tendsto.comp h1 (h2.continuousAt (x := z₀))
      exact h
    have h4 : ContinuousAt (fun z : WithLp 2 (F × ℝ) => c * (ofLp z).2) z₀ := by
      refine continuousAt_const.mul ?_
      exact (continuous_snd.comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous).continuousAt
    exact h3.sub h4
  · -- ===================== Step 3: the viscosity inequality =====================
    intro z₀ hz₀ φ hφ hmax
    obtain ⟨x₀, t₀, hx₀, ht₀d⟩ :
        ∃ x t, x = (ofLp z₀).1 ∧ t = (ofLp z₀).2 := ⟨_, _, rfl, rfl⟩
    have ht₀ : 0 < t₀ := by rw [ht₀d]; exact hz₀
    have hz₀eq : z₀ = toLp 2 (x₀, t₀) := by rw [hx₀, ht₀d]
    -- (3a) an attaining configuration, with its weights now held fixed
    obtain ⟨n, θ, y₀, hcfg, hattaineq⟩ := hattain t₀ z₀ ht₀ hz₀
    obtain ⟨hθ, hθ1, hmean⟩ := hcfg
    have hn : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; simp at hθ1
      · exact h
    have hmean' : ∑ i, θ i • y₀ i = x₀ := by rw [hx₀]; exact hmean
    -- (3b) the test function on the product
    obtain ⟨Φ, hΦ⟩ : ∃ G : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) → ℝ,
        ∀ W, G W = φ (toLp 2 (∑ j, θ j • ofLp (ofLp W).1 j, (ofLp W).2))
          + c * (ofLp W).2
          + (∑ j, θ j * ‖ofLp (ofLp W).1 j - ∑ k, θ k • ofLp (ofLp W).1 k‖ ^ 2)
              / (2 * (ofLp W).2) := ⟨_, fun W => rfl⟩
    have hφ' : ContDiffAt ℝ 2 φ (toLp 2 (x₀, t₀)) := by rw [← hz₀eq]; exact hφ
    -- (3b), (3f) and (3g) in one citation: the lift is an admissible test, and its
    -- second variation in the common-time direction is the operator applied to `φ`
    obtain ⟨hΦC2, hvar⟩ :=
      BaryTestSecondVariation n θ hθ1 y₀ x₀ hmean' t₀ ht₀ c φ hφ' Φ hΦ
    -- (3c) is the one remaining support obligation; the .tex proof carries it in full,
    -- resting on the domination of Step 1.
    have hlocmax : IsLocalMaxOn
        (fun W : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) =>
          (∑ i, θ i * f (toLp 2 (ofLp (ofLp W).1 i, (ofLp W).2))) - Φ W)
        {W : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) | (ofLp W).2 ∈ Set.Ioi (0:ℝ)}
        (toLp 2 (toLp 2 y₀, t₀)) := by
      -- the lift `(Y,t) ↦ (X(Y),t)`, as a continuous linear map
      obtain ⟨L, hL⟩ : ∃ L : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ]
            WithLp 2 (F × ℝ),
          ∀ W, L W = toLp 2 (∑ j, θ j • ofLp (ofLp W).1 j, (ofLp W).2) := by
        obtain ⟨P, hP⟩ : ∃ P : Fin n → (PiLp 2 (fun _ : Fin n => F) →L[ℝ] F),
            ∀ j Y, P j Y = ofLp Y j :=
          ⟨fun j => (ContinuousLinearMap.proj j).comp
            (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => F)).toContinuousLinearMap,
           fun j Y => rfl⟩
        obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ]
              PiLp 2 (fun _ : Fin n => F), ∀ W, π₁ W = (ofLp W).1 :=
          ⟨(ContinuousLinearMap.fst ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ).comp
            (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ
              ).toContinuousLinearMap, fun W => rfl⟩
        obtain ⟨π₂, hπ₂⟩ : ∃ π₂ : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ) →L[ℝ] ℝ,
            ∀ W, π₂ W = (ofLp W).2 :=
          ⟨(ContinuousLinearMap.snd ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ).comp
            (WithLp.prodContinuousLinearEquiv 2 ℝ (PiLp 2 (fun _ : Fin n => F)) ℝ
              ).toContinuousLinearMap, fun W => rfl⟩
        obtain ⟨X, hX⟩ : ∃ X : PiLp 2 (fun _ : Fin n => F) →L[ℝ] F,
            ∀ Y, X Y = ∑ j, θ j • ofLp Y j := by
          refine ⟨∑ j, θ j • P j, fun Y => ?_⟩
          rw [sum_apply]
          exact Finset.sum_congr rfl fun j _ => by rw [smul_apply, hP]
        refine ⟨(WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.toContinuousLinearMap.comp
          ((X.comp π₁).prod π₂), fun W => ?_⟩
        show toLp 2 (X (π₁ W), π₂ W) = _
        rw [hπ₁, hπ₂, hX]
      have hLW₀ : L (toLp 2 (toLp 2 y₀, t₀)) = z₀ := by
        rw [hL, hz₀eq]
        congr 1
        refine Prod.ext ?_ rfl
        show (∑ j, θ j • y₀ j) = x₀
        exact hmean'
      -- the hypothesised local maximum of `V - φ`, as a ball around `z₀`
      have hΩopen : IsOpen {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} := hf.1
      rw [IsLocalMaxOn, IsMaxFilter, hΩopen.nhdsWithin_eq hz₀] at hmax
      obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp hmax
      -- at the base point the domination is an equality, by the attaining configuration
      have hrad0 : BaryRadius n θ y₀ x₀ ^ 2 = ∑ j, θ j * ‖y₀ j - x₀‖ ^ 2 := by
        rw [BaryRadius, Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ i).le (by positivity)
      have hGW₀ : (∑ i, θ i * f (toLp 2 (y₀ i, t₀))) - Φ (toLp 2 (toLp 2 y₀, t₀))
          = BaryEnv f (ofLp z₀).2 z₀ - c * (ofLp z₀).2 - φ z₀ := by
        have hΦ0 : Φ (toLp 2 (toLp 2 y₀, t₀))
            = φ z₀ + c * t₀ + (∑ j, θ j * ‖y₀ j - x₀‖ ^ 2) / (2 * t₀) := by
          rw [hΦ]
          show φ (toLp 2 ((∑ j, θ j • y₀ j : F), t₀)) + c * t₀
              + (∑ j, θ j * ‖y₀ j - ∑ k, θ k • y₀ k‖ ^ 2) / (2 * t₀) = _
          rw [hmean', hz₀eq]
        have hatt : BaryEnv f t₀ z₀
            = (∑ i, θ i * f (toLp 2 (y₀ i, t₀))) - (∑ j, θ j * ‖y₀ j - x₀‖ ^ 2) / (2 * t₀) := by
          rw [hattaineq, ← ht₀d, ← hx₀, hrad0]
        rw [hΦ0, ← ht₀d, hatt]
        ring
      -- the neighbourhood on which the domination can be fed into `hball`
      have hpre : L ⁻¹' (Metric.ball z₀ ρ) ∈ nhds
          (toLp 2 (toLp 2 y₀, t₀) : WithLp 2 (PiLp 2 (fun _ : Fin n => F) × ℝ)) := by
        refine (Metric.isOpen_ball.preimage L.continuous).mem_nhds ?_
        simp only [Set.mem_preimage, hLW₀, Metric.mem_ball, dist_self]
        exact hρ
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hpre] with W hWΩ hWb
      have htW : 0 < (ofLp W).2 := hWΩ
      -- Step 1 at the point `(X(Y), t)`
      have hd := hdom (ofLp W).2 htW (∑ j, θ j • ofLp (ofLp W).1 j) n θ
        (fun i => ofLp (ofLp W).1 i) ⟨hθ, hθ1, rfl⟩
      have hradW : BaryRadius n θ (fun i => ofLp (ofLp W).1 i)
            (∑ j, θ j • ofLp (ofLp W).1 j) ^ 2
          = ∑ i, θ i * ‖ofLp (ofLp W).1 i - ∑ k, θ k • ofLp (ofLp W).1 k‖ ^ 2 := by
        rw [BaryRadius, Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => mul_nonneg (hθ i).le (by positivity)
      rw [hradW, ← hL W] at hd
      -- and the hypothesised maximum at the image point
      have hVb := hball (Metric.mem_ball.mp hWb)
      have hΦW : Φ W = φ (L W) + c * (ofLp W).2
          + (∑ i, θ i * ‖ofLp (ofLp W).1 i - ∑ k, θ k • ofLp (ofLp W).1 k‖ ^ 2)
              / (2 * (ofLp W).2) := by
        rw [hΦ, hL]
      have hLWt : (ofLp (L W)).2 = (ofLp W).2 := by rw [hL]
      simp only [hLWt] at hVb
      show (∑ i, θ i * f (toLp 2 (ofLp (ofLp W).1 i, (ofLp W).2))) - Φ W
        ≤ (∑ i, θ i * f (toLp 2 (y₀ i, t₀))) - Φ (toLp 2 (toLp 2 y₀, t₀))
      rw [hΦW, hGW₀]
      linarith [hd, hVb]
    -- (3d) the common-time rule
    have hfI : IsLimitSubOn {z : WithLp 2 (F × ℝ) | (ofLp z).2 ∈ Set.Ioi (0:ℝ)} f := hf
    have hsr := CommonTimeSubsolution n hn (Set.Ioi (0:ℝ)) f hfI θ hθ hθ1 Φ
      (toLp 2 y₀) t₀ ht₀ hΦC2 hlocmax
    -- (3e) the direction the sum rule produced is the one the computation describes
    have hdir := BaryTestDirections n θ hθ hθ1 y₀ x₀ hmean' t₀ ht₀ c φ hφ' Φ hΦ
    have hdirfun : (fun i => (θ i)⁻¹ • ofLp (ofLp (gradient Φ (toLp 2 (toLp 2 y₀, t₀)))).1 i)
        = fun i => (ofLp (gradient φ (toLp 2 (x₀, t₀)))).1 + (t₀)⁻¹ • (y₀ i - x₀) := funext hdir
    rw [hdirfun, hvar] at hsr
    rw [hz₀eq]
    exact hsr
