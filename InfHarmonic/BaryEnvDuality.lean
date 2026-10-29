module

public import InfHarmonic.BaryEnvWeakDuality
public import InfHarmonic.BaryEnvSlopeLocalization
public import InfHarmonic.BaryGammaMinAttained
public import InfHarmonic.BaryEnvHullOfMinSlope
public import InfHarmonic.BaryConfigOfConvexHull
public import InfHarmonic.BaryGammaAffineInCenter
public import InfHarmonic.BaryAffineMajorantIntegral
public import InfHarmonic.BaryEnv
public import InfHarmonic.SubquadraticGrowth
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section
open Metric Set Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable [MeasurableSpace F] [BorelSpace F]

/-- Lemma 5.2: the barycentric envelope is attained by a finite configuration,
is given by the min-max duality formula (5.3), is continuous, is semiconcave in
the center, and is not increased by probability measures of finite second
moment. -/
theorem BaryEnvDuality (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f) :
    (∀ (s : ℝ) (z : WithLp 2 (F × ℝ)), 0 < s → (ofLp z).2 ∈ I →
        ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
          IsBaryConfig n θ y (ofLp z).1 ∧
          BaryEnv f s z = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)) ∧
    (∀ (s : ℝ) (z : WithLp 2 (F × ℝ)), 0 < s → (ofLp z).2 ∈ I →
        ∃ A₀ : F,
          (BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s)
            = sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
                - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - (ofLp z).1)}) ∧
          ∀ A : F, BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s)
            ≤ sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
                - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)}) ∧
    (∀ s : ℝ, 0 < s → ∀ z₀ : WithLp 2 (F × ℝ), (ofLp z₀).2 ∈ I →
        ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => BaryEnv f p.1 p.2) (s, z₀)) ∧
    (∀ (s t : ℝ), 0 < s → t ∈ I →
        ConcaveOn ℝ (Set.univ : Set F)
          (fun x : F => BaryEnv f s (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * s))) ∧
    (∀ (s : ℝ) (z : WithLp 2 (F × ℝ)), 0 < s → (ofLp z).2 ∈ I →
        ∀ μ : Measure F, IsProbabilityMeasure μ →
          Integrable (fun y : F => ‖y - (ofLp z).1‖ ^ 2) μ →
          Integrable (fun y : F => f (toLp 2 (y, (ofLp z).2))) μ →
          Integrable (fun y : F => y - (ofLp z).1) μ →
          (∫ y, (y - (ofLp z).1) ∂μ) = 0 →
            (∫ y, f (toLp 2 (y, (ofLp z).2)) ∂μ)
              - (∫ y, ‖y - (ofLp z).1‖ ^ 2 ∂μ) / (2 * s) ≤ BaryEnv f s z) := by
  -- A time slice of `f` is continuous on any spatial set whose time level lies in `I`.
  have hslice : ∀ t : ℝ, t ∈ I → ∀ T : Set F,
      ContinuousOn (fun y : F => f (toLp 2 (y, t))) T := by
    intro t ht T
    have hmap : Continuous (fun y : F => (toLp 2 (y, t) : WithLp 2 (F × ℝ))) := by fun_prop
    exact hcont.comp hmap.continuousOn (fun y _ => ht)
  -- STEPS 2, 3 and 4 at a single admissible triple: a minimizing slope `A₀`, the
  -- configuration supported in its maximizer set, strong duality, weak duality
  -- against every slope, and the finiteness that licenses every supremum used.
  have core : ∀ (s : ℝ) (z : WithLp 2 (F × ℝ)), 0 < s → (ofLp z).2 ∈ I →
      ∃ A₀ : F,
        (∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
            IsBaryConfig n θ y (ofLp z).1 ∧
            BaryEnv f s z = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
              - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)) ∧
        (BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s)
          = sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
              - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - (ofLp z).1)}) ∧
        (∀ A : F, BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s)
          ≤ sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
              - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)}) ∧
        (∀ A : F, BddAbove {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
              - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)}) := by
    intro s z hs ht
    obtain ⟨S, hSdef⟩ : ∃ S : Set (F × ℝ × ℝ),
        S = {((ofLp z).1, (ofLp z).2, s)} := ⟨_, rfl⟩
    have hSc : IsCompact S := by rw [hSdef]; exact isCompact_singleton
    have hpS : ((ofLp z).1, (ofLp z).2, s) ∈ S := by rw [hSdef]; rfl
    have hSne : S.Nonempty := ⟨_, hpS⟩
    have hSadm : ∀ p ∈ S, 0 < p.2.2 ∧ p.2.1 ∈ I := by
      intro p hp
      rw [hSdef, Set.mem_singleton_iff] at hp
      subst hp
      exact ⟨hs, ht⟩
    obtain ⟨Λ₀, M, hΛ₀, hM, hsup, hslope, hball⟩ :=
      BaryEnvSlopeLocalization I f hcont hgrow S hSc hSne hSadm
    obtain ⟨hΓcont, G, hGcont, hGspec⟩ :=
      BaryGammaMinAttained I f hcont S hSc hSne hSadm Λ₀ M hΛ₀ hM hsup hslope
        (fun p hp A hA => (hball p hp A hA).1)
    obtain ⟨hGle, A₀, hA₀, hGeq⟩ := hGspec _ hpS
    -- `A₀` minimizes the slope functional over all of `F`
    have hmin : ∀ A : F,
        sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
            - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - (ofLp z).1)}
          ≤ sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
            - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)} := by
      intro A
      rw [← hGeq]
      exact hGle A
    -- the slope functional is continuous in the slope on the ball of radius `Λ₀ + 1`
    have hΓA : ContinuousOn (fun A : F =>
        sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
          - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)})
        (closedBall (0 : F) (Λ₀ + 1)) := by
      have hmap : Continuous (fun A : F => (A, ((ofLp z).1, (ofLp z).2, s))) := by fun_prop
      exact hΓcont.comp hmap.continuousOn (fun A hA => ⟨hA, hpS⟩)
    -- Step 4: the center lies in the convex hull of the maximizer set, hence is the
    -- mean of a finite configuration supported there
    obtain ⟨n, θ, y, hcfg, hyE⟩ :=
      (BaryConfigOfConvexHull _).1 _
        (BaryEnvHullOfMinSlope f s (ofLp z).2 hs (ofLp z).1 (fun A => hsup _ hpS A)
          Λ₀ M hΛ₀ hM A₀ hA₀ hmin
          (fun A hA => (hball _ hpS A hA).2.1) (fun A hA => (hball _ hpS A hA).2.2)
          hΓA (hslice _ ht _))
    obtain ⟨hid, hdom, hweak⟩ := BaryEnvWeakDuality f s hs z (fun A => hsup _ hpS A)
    -- every configuration point is a maximizer at `A₀`, so the `g`-average is `Γ(A₀;x)`
    have hθ1 : ∑ i, θ i = 1 := hcfg.2.1
    have hmean : ∑ i, θ i • y i = (ofLp z).1 := hcfg.2.2
    have hzero : ∑ i, θ i • (y i - (ofLp z).1) = (0 : F) := by
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hmean, hθ1, one_smul, sub_self]
    have hsum : ∑ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s))
        = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2))
            - ‖y'‖ ^ 2 / (2 * s) - inner ℝ A₀ (y' - (ofLp z).1)} := by
      have hterm : ∀ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s))
          = θ i * sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2))
                - ‖y'‖ ^ 2 / (2 * s) - inner ℝ A₀ (y' - (ofLp z).1)}
            + θ i * (inner ℝ A₀ (y i - (ofLp z).1) : ℝ) := by
        intro i
        have h := (hyE i).2
        have : f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s)
            = sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2))
                - ‖y'‖ ^ 2 / (2 * s) - inner ℝ A₀ (y' - (ofLp z).1)}
              + (inner ℝ A₀ (y i - (ofLp z).1) : ℝ) := by linarith [h]
        rw [this]; ring
      have hlin : ∑ i, θ i * (inner ℝ A₀ (y i - (ofLp z).1) : ℝ)
          = (inner ℝ A₀ (∑ i, θ i • (y i - (ofLp z).1)) : ℝ) := by
        rw [inner_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [real_inner_smul_right]
      rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
        ← Finset.sum_mul, hθ1, one_mul, hlin, hzero, inner_zero_right, add_zero]
    have hidc := hid n θ y hcfg
    have hdomc := hdom n θ y hcfg
    refine ⟨A₀, ⟨n, θ, y, hcfg, by linarith [hweak A₀]⟩, ?_, hweak, fun A => hsup _ hpS A⟩
    linarith [hweak A₀]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- (1) finite attainment
    intro s z hs ht
    obtain ⟨A₀, hconf, -, -, -⟩ := core s z hs ht
    exact hconf
  · -- (2) min-max duality with the minimum attained
    intro s z hs ht
    obtain ⟨A₀, -, heq, hweak, -⟩ := core s z hs ht
    exact ⟨A₀, heq, hweak⟩
  · -- (3) continuity: Step 5, the compact box of triples
    intro s hs z₀ ht₀
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hI _ ht₀
    obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = min (ε / 2) (s / 2) := ⟨_, rfl⟩
    have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min (by linarith) (by linarith)
    have hρε : 2 * ρ ≤ ε := by
      have h := min_le_left (ε / 2) (s / 2); rw [hρdef]; linarith
    have hρs : 2 * ρ ≤ s := by
      have h := min_le_right (ε / 2) (s / 2); rw [hρdef]; linarith
    obtain ⟨S, hSdef⟩ : ∃ S : Set (F × ℝ × ℝ),
        S = closedBall (ofLp z₀).1 ρ ×ˢ
          (Icc ((ofLp z₀).2 - ρ) ((ofLp z₀).2 + ρ) ×ˢ Icc (s - ρ) (s + ρ)) := ⟨_, rfl⟩
    have hSc : IsCompact S := by
      rw [hSdef]
      exact (isCompact_closedBall _ _).prod (isCompact_Icc.prod isCompact_Icc)
    have hpS : ((ofLp z₀).1, (ofLp z₀).2, s) ∈ S := by
      rw [hSdef]
      exact ⟨Metric.mem_closedBall_self hρ0.le,
        ⟨by constructor <;> linarith, by constructor <;> linarith⟩⟩
    have hSne : S.Nonempty := ⟨_, hpS⟩
    have hSadm : ∀ p ∈ S, 0 < p.2.2 ∧ p.2.1 ∈ I := by
      intro p hp
      rw [hSdef] at hp
      obtain ⟨-, ht1, hs1⟩ := hp
      refine ⟨by simp only [Set.mem_Icc] at hs1; linarith [hs1.1], ?_⟩
      simp only [Set.mem_Icc] at ht1
      refine hεsub ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht1.1], by linarith [ht1.2]⟩
    obtain ⟨Λ₀, M, hΛ₀, hM, hsup, hslope, hball⟩ :=
      BaryEnvSlopeLocalization I f hcont hgrow S hSc hSne hSadm
    obtain ⟨-, G, hGcont, hGspec⟩ :=
      BaryGammaMinAttained I f hcont S hSc hSne hSadm Λ₀ M hΛ₀ hM hsup hslope
        (fun p hp A hA => (hball p hp A hA).1)
    -- on the box the envelope is `G` plus the explicit quadratic
    have hagree : ∀ p ∈ S, BaryEnv f p.2.2 (toLp 2 (p.1, p.2.1))
        = G p + ‖p.1‖ ^ 2 / (2 * p.2.2) := by
      intro p hp
      obtain ⟨hps, hpt⟩ := hSadm p hp
      obtain ⟨A₁, -, heq, hweak, -⟩ := core p.2.2 (toLp 2 (p.1, p.2.1)) hps hpt
      obtain ⟨hGle, A₂, -, hGeq⟩ := hGspec p hp
      have h1 : BaryEnv f p.2.2 (toLp 2 (p.1, p.2.1)) - ‖p.1‖ ^ 2 / (2 * p.2.2) ≤ G p := by
        rw [hGeq]; exact hweak A₂
      have h2 : G p ≤ BaryEnv f p.2.2 (toLp 2 (p.1, p.2.1)) - ‖p.1‖ ^ 2 / (2 * p.2.2) := by
        rw [heq]; exact hGle A₁
      linarith
    -- transfer to the `(s, z)` coordinates through the open box
    obtain ⟨U, hUdef⟩ : ∃ U : Set (ℝ × WithLp 2 (F × ℝ)),
        U = {q : ℝ × WithLp 2 (F × ℝ) | ‖(ofLp q.2).1 - (ofLp z₀).1‖ < ρ} ∩
            ({q : ℝ × WithLp 2 (F × ℝ) | |(ofLp q.2).2 - (ofLp z₀).2| < ρ} ∩
              {q : ℝ × WithLp 2 (F × ℝ) | |q.1 - s| < ρ}) := ⟨_, rfl⟩
    have hUopen : IsOpen U := by
      rw [hUdef]
      exact (isOpen_lt (by fun_prop) continuous_const).inter
        ((isOpen_lt (by fun_prop) continuous_const).inter
          (isOpen_lt (by fun_prop) continuous_const))
    have hUmem : (s, z₀) ∈ U := by
      rw [hUdef]; refine ⟨?_, ?_, ?_⟩ <;> simp [hρ0]
    have hUS : ∀ q ∈ U, ((ofLp q.2).1, (ofLp q.2).2, q.1) ∈ S := by
      intro q hq
      rw [hUdef] at hq
      obtain ⟨h1, h2, h3⟩ := hq
      simp only [Set.mem_ofPred_eq] at h1 h2 h3
      rw [hSdef]
      refine ⟨?_, ⟨?_, ?_⟩⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]; exact h1.le
      · rw [Set.mem_Icc]
        have := abs_lt.mp h2
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
      · rw [Set.mem_Icc]
        have := abs_lt.mp h3
        exact ⟨by linarith [this.1], by linarith [this.2]⟩
    have hΨ : Continuous (fun q : ℝ × WithLp 2 (F × ℝ) =>
        ((ofLp q.2).1, (ofLp q.2).2, q.1)) := by fun_prop
    have hcts : ContinuousOn (fun q : ℝ × WithLp 2 (F × ℝ) => BaryEnv f q.1 q.2) U := by
      have hGU : ContinuousOn (fun q : ℝ × WithLp 2 (F × ℝ) =>
          G ((ofLp q.2).1, (ofLp q.2).2, q.1)) U :=
        hGcont.comp hΨ.continuousOn hUS
      have hquad : ContinuousOn (fun q : ℝ × WithLp 2 (F × ℝ) =>
          ‖(ofLp q.2).1‖ ^ 2 / (2 * q.1)) U := by
        refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
        intro q hq
        rw [hUdef] at hq
        have h3 : |q.1 - s| < ρ := hq.2.2
        have h4 := abs_lt.mp h3
        have h5 : 0 < q.1 := by linarith [h4.1]
        positivity
      refine (hGU.add hquad).congr ?_
      intro q hq
      exact hagree _ (hUS q hq)
    exact hcts.continuousAt (hUopen.mem_nhds hUmem)
  · -- (4) concavity: Step 6
    intro s t hs ht
    obtain ⟨A₀', -, -, -, hbdd'⟩ := core s (toLp 2 ((0 : F), t)) hs ht
    have hbdd0 : ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, t)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A y} := by
      intro A
      have h := hbdd' A
      simpa only [sub_zero] using h
    obtain ⟨c, hc⟩ := BaryGammaAffineInCenter f s t hs hbdd0
    refine ⟨convex_univ, ?_⟩
    intro x₀ _ x₁ _ a b ha hb hab
    obtain ⟨A₀, -, heqτ, -, -⟩ := core s (toLp 2 (a • x₀ + b • x₁, t)) hs ht
    obtain ⟨-, -, -, hw₀, -⟩ := core s (toLp 2 (x₀, t)) hs ht
    obtain ⟨-, -, -, hw₁, -⟩ := core s (toLp 2 (x₁, t)) hs ht
    have h₀ : BaryEnv f s (toLp 2 (x₀, t)) - ‖x₀‖ ^ 2 / (2 * s) ≤ c A₀ + inner ℝ A₀ x₀ := by
      rw [← hc A₀ x₀]; exact hw₀ A₀
    have h₁ : BaryEnv f s (toLp 2 (x₁, t)) - ‖x₁‖ ^ 2 / (2 * s) ≤ c A₀ + inner ℝ A₀ x₁ := by
      rw [← hc A₀ x₁]; exact hw₁ A₀
    have hτ : BaryEnv f s (toLp 2 (a • x₀ + b • x₁, t))
        - ‖a • x₀ + b • x₁‖ ^ 2 / (2 * s)
        = c A₀ + inner ℝ A₀ (a • x₀ + b • x₁) := by
      rw [heqτ]; exact hc A₀ (a • x₀ + b • x₁)
    have hinner : (inner ℝ A₀ (a • x₀ + b • x₁) : ℝ)
        = a * (inner ℝ A₀ x₀ : ℝ) + b * (inner ℝ A₀ x₁ : ℝ) := by
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hp₀ := mul_le_mul_of_nonneg_left h₀ ha
    have hp₁ := mul_le_mul_of_nonneg_left h₁ hb
    have hcab : a * c A₀ + b * c A₀ = c A₀ := by rw [← add_mul, hab, one_mul]
    simp only [smul_eq_mul]
    rw [hτ, hinner]
    linarith [hp₀, hp₁, hcab]
  · -- (5) probability measures: Step 7
    intro s z hs ht μ hμ hsq hf hlin hmean
    obtain ⟨A₀, -, heq, -, hbdd⟩ := core s z hs ht
    have hmaj : ∀ y : F, f (toLp 2 (y, (ofLp z).2)) - ‖y‖ ^ 2 / (2 * s)
        ≤ (BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s))
          + inner ℝ A₀ (y - (ofLp z).1) := by
      intro y
      have hmem : f (toLp 2 (y, (ofLp z).2)) - ‖y‖ ^ 2 / (2 * s)
          - inner ℝ A₀ (y - (ofLp z).1)
          ∈ {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2))
              - ‖y'‖ ^ 2 / (2 * s) - inner ℝ A₀ (y' - (ofLp z).1)} := ⟨y, rfl⟩
      have h := le_csSup (hbdd A₀) hmem
      rw [← heq] at h
      linarith
    have h := BaryAffineMajorantIntegral f s (ofLp z).2 hs (ofLp z).1
      (BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s)) A₀ hmaj μ hμ hsq hf hlin hmean
    linarith
