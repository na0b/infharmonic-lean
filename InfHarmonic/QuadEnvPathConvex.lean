import InfHarmonic.QuadEnvAttained
import InfHarmonic.IsLimitSolutionOn
import InfHarmonic.TimeReversal
import InfHarmonic.ViscosityConvexOnIcc
import InfHarmonic.EnvelopeCompetitorBounds
import InfHarmonic.SecondVariationAlongLine
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.6), path convexity: for a subsolution, the forward envelope
along an affine path, corrected by `|d|² ℓ log ℓ`, is convex in the length; for
a supersolution the backward envelope is concave in the length. -/
theorem QuadEnvPathConvex (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f) (T : ℝ) (hT : 0 < T) :
    (IsLimitSubOn ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) f →
      ∀ (x₀ d : F) (t : ℝ), (∀ l ∈ Set.Icc (0 : ℝ) T, t + l ∈ I) →
        ConvexOn ℝ (Set.Icc (0 : ℝ) T)
          (fun l : ℝ => QuadEnvP f l (toLp 2 (x₀ + l • d, t))
                          + ‖d‖ ^ 2 * (l * Real.log l))) ∧
    (IsLimitSuperOn ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) f →
      ∀ (x : F) (t : ℝ), (∀ l ∈ Set.Icc (0 : ℝ) T, t - l ∈ I) →
        ConcaveOn ℝ (Set.Icc (0 : ℝ) T)
          (fun l : ℝ => QuadEnvM f l (toLp 2 (x, t)))) := by
  classical
  -- Part (1) is established here in GENERALIZED form, over an arbitrary time set and
  -- function, because Part (2) applies it to the time-reversed function on the reflected
  -- time set -- a different `I` and `f` than this theorem's own arguments.  The .tex's
  -- "apply Part (1) to the time reversal" therefore cannot be a citation of the first
  -- conjunct in Lean; the statement has to be proved once, generally, and used twice.
  have part1 : ∀ J : Set ℝ, IsOpen J → ∀ u : WithLp 2 (F × ℝ) → ℝ,
      ContinuousOn u ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' J) →
      SubquadraticGrowth J u →
      IsLimitSubOn ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' J) u →
      ∀ (x₀ d : F) (t : ℝ), (∀ l ∈ Set.Icc (0 : ℝ) T, t + l ∈ J) →
        ConvexOn ℝ (Set.Icc (0 : ℝ) T)
          (fun l : ℝ => QuadEnvP u l (toLp 2 (x₀ + l • d, t))
                          + ‖d‖ ^ 2 * (l * Real.log l)) := by
    intro J hJ u hucont hugrow husub x₀ d t hadm
    obtain ⟨hatt, -, hcontP, -, hcoll, -⟩ := QuadEnvAttained J hJ u hucont hugrow
    have ht0 : t ∈ J := by
      have h := hadm 0 ⟨le_refl 0, hT.le⟩
      rwa [add_zero] at h
    have hOopen : IsOpen ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' J) :=
      hJ.preimage (continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous)
    -- the affine path, as a continuous map into space-time
    have hpath : Continuous (fun σ : ℝ => (toLp 2 (x₀ + σ • d, t) : WithLp 2 (F × ℝ))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.continuous.comp
        ((continuous_const.add (continuous_id.smul continuous_const)).prodMk continuous_const)
    have hp0 : (toLp 2 (x₀ + (0:ℝ) • d, t) : WithLp 2 (F × ℝ)) = toLp 2 (x₀, t) := by
      rw [zero_smul, add_zero]
    obtain ⟨G, hGd⟩ : ∃ g : ℝ → ℝ, g = fun l : ℝ =>
        QuadEnvP u l (toLp 2 (x₀ + l • d, t)) + ‖d‖ ^ 2 * (l * Real.log l) := ⟨_, rfl⟩
    -- Step 1 of the .tex: `G` is continuous on `[0, T]`.
    have hGc : ContinuousOn G (Set.Icc (0:ℝ) T) := by
      -- the correction `l ↦ |d|² l log l` is continuous everywhere, `0 · log 0 = 0`
      -- being its continuous value, so only the envelope factor needs an argument
      have hgc : ContinuousOn (fun σ : ℝ => QuadEnvP u σ (toLp 2 (x₀ + σ • d, t)))
          (Set.Icc (0:ℝ) T) := by
        intro l hl
        rcases eq_or_lt_of_le hl.1 with hl0 | hl0
        · -- the left endpoint: the envelope collapses to `u` uniformly on the compact
          -- path, and `u` is continuous at the base point
          subst hl0
          have hf0 : QuadEnvP u 0 (toLp 2 (x₀ + (0:ℝ) • d, t)) = u (toLp 2 (x₀, t)) := by
            rw [hp0, QuadEnvP, if_pos rfl]
          rw [ContinuousWithinAt, hf0, Metric.tendsto_nhdsWithin_nhds]
          intro ε hε
          obtain ⟨δ₁, hδ₁, hcol⟩ := hcoll
            ((fun σ : ℝ => (toLp 2 (x₀ + σ • d, t) : WithLp 2 (F × ℝ))) '' Set.Icc (0:ℝ) T)
            (isCompact_Icc.image hpath) (by rintro z ⟨σ, -, rfl⟩; exact ht0) (ε / 3)
            (by positivity)
          have hucA : ContinuousAt u (toLp 2 (x₀, t)) :=
            hucont.continuousAt (hOopen.mem_nhds ht0)
          have hcomp : ContinuousAt (fun σ : ℝ => u (toLp 2 (x₀ + σ • d, t))) 0 :=
            ContinuousAt.comp (by rw [hp0]; exact hucA) hpath.continuousAt
          obtain ⟨δ₂, hδ₂, hu3⟩ := Metric.continuousAt_iff.mp hcomp (ε / 3) (by positivity)
          refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
          intro σ hσ hdist
          rcases eq_or_lt_of_le hσ.1 with hσ0 | hσ0
          · rw [← hσ0, hf0, dist_self]
            exact hε
          · have hzK : (toLp 2 (x₀ + σ • d, t) : WithLp 2 (F × ℝ))
                ∈ (fun σ : ℝ => (toLp 2 (x₀ + σ • d, t) : WithLp 2 (F × ℝ))) ''
                    Set.Icc (0:ℝ) T := ⟨σ, hσ, rfl⟩
            have habs : |σ| < min δ₁ δ₂ := by
              rw [Real.dist_eq, sub_zero] at hdist
              exact hdist
            have hσδ₁ : σ < δ₁ :=
              lt_of_lt_of_le (by rwa [abs_of_pos hσ0] at habs) (min_le_left _ _)
            have e1 := (hcol σ hσ0 hσδ₁ _ hzK).1
            have e2 : |u (toLp 2 (x₀ + σ • d, t)) - u (toLp 2 (x₀, t))| < ε / 3 := by
              have h := hu3 (lt_of_lt_of_le hdist (min_le_right _ _))
              rw [hp0, Real.dist_eq] at h
              exact h
            rw [Real.dist_eq]
            calc |QuadEnvP u σ (toLp 2 (x₀ + σ • d, t)) - u (toLp 2 (x₀, t))|
                ≤ |QuadEnvP u σ (toLp 2 (x₀ + σ • d, t)) - u (toLp 2 (x₀ + σ • d, t))|
                    + |u (toLp 2 (x₀ + σ • d, t)) - u (toLp 2 (x₀, t))| := abs_sub_le _ _ _
              _ < ε := by linarith
        · -- positive lengths: joint continuity of the envelope in length and centre
          refine ContinuousAt.continuousWithinAt ?_
          have hcA := hcontP l hl0 (toLp 2 (x₀ + l • d, t)) ht0 (hadm l hl)
          -- `ContinuousAt.comp` unifies the outer function with a `Prod.mk` section here,
          -- so the composition is taken at the level of filters instead
          have hmap : ContinuousAt
              (fun σ : ℝ => ((σ, toLp 2 (x₀ + σ • d, t)) : ℝ × WithLp 2 (F × ℝ))) l :=
            (continuous_id.prodMk hpath).continuousAt
          have hcomp := Filter.Tendsto.comp hcA hmap
          exact hcomp
      rw [hGd]
      exact hgc.add (continuous_const.mul Real.continuous_mul_log).continuousOn
    -- Step 2 of the .tex: every quadratic upper test at an interior length has
    -- nonnegative leading coefficient.
    have htest : ∀ A B C l₀ : ℝ, l₀ ∈ Set.Ioo (0:ℝ) T →
        IsLocalMaxOn (fun τ : ℝ => G τ - (A * τ ^ 2 + B * τ + C)) (Set.Icc (0:ℝ) T) l₀ →
        0 ≤ A := by
      intro A B C l₀ hl₀ hmax
      obtain ⟨hl₀0, hl₀T⟩ := hl₀
      have hl₀ne : l₀ ≠ 0 := ne_of_gt hl₀0
      have htl₀ : t + l₀ ∈ J := hadm l₀ ⟨hl₀0.le, hl₀T.le⟩
      have hGv : ∀ τ : ℝ, G τ = QuadEnvP u τ (toLp 2 (x₀ + τ • d, t))
          + ‖d‖ ^ 2 * (τ * Real.log τ) := by
        intro τ; rw [hGd]
      -- ===== the quadratic test, with the logarithmic correction removed =====
      obtain ⟨Kc, hKc⟩ : ∃ k : ℝ, k = G l₀ - (A * l₀ ^ 2 + B * l₀ + C) := ⟨_, rfl⟩
      obtain ⟨ψ, hψd⟩ : ∃ p : ℝ → ℝ, p = fun τ : ℝ =>
          A * τ ^ 2 + B * τ + C + Kc - ‖d‖ ^ 2 * (τ * Real.log τ) := ⟨_, rfl⟩
      have hψeq : ψ l₀ = QuadEnvP u l₀ (toLp 2 (x₀ + l₀ • d, t)) := by
        simp only [hψd, hKc, hGv l₀]; ring
      have hIoo : ∀ᶠ τ : ℝ in nhds l₀, τ ∈ Set.Ioo (0:ℝ) T :=
        Filter.eventually_of_mem (isOpen_Ioo.mem_nhds ⟨hl₀0, hl₀T⟩) fun τ hτ => hτ
      have hle : ∀ᶠ τ : ℝ in nhds l₀,
          QuadEnvP u τ (toLp 2 (x₀ + τ • d, t)) ≤ ψ τ := by
        filter_upwards [eventually_nhdsWithin_iff.mp hmax, hIoo] with τ hτmax hτIoo
        have hh : G τ - (A * τ ^ 2 + B * τ + C) ≤ G l₀ - (A * l₀ ^ 2 + B * l₀ + C) :=
          hτmax ⟨hτIoo.1.le, hτIoo.2.le⟩
        simp only [hψd, hKc]
        linarith [hGv τ]
      -- ===== the optimizing competitor and the velocity it determines =====
      obtain ⟨y₀, hy₀⟩ : ∃ y : F, QuadEnvP u l₀ (toLp 2 (x₀ + l₀ • d, t))
          = u (toLp 2 (y, t + l₀)) - ‖y - (x₀ + l₀ • d)‖ ^ 2 / (2 * l₀) :=
        hatt l₀ (toLp 2 (x₀ + l₀ • d, t)) hl₀0 ht0 htl₀
      obtain ⟨q, hqd⟩ : ∃ p : F, p = (l₀)⁻¹ • (y₀ - (x₀ + l₀ • d)) := ⟨_, rfl⟩
      have hw : y₀ - (x₀ + l₀ • d) = l₀ • q := by
        rw [hqd, smul_smul, mul_inv_cancel₀ hl₀ne, one_smul]
      have hy₀e : y₀ = l₀ • q + (x₀ + l₀ • d) := by rw [← hw]; abel
      -- ===== the space-time test function =====
      obtain ⟨π₁, hπ₁⟩ : ∃ p : WithLp 2 (F × ℝ) →L[ℝ] F, ∀ ζ, p ζ = (ofLp ζ).1 :=
        ⟨(ContinuousLinearMap.fst ℝ F ℝ).comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap, fun ζ => rfl⟩
      obtain ⟨π₂, hπ₂⟩ : ∃ p : WithLp 2 (F × ℝ) →L[ℝ] ℝ, ∀ ζ, p ζ = (ofLp ζ).2 :=
        ⟨(ContinuousLinearMap.snd ℝ F ℝ).comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).toContinuousLinearMap, fun ζ => rfl⟩
      obtain ⟨Φ, hΦ⟩ : ∃ p : WithLp 2 (F × ℝ) → ℝ, p = fun ζ : WithLp 2 (F × ℝ) =>
          ψ (π₂ ζ - t)
            + ‖π₁ ζ - (x₀ + (π₂ ζ - t) • d)‖ ^ 2 * (2 * (π₂ ζ - t))⁻¹ := ⟨_, rfl⟩
      obtain ⟨ζ₀, hζ₀d⟩ : ∃ p : WithLp 2 (F × ℝ), p = toLp 2 (y₀, t + l₀) := ⟨_, rfl⟩
      have hπ₁ζ₀ : π₁ ζ₀ = y₀ := by rw [hπ₁, hζ₀d]
      have hπ₂ζ₀ : π₂ ζ₀ = t + l₀ := by rw [hπ₂, hζ₀d]
      have hτ₀ : π₂ ζ₀ - t = l₀ := by rw [hπ₂ζ₀]; ring
      -- regularity of the one-variable test, then of its space-time lift
      have hψC2 : ContDiffAt ℝ 2 ψ l₀ := by
        rw [hψd]
        have h1 : ContDiff ℝ 2 (fun τ : ℝ => A * τ ^ 2 + B * τ + C + Kc) := by fun_prop
        have h2 : ContDiffAt ℝ 2 (fun τ : ℝ => ‖d‖ ^ 2 * (τ * Real.log τ)) l₀ :=
          contDiffAt_const.mul (contDiffAt_id.mul (Real.contDiffAt_log.mpr hl₀ne))
        exact h1.contDiffAt.sub h2
      have hΦC2 : ContDiffAt ℝ 2 Φ ζ₀ := by
        rw [hΦ]
        have hmap : ContDiffAt ℝ 2 (fun ζ : WithLp 2 (F × ℝ) => π₂ ζ - t) ζ₀ :=
          (π₂.contDiff (n := 2)).contDiffAt.sub contDiffAt_const
        refine ContDiffAt.add ?_ (ContDiffAt.mul ?_ ?_)
        · have hψ' : ContDiffAt ℝ 2 ψ ((fun ζ : WithLp 2 (F × ℝ) => π₂ ζ - t) ζ₀) := by
            simp only [hτ₀]; exact hψC2
          exact ContDiffAt.comp ζ₀ hψ' hmap
        · exact ((contDiff_norm_sq ℝ).comp
            ((π₁.contDiff (n := 2)).sub
              (contDiff_const.add
                (((π₂.contDiff (n := 2)).sub contDiff_const).smul contDiff_const)))).contDiffAt
        · refine ContDiffAt.inv
            (contDiff_const.mul ((π₂.contDiff (n := 2)).sub contDiff_const)).contDiffAt ?_
          simp only [hτ₀]
          positivity
      have hΦζ₀ : Φ ζ₀ = ψ l₀ + ‖y₀ - (x₀ + l₀ • d)‖ ^ 2 * (2 * l₀)⁻¹ := by
        simp only [hΦ, hτ₀, hπ₁ζ₀]
      -- ===== the envelope licence (pm-0026): the forward envelope dominates every
      -- competitor, which is part (1) of EnvelopeCompetitorBounds and not a
      -- restatement of attainment =====
      have hdom : ∀ (l : ℝ) (y : F), 0 < l → t + l ∈ J →
          u (toLp 2 (y, t + l)) - ‖y - (x₀ + l • d)‖ ^ 2 / (2 * l)
            ≤ QuadEnvP u l (toLp 2 (x₀ + l • d, t)) := by
        intro l y hl htlJ
        exact ((EnvelopeCompetitorBounds J u hucont hugrow).1 l
          (toLp 2 (x₀ + l • d, t)) hl ht0 htlJ).1 y
      -- ===== `u - Φ` has a local maximum at the optimizer =====
      have hζ₀Ω : ζ₀ ∈ (fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' J := by
        rw [hζ₀d]; exact htl₀
      have hmaxΦ : IsLocalMaxOn (fun w => u w - Φ w)
          ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' J) ζ₀ := by
        have hval : u ζ₀ - Φ ζ₀ = 0 := by
          rw [hΦζ₀, hψeq, hy₀, hζ₀d, div_eq_mul_inv]; ring
        have hcont2 : Filter.Tendsto (fun ζ : WithLp 2 (F × ℝ) => π₂ ζ - t)
            (nhds ζ₀) (nhds l₀) := by
          have hh : Filter.Tendsto (fun ζ : WithLp 2 (F × ℝ) => π₂ ζ - t) (nhds ζ₀)
              (nhds (π₂ ζ₀ - t)) := (π₂.continuous.sub continuous_const).tendsto ζ₀
          rw [hτ₀] at hh
          exact hh
        rw [IsLocalMaxOn, IsMaxFilter, eventually_nhdsWithin_iff]
        filter_upwards [hcont2.eventually hle, hcont2.eventually hIoo] with ζ hζle hζIoo
        intro hζΩ
        show u ζ - Φ ζ ≤ u ζ₀ - Φ ζ₀
        rw [hval]
        obtain ⟨l, hld⟩ : ∃ s : ℝ, s = π₂ ζ - t := ⟨_, rfl⟩
        have hl0 : 0 < l := by rw [hld]; exact hζIoo.1
        have hζ2 : (ofLp ζ).2 = t + l := by rw [hld, hπ₂]; ring
        have htlJ : t + l ∈ J := by rw [← hζ2]; exact hζΩ
        have hζeq : ζ = toLp 2 ((ofLp ζ).1, t + l) := by rw [← hζ2]
        have hu : u ζ = u (toLp 2 ((ofLp ζ).1, t + l)) := by rw [← hζeq]
        have hΦζ : Φ ζ = ψ l + ‖(ofLp ζ).1 - (x₀ + l • d)‖ ^ 2 / (2 * l) := by
          simp only [hΦ, hld, hπ₁, div_eq_mul_inv]
        have hψl : QuadEnvP u l (toLp 2 (x₀ + l • d, t)) ≤ ψ l := by
          rw [hld]; exact hζle
        rw [hu, hΦζ]
        linarith [hdom l ((ofLp ζ).1) hl0 htlJ, hψl]
      have hop : 0 ≤ LimitOp Φ ζ₀ := husub.2.2 ζ₀ hζ₀Ω Φ hΦC2 hmaxΦ
      -- ===== the spatial gradient of the test function at the optimizer =====
      have hgradfd : ∀ a : F, fderiv ℝ Φ ζ₀ (toLp 2 (a, (0:ℝ))) = (inner ℝ q a : ℝ) := by
        intro a
        obtain ⟨c₀, hc₀⟩ : ∃ s : ℝ, s = ψ l₀ + l₀ ^ 2 * ‖q‖ ^ 2 * (2 * l₀)⁻¹ := ⟨_, rfl⟩
        obtain ⟨c₁, hc₁⟩ : ∃ s : ℝ, s = 2 * l₀ * (inner ℝ q a : ℝ) * (2 * l₀)⁻¹ := ⟨_, rfl⟩
        obtain ⟨c₂, hc₂⟩ : ∃ s : ℝ, s = ‖a‖ ^ 2 * (2 * l₀)⁻¹ := ⟨_, rfl⟩
        have hπ₂v : π₂ (toLp 2 (a, (0:ℝ)) : WithLp 2 (F × ℝ)) = 0 := by rw [hπ₂]
        have hπ₁v : π₁ (toLp 2 (a, (0:ℝ)) : WithLp 2 (F × ℝ)) = a := by rw [hπ₁]
        have hagree : ∀ᶠ h : ℝ in nhds (0:ℝ),
            Φ (ζ₀ + h • toLp 2 (a, (0:ℝ))) = c₀ + c₁ * h + c₂ * h ^ 2 := by
          filter_upwards with h
          have e2 : π₂ (ζ₀ + h • toLp 2 (a, (0:ℝ))) - t = l₀ := by
            rw [map_add, map_smul, hπ₂v, hπ₂ζ₀, smul_zero, add_zero]; ring
          have e1 : π₁ (ζ₀ + h • toLp 2 (a, (0:ℝ))) = y₀ + h • a := by
            rw [map_add, map_smul, hπ₁v, hπ₁ζ₀]
          have hsh : y₀ + h • a - (x₀ + l₀ • d) = l₀ • q + h • a := by
            rw [hy₀e]; abel
          simp only [hΦ, e1, e2, hsh, hc₀, hc₁, hc₂]
          rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
            real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
            sq_abs, sq_abs]
          ring
        have hderiv : ∀ᶠ h : ℝ in nhds (0:ℝ),
            HasDerivAt (fun k : ℝ => c₀ + c₁ * k + c₂ * k ^ 2) (c₁ + c₂ * (2 * h)) h := by
          filter_upwards with h
          have hb := (((hasDerivAt_const h c₀).add ((hasDerivAt_id h).const_mul c₁)).add
            ((hasDerivAt_pow 2 h).const_mul c₂))
          exact hb.congr_deriv (by push_cast; ring)
        have hderiv2 : HasDerivAt (fun k : ℝ => c₁ + c₂ * (2 * k)) (c₂ * 2) 0 := by
          have hb := (hasDerivAt_const (0:ℝ) c₁).add
            (((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).const_mul c₂)
          exact hb.congr_deriv (by ring)
        have hnode := SecondVariationAlongLine Φ ζ₀ (toLp 2 (a, (0:ℝ))) hΦC2
          (fun k : ℝ => c₀ + c₁ * k + c₂ * k ^ 2) (fun k : ℝ => c₁ + c₂ * (2 * k)) (c₂ * 2)
          hagree hderiv hderiv2
        rw [hnode.1, hc₁]
        field_simp
        ring
      have hgradq : (ofLp (gradient Φ ζ₀)).1 = q := by
        refine ext_inner_right ℝ fun a => ?_
        have h1 : (inner ℝ (gradient Φ ζ₀) (toLp 2 (a, (0:ℝ))) : ℝ)
            = fderiv ℝ Φ ζ₀ (toLp 2 (a, (0:ℝ))) := inner_gradient_left
        rw [WithLp.prod_inner_apply, hgradfd a] at h1
        simpa using h1
      -- ===== the second variation in the direction `(q, 1)` =====
      have hnb : {h : ℝ | 0 < l₀ + h} ∈ nhds (0:ℝ) := by
        refine (isOpen_lt continuous_const (continuous_const.add continuous_id)).mem_nhds ?_
        simpa using hl₀0
      have hlinid : ∀ h : ℝ, HasDerivAt (fun k : ℝ => l₀ + k) 1 h :=
        fun h => (hasDerivAt_id h).const_add l₀
      have hψ' : ∀ τ : ℝ, 0 < τ →
          HasDerivAt ψ (2 * A * τ + B - ‖d‖ ^ 2 * (Real.log τ + 1)) τ := by
        intro τ hτ
        have hτne : τ ≠ 0 := ne_of_gt hτ
        have h1 : HasDerivAt (fun s : ℝ => A * s ^ 2 + B * s + C + Kc) (2 * A * τ + B) τ := by
          have hb := ((((hasDerivAt_pow 2 τ).const_mul A).add
            ((hasDerivAt_id τ).const_mul B)).add_const C).add_const Kc
          exact hb.congr_deriv (by push_cast; ring)
        have h2 : HasDerivAt (fun s : ℝ => ‖d‖ ^ 2 * (s * Real.log s))
            (‖d‖ ^ 2 * (Real.log τ + 1)) τ := by
          have hb := ((hasDerivAt_id τ).mul (Real.hasDerivAt_log hτne)).const_mul (‖d‖ ^ 2)
          exact hb.congr_deriv (by simp only [id_eq]; field_simp)
        rw [hψd]
        exact h1.sub h2
      have hψ2 : HasDerivAt (fun s : ℝ => 2 * A * s + B - ‖d‖ ^ 2 * (Real.log s + 1))
          (2 * A - ‖d‖ ^ 2 * l₀⁻¹) l₀ := by
        have h1 : HasDerivAt (fun s : ℝ => 2 * A * s + B) (2 * A) l₀ := by
          have hb := ((hasDerivAt_id l₀).const_mul (2 * A)).add_const B
          exact hb.congr_deriv (by ring)
        exact h1.sub (((Real.hasDerivAt_log hl₀ne).add_const (1:ℝ)).const_mul (‖d‖ ^ 2))
      obtain ⟨R, hRd⟩ : ∃ p : ℝ → ℝ, p = fun h : ℝ =>
          ψ (l₀ + h) + (l₀ + h) * ‖q - d‖ ^ 2 / 2 + l₀ * (inner ℝ (q - d) d : ℝ)
            + l₀ ^ 2 * ‖d‖ ^ 2 * (2 * (l₀ + h))⁻¹ := ⟨_, rfl⟩
      obtain ⟨R', hR'd⟩ : ∃ p : ℝ → ℝ, p = fun h : ℝ =>
          (2 * A * (l₀ + h) + B - ‖d‖ ^ 2 * (Real.log (l₀ + h) + 1)) + ‖q - d‖ ^ 2 / 2
            - l₀ ^ 2 * ‖d‖ ^ 2 * (2 * (l₀ + h) ^ 2)⁻¹ := ⟨_, rfl⟩
      have hagree2 : ∀ᶠ h : ℝ in nhds (0:ℝ),
          Φ (ζ₀ + h • toLp 2 (q, (1:ℝ))) = R h := by
        filter_upwards [hnb] with h hh
        have hne : l₀ + h ≠ 0 := ne_of_gt hh
        have hπ₂v : π₂ (toLp 2 (q, (1:ℝ)) : WithLp 2 (F × ℝ)) = 1 := by rw [hπ₂]
        have hπ₁v : π₁ (toLp 2 (q, (1:ℝ)) : WithLp 2 (F × ℝ)) = q := by rw [hπ₁]
        have e2 : π₂ (ζ₀ + h • toLp 2 (q, (1:ℝ))) - t = l₀ + h := by
          rw [map_add, map_smul, hπ₂v, hπ₂ζ₀, smul_eq_mul, mul_one]; ring
        have e1 : π₁ (ζ₀ + h • toLp 2 (q, (1:ℝ))) = y₀ + h • q := by
          rw [map_add, map_smul, hπ₁v, hπ₁ζ₀]
        have hsh : y₀ + h • q - (x₀ + (l₀ + h) • d) = (l₀ + h) • (q - d) + l₀ • d := by
          rw [hy₀e]
          simp only [smul_sub, add_smul]
          abel
        simp only [hΦ, hRd, e1, e2, hsh]
        rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left,
          real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow,
          sq_abs, sq_abs]
        field_simp
        ring
      have hRderiv : ∀ᶠ h : ℝ in nhds (0:ℝ), HasDerivAt R (R' h) h := by
        filter_upwards [hnb] with h hh
        have hne : l₀ + h ≠ 0 := ne_of_gt hh
        have t1 : HasDerivAt (fun k : ℝ => ψ (l₀ + k))
            ((2 * A * (l₀ + h) + B - ‖d‖ ^ 2 * (Real.log (l₀ + h) + 1)) * 1) h :=
          (hψ' (l₀ + h) hh).comp h (hlinid h)
        have t2 : HasDerivAt (fun k : ℝ => (l₀ + k) * ‖q - d‖ ^ 2 / 2)
            (1 * ‖q - d‖ ^ 2 / 2) h :=
          ((hlinid h).mul_const (‖q - d‖ ^ 2)).div_const 2
        have t3 : HasDerivAt (fun _ : ℝ => l₀ * (inner ℝ (q - d) d : ℝ)) 0 h :=
          hasDerivAt_const h _
        have t4 := (((hlinid h).const_mul (2:ℝ)).inv
          (mul_ne_zero two_ne_zero hne)).const_mul (l₀ ^ 2 * ‖d‖ ^ 2)
        simp only [hRd, hR'd]
        exact (((t1.add t2).add t3).add t4).congr_deriv (by field_simp; ring)
      have hR'deriv : HasDerivAt R' (2 * A) 0 := by
        have hne0 : l₀ + 0 ≠ 0 := by simpa using hl₀ne
        have hψ2' : HasDerivAt (fun s : ℝ => 2 * A * s + B - ‖d‖ ^ 2 * (Real.log s + 1))
            (2 * A - ‖d‖ ^ 2 * l₀⁻¹) (l₀ + 0) := by simpa using hψ2
        have s1 := hψ2'.comp (0:ℝ) (hlinid 0)
        have s2 : HasDerivAt (fun _ : ℝ => ‖q - d‖ ^ 2 / 2) 0 (0:ℝ) :=
          hasDerivAt_const _ _
        have s3 := ((((hlinid 0).fun_pow 2).const_mul (2:ℝ)).inv
          (mul_ne_zero two_ne_zero (pow_ne_zero 2 hne0))).const_mul (l₀ ^ 2 * ‖d‖ ^ 2)
        simp only [hR'd]
        exact ((s1.add s2).sub s3).congr_deriv (by push_cast; field_simp; ring)
      have hnode2 := SecondVariationAlongLine Φ ζ₀ (toLp 2 (q, (1:ℝ))) hΦC2 R R' (2 * A)
        hagree2 hRderiv hR'deriv
      have hLO : LimitOp Φ ζ₀ = 2 * A := by
        simp only [LimitOp]
        rw [hgradq]
        exact hnode2.2
      rw [hLO] at hop
      linarith
    -- Step 3 of the .tex is now a single citation.
    have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) T) G := ViscosityConvexOnIcc T hT G hGc htest
    rw [hGd] at hconv
    exact hconv
  refine ⟨fun hsub x₀ d t hadm => part1 I hI f hcont hgrow hsub x₀ d t hadm, ?_⟩
  -- ===================== Part (2): the backward envelope, by time reversal ===========
  intro hsuper x t hadm
  obtain ⟨hrev1, hrev2, hrev3, -, -, -, -⟩ := TimeReversal (0:ℝ) f
  obtain ⟨Jm, hJmd⟩ : ∃ s : Set ℝ, s = (fun σ : ℝ => -σ) ⁻¹' I := ⟨_, rfl⟩
  have hJmopen : IsOpen Jm := by rw [hJmd]; exact hI.preimage continuous_neg
  -- the reflection, and the fact that it carries the reflected slab onto the slab
  obtain ⟨R, hRd⟩ : ∃ r : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ),
      r = fun z => toLp 2 ((ofLp z).1, -(ofLp z).2) := ⟨_, rfl⟩
  have hRc : Continuous R := by
    rw [hRd]
    exact (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.continuous.comp
      (((continuous_fst.comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous)).prodMk
        (continuous_neg.comp (continuous_snd.comp
          (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous)))
  have hpre : ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Jm)
      = R ⁻¹' ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) := by
    rw [hJmd, hRd]
    rfl
  -- the three hypotheses of Part (1) for the time reversal on the reflected time set
  have hTFsub : IsLimitSubOn ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Jm)
      (TimeFlip f) := by
    rw [hpre, hRd]
    exact hrev2 _ hsuper
  have hTFcont : ContinuousOn (TimeFlip f)
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Jm) := hTFsub.2.1
  have hTFgrow : SubquadraticGrowth Jm (TimeFlip f) := by
    intro K hKJ hKc ε hε
    have hnegK : (fun σ : ℝ => -σ) '' K ⊆ I := by
      rintro σ ⟨r, hr, rfl⟩
      have := hKJ hr
      rw [hJmd] at this
      exact this
    obtain ⟨M, hM0, hMb⟩ := hgrow ((fun σ : ℝ => -σ) '' K) hnegK
      (hKc.image continuous_neg) ε hε
    refine ⟨M, hM0, fun z hz hzK => ?_⟩
    have hb := hMb (R z) (by rw [hRd]; exact hz) (by rw [hRd]; exact ⟨(ofLp z).2, hzK, rfl⟩)
    simp only [hRd] at hb
    rw [TimeFlip, abs_neg]
    exact hb
  -- apply the generalized Part (1) with `d = 0` and base time `-t`
  have hadm' : ∀ l ∈ Set.Icc (0:ℝ) T, -t + l ∈ Jm := by
    intro l hl
    rw [hJmd]
    show -(-t + l) ∈ I
    have he : -(-t + l) = t - l := by ring
    rw [he]
    exact hadm l hl
  have hcv := part1 Jm hJmopen (TimeFlip f) hTFcont hTFgrow hTFsub x 0 (-t) hadm'
  -- rewrite the conclusion through the time-reversal identity
  have hfun : (fun l : ℝ => QuadEnvP (TimeFlip f) l (toLp 2 (x + l • (0:F), -t))
        + ‖(0:F)‖ ^ 2 * (l * Real.log l))
      = fun l : ℝ => -QuadEnvM f l (toLp 2 (x, t)) := by
    funext l
    rw [norm_zero]
    show QuadEnvP (TimeFlip f) l (toLp 2 (x + l • (0:F), -t)) + 0 ^ 2 * (l * Real.log l)
      = -QuadEnvM f l (toLp 2 (x, t))
    rw [smul_zero, add_zero, hrev3 l (toLp 2 (x, -t))]
    show -QuadEnvM f l (toLp 2 (x, -(-t))) + 0 ^ 2 * (l * Real.log l) = _
    rw [neg_neg]
    ring
  rw [hfun] at hcv
  have hneg := hcv.neg
  have hfun2 : (-fun l : ℝ => -QuadEnvM f l (toLp 2 (x, t)))
      = fun l : ℝ => QuadEnvM f l (toLp 2 (x, t)) := by
    funext l; simp
  rw [hfun2] at hneg
  exact hneg
