module

public import InfHarmonic.EnvSlopeP
public import InfHarmonic.EnvSlopeM
public import InfHarmonic.QuadEnvPathConvex
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.EnvelopeCompetitorBounds

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.4, subsolution half: the forward envelope slope is nondecreasing in
the length, and the small-length upper limit of the backward slope is at most
every forward slope. -/
theorem EnvelopeSlopeOrder (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f)
    (hsub : IsLimitSubOn ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) f) :
    (∀ (z : WithLp 2 (F × ℝ)) (l l' : ℝ), 0 < l → l ≤ l' →
        (∀ σ ∈ Set.Icc (0 : ℝ) l', (ofLp z).2 + σ ∈ I) →
        EnvSlopeP f l z ≤ EnvSlopeP f l' z) ∧
    (∀ (z : WithLp 2 (F × ℝ)) (h ε : ℝ), 0 < h → 0 < ε →
        (∀ σ ∈ Set.Icc (-h) h, (ofLp z).2 + σ ∈ I) →
        ∃ δ : ℝ, 0 < δ ∧ ∀ l : ℝ, 0 < l → l < δ →
          EnvSlopeM f l z ≤ EnvSlopeP f h z + ε) := by
  classical
  have hP0 : ∀ ζ : WithLp 2 (F × ℝ), QuadEnvP f 0 ζ = f ζ := by
    intro ζ; rw [QuadEnvP, if_pos rfl]
  -- ===================== (1): the chord slope from a fixed left endpoint ============
  -- `EnvSlopeP f σ z` is the slope of the chord of `σ ↦ P_σ f z` from `0` to `σ`, and
  -- that function is convex by QuadEnvPathConvex at `d = 0`, where the centre stops
  -- depending on the length and the logarithmic correction vanishes.
  have hmono : ∀ (z : WithLp 2 (F × ℝ)) (l l' : ℝ), 0 < l → l ≤ l' →
      (∀ σ ∈ Set.Icc (0 : ℝ) l', (ofLp z).2 + σ ∈ I) →
      EnvSlopeP f l z ≤ EnvSlopeP f l' z := by
    intro z l l' hl hll' hadm
    have hl'0 : 0 < l' := lt_of_lt_of_le hl hll'
    have hconv := (QuadEnvPathConvex I hI f hcont hgrow l' hl'0).1 hsub (ofLp z).1 0
      (ofLp z).2 hadm
    have hfun : (fun s : ℝ => QuadEnvP f s (toLp 2 ((ofLp z).1 + s • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * (s * Real.log s))
        = fun s : ℝ => QuadEnvP f s z := by
      funext s
      rw [smul_zero, add_zero, norm_zero]
      show QuadEnvP f s z + (0 : ℝ) ^ 2 * (s * Real.log s) = QuadEnvP f s z
      ring
    rw [hfun] at hconv
    rcases eq_or_lt_of_le hll' with heq | hlt
    · subst heq; exact le_rfl
    · have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) l' := ⟨le_refl 0, hl'0.le⟩
      have h1 : l' ∈ Set.Icc (0 : ℝ) l' := ⟨hl'0.le, le_refl l'⟩
      have hadj := hconv.slope_mono_adjacent h0 h1 hl hlt
      simp only [hP0, sub_zero] at hadj
      have hpos : 0 < l' - l := by linarith
      rw [div_le_div_iff₀ hl hpos] at hadj
      simp only [EnvSlopeP]
      rw [div_le_div_iff₀ hl hl'0]
      have he1 : (QuadEnvP f l z - f z) * l'
          = (QuadEnvP f l z - f z) * (l' - l) + (QuadEnvP f l z - f z) * l := by ring
      have he2 : (QuadEnvP f l' z - QuadEnvP f l z) * l + (QuadEnvP f l z - f z) * l
          = (QuadEnvP f l' z - f z) * l := by ring
      linarith
  refine ⟨hmono, ?_⟩
  -- ===================== (2): the cross inequality, then two limits =================
  intro z hh ε hh0 hε hadm
  obtain ⟨-, hattM, hcontP, -, -, hloc⟩ := QuadEnvAttained I hI f hcont hgrow
  have htI : (ofLp z).2 ∈ I := by
    have hz := hadm 0 ⟨by linarith, hh0.le⟩
    rwa [add_zero] at hz
  have hthI : (ofLp z).2 + hh ∈ I := hadm hh ⟨by linarith, le_refl hh⟩
  -- `ζ ↦ S⁺_hh f ζ` is continuous at `z`: the envelope is jointly continuous and `f` is
  -- continuous on the open slab
  have hOopen : IsOpen ((fun w : WithLp 2 (F × ℝ) => (ofLp w).2) ⁻¹' I) :=
    hI.preimage (continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous)
  have hfA : ContinuousAt f z := hcont.continuousAt (hOopen.mem_nhds htI)
  have hQA : ContinuousAt (fun ζ : WithLp 2 (F × ℝ) => QuadEnvP f hh ζ) z := by
    have hcA := hcontP hh hh0 z htI hthI
    have hmap : ContinuousAt
        (fun ζ : WithLp 2 (F × ℝ) => ((hh, ζ) : ℝ × WithLp 2 (F × ℝ))) z :=
      (continuous_const.prodMk continuous_id).continuousAt
    exact Filter.Tendsto.comp hcA hmap
  have hSA : ContinuousAt (fun ζ : WithLp 2 (F × ℝ) => EnvSlopeP f hh ζ) z := by
    have hdiv : ContinuousAt
        (fun ζ : WithLp 2 (F × ℝ) => (QuadEnvP f hh ζ - f ζ) / hh) z :=
      (hQA.sub hfA).div_const hh
    exact hdiv
  obtain ⟨δ₁, hδ₁, hδ₁p⟩ := Metric.continuousAt_iff.mp hSA ε hε
  -- the optimizer localization at length zero, with tolerance `δ₁ / 4`
  obtain ⟨δ₂, hδ₂, hlocp⟩ := hloc z htI (δ₁ / 4) (by linarith)
  refine ⟨min (min δ₂ hh) (δ₁ / 4), lt_min (lt_min hδ₂ hh0) (by linarith), ?_⟩
  intro l hl hlδ
  have hlδ₂ : l < δ₂ := lt_of_lt_of_le hlδ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hlh : l < hh := lt_of_lt_of_le hlδ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hlδ₁ : l < δ₁ / 4 := lt_of_lt_of_le hlδ (min_le_right _ _)
  have htlI : (ofLp z).2 - l ∈ I := by
    have hz := hadm (-l) ⟨by linarith, by linarith⟩
    have he : (ofLp z).2 + -l = (ofLp z).2 - l := by ring
    rwa [he] at hz
  -- the backward optimizer and the point it determines
  obtain ⟨y, hy⟩ : ∃ y : F, QuadEnvM f l z
      = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
    hattM l z hl htI htlI
  have hyloc : ‖y - (ofLp z).1‖ ≤ δ₁ / 4 := (hlocp l hl hlδ₂ y).2 hy
  obtain ⟨w, hwd⟩ : ∃ w : WithLp 2 (F × ℝ), w = toLp 2 (y, (ofLp z).2 - l) := ⟨_, rfl⟩
  have hw1 : (ofLp w).1 = y := by rw [hwd]
  have hw2 : (ofLp w).2 = (ofLp z).2 - l := by rw [hwd]
  -- it is close to `z`
  have hdle : dist w z ≤ ‖y - (ofLp z).1‖ + l := by
    rw [hwd, WithLp.prod_dist_eq_of_L2]
    have e1 : dist (toLp 2 (y, (ofLp z).2 - l) : WithLp 2 (F × ℝ)).fst z.fst
        = ‖y - (ofLp z).1‖ := by
      show dist y (ofLp z).1 = _
      rw [dist_eq_norm]
    have e2 : dist (toLp 2 (y, (ofLp z).2 - l) : WithLp 2 (F × ℝ)).snd z.snd = l := by
      show dist ((ofLp z).2 - l) (ofLp z).2 = l
      rw [Real.dist_eq, show (ofLp z).2 - l - (ofLp z).2 = -l from by ring, abs_neg,
        abs_of_pos hl]
    rw [e1, e2]
    have hnn : (0 : ℝ) ≤ ‖y - (ofLp z).1‖ + l := by positivity
    calc Real.sqrt (‖y - (ofLp z).1‖ ^ 2 + l ^ 2)
        ≤ Real.sqrt ((‖y - (ofLp z).1‖ + l) ^ 2) := by
          refine Real.sqrt_le_sqrt ?_
          nlinarith [norm_nonneg (y - (ofLp z).1), hl.le]
      _ = ‖y - (ofLp z).1‖ + l := Real.sqrt_sq hnn
  have hdist : dist w z < δ₁ := lt_of_le_of_lt hdle (by linarith)
  -- the cross inequality: `z` is a forward competitor from `w`.  The domination is
  -- part (1) of EnvelopeCompetitorBounds, whose first clause says exactly that the
  -- forward envelope dominates every competitor value.
  have hw2l : (ofLp w).2 + l = (ofLp z).2 := by rw [hw2]; ring
  have hdomw := ((EnvelopeCompetitorBounds I f hcont hgrow).1 l w hl
    (by rw [hw2]; exact htlI) (by rw [hw2l]; exact htI)).1 (ofLp z).1
  have hcross : f z - ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ QuadEnvP f l w := by
    have hz : (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := rfl
    rw [hw2l, hw1, hz, norm_sub_rev] at hdomw
    exact hdomw
  have hslope : EnvSlopeM f l z ≤ EnvSlopeP f l w := by
    have hM : QuadEnvM f l z = f w + ‖y - (ofLp z).1‖ ^ 2 / (2 * l) := by
      rw [hy, hwd]
    simp only [EnvSlopeM, EnvSlopeP, hM]
    rw [div_le_div_iff₀ hl hl]
    have hnum : f z - (f w + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) ≤ QuadEnvP f l w - f w := by
      linarith
    exact mul_le_mul_of_nonneg_right hnum hl.le
  -- monotonicity of the forward slope at the centre `w`
  have hadmw : ∀ σ ∈ Set.Icc (0 : ℝ) hh, (ofLp w).2 + σ ∈ I := by
    intro σ hσ
    rw [hw2, show (ofLp z).2 - l + σ = (ofLp z).2 + (σ - l) from by ring]
    exact hadm (σ - l) ⟨by linarith [hσ.1, hσ.2], by linarith [hσ.1, hσ.2]⟩
  have hmonow := hmono w l hh hl hlh.le hadmw
  -- and continuity of the forward slope in the centre at the fixed length `hh`
  have hclose : dist (EnvSlopeP f hh w) (EnvSlopeP f hh z) < ε := hδ₁p hdist
  have hfin : EnvSlopeP f hh w ≤ EnvSlopeP f hh z + ε := by
    rw [Real.dist_eq] at hclose
    have habs := abs_lt.mp hclose
    linarith [habs.2]
  linarith
