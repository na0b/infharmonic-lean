import InfHarmonic.SupConvolutionMagic
import InfHarmonic.JensenLemma
import InfHarmonic.SemiconvexSecondOrderAe
import InfHarmonic.SymmetricFormNormFromDiagonal
set_option linter.unusedSectionVars false
open Set MeasureTheory Metric
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Part IV of the theorem of sums: Jensen's lemma supplies a point of positive
measure at which a small linear perturbation of the semiconvex test `Υ` has a
local maximum, Alexandrov's theorem for semiconvex functions supplies a
second-order expansion there, and the two combine into a superjet of each
`G j ^ ε` whose Hessians add up to at most the quadratic form of `Aeps`.  The
magic property of the sup-convolution then moves the jet onto `G j` itself, at
the shifted base point `z' j + ε • Pv j`. -/
theorem SumRuleJetFromJensen (N : ℕ) (G : Fin N → E → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hGc : ∀ j, Continuous (G j)) (hGb : ∀ j, ∀ w : E, G j w ≤ C)
    (ε : ℝ) (hε : 0 < ε)
    (Aeps : PiLp 2 (fun _ : Fin N => E) →L[ℝ] PiLp 2 (fun _ : Fin N => E))
    (hAs : ∀ ξ ζ : PiLp 2 (fun _ : Fin N => E), inner ℝ (Aeps ξ) ζ = inner ℝ ξ (Aeps ζ))
    (Υ : PiLp 2 (fun _ : Fin N => E) → ℝ)
    (hΥdef : ∀ Z : PiLp 2 (fun _ : Fin N => E), Υ Z =
      SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
        - (inner ℝ (Aeps Z) Z : ℝ) / 2)
    (hsep : ∀ Z : PiLp 2 (fun _ : Fin N => E),
      SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
        = ∑ j, SupConvolution ε (G j) (ofLp Z j))
    (hΥ0 : Υ 0 = 0) (hΥneg : ∀ Z : PiLp 2 (fun _ : Fin N => E), Z ≠ 0 → Υ Z < 0)
    (hΥsc : SemiconvexOn (1 / ε + ‖Aeps‖) Set.univ Υ) (hΥc : Continuous Υ)
    (R δ' : ℝ) (hR : 0 < R) (hδ' : 0 < δ') :
    ∃ (Z' Pv : PiLp 2 (fun _ : Fin N => E)) (X : Fin N → (E →L[ℝ] E →L[ℝ] ℝ)),
      ‖Z'‖ < R ∧ ‖Pv‖ ≤ δ' + ‖Aeps‖ * R ∧
      (∀ j, ∀ a b : E, X j a b = X j b a) ∧
      (∀ j, ‖X j‖ ≤ 1 / ε + 2 * ‖Aeps‖) ∧
      (∀ j, ((ofLp Pv j), X j) ∈ Superjet (G j) (ofLp Z' j + ε • ofLp Pv j)) ∧
      (∀ ζ : PiLp 2 (fun _ : Fin N => E),
        (∑ j, X j (ofLp ζ j) (ofLp ζ j)) ≤ (inner ℝ (Aeps ζ) ζ : ℝ)) := by
  classical
  -- DURABLE ROUTE NOTES (burst 401, closure burst).
  --   * THE MEASURE LIVES ON V, NOT ON E.  The node's `[MeasurableSpace E] [BorelSpace E]` are
  --     never consumed: `borelize` installs the Borel structure on `PiLp 2 (fun _ => E)` and
  --     `Measure.addHaar` on that space is what `JensenLemma` and `SemiconvexSecondOrderAe` are
  --     applied to.  Hence the `linter.unusedSectionVars` suppression above the marker.
  --   * EVERY `t ↓ 0` LIMIT OF THE .tex IS A SINGLE EXPLICIT SMALL `t`.  Three times
  --     (`hfirst`, `hsecond`, `hdiag`) the pattern is: pick `t = <bound> / (2 * ‖·‖)` so that
  --     `t * ‖·‖` is half the admissible radius, apply the hypothesis once, and divide by
  --     `t` or `t ^ 2` with `le_of_mul_le_mul_left`.  No filter and no `Tendsto`.
  --   * `hfirst` USES THE SAME TRICK AS `MaxMultiplierPinsSubgradient`: test the combined
  --     inequality in the direction of `d = qU + Q` itself (not a normalized vector), with
  --     `t` small enough that `t * (‖AU‖/2 + 1) < 1`; `1 ≤ t * Kc < 1` is the contradiction.
  --   * (J2) DOES NOT GO THROUGH (eq:srjj-bounds) IN LEAN.  The diagonal bound on `X j` comes
  --     straight from `hAUlb`, `hsecond` and Cauchy-Schwarz on `Aeps`, and
  --     `SymmetricFormNormFromDiagonal` turns it into the operator-norm bound.  That helper was
  --     peeled off because inlining its polarization-plus-scaling argument here exhausted the
  --     default heartbeat budget in a 470-line declaration (the timeout surfaced at an innocent
  --     later `simp only`, as usual); peeling it out fixed the budget without a `set_option`.
  borelize (PiLp 2 (fun _ : Fin N => E))
  -- Body-only acknowledgement: `hC : 0 ≤ C` belongs to this node's protected signature, but the
  -- route consumes `C` only through the growth bound `G j w ≤ C + ‖w‖` that
  -- `SupConvolutionMagic` wants, which needs no sign.
  have _hC : (0:ℝ) ≤ C := hC
  -- the semiconvexity constant
  obtain ⟨lam, hlamd⟩ : ∃ x : ℝ, x = 1 / ε + ‖Aeps‖ := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by
    rw [hlamd]
    have h1 : (0:ℝ) < 1 / ε := by positivity
    linarith [norm_nonneg Aeps]
  rw [← hlamd] at hΥsc
  -- ============ the coordinate embeddings ι j : E →L[ℝ] V ============
  obtain ⟨iota, hiota⟩ : ∃ f : Fin N → (E →L[ℝ] PiLp 2 (fun _ : Fin N => E)),
      ∀ (j : Fin N) (a : E), ofLp (f j a) = Pi.single j a :=
    ⟨fun j => LinearMap.toContinuousLinearMap
      (((WithLp.linearEquiv 2 ℝ (∀ _ : Fin N, E)).symm.toLinearMap).comp
        (LinearMap.single ℝ (fun _ : Fin N => E) j)), fun j a => rfl⟩
  have hiotan : ∀ (j : Fin N) (a : E), ‖iota j a‖ = ‖a‖ := by
    intro j a
    have h1 : ‖iota j a‖ ^ 2 = ‖a‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply,
        Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
      · rw [hiota j a]; simp
      · intro i _ hij; rw [hiota j a]; simp [hij]
    nlinarith [norm_nonneg (iota j a), norm_nonneg a]
  have hiotai : ∀ (j : Fin N) (ξ : PiLp 2 (fun _ : Fin N => E)) (a : E),
      (inner ℝ ξ (iota j a) : ℝ) = inner ℝ (ofLp ξ j) a := by
    intro j ξ a
    rw [PiLp.inner_apply, Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · rw [hiota j a]; simp
    · intro i _ hij; rw [hiota j a]; simp [hij]
  -- the two ℓ²-product identities used throughout
  have hpyth : ∀ ζ : PiLp 2 (fun _ : Fin N => E), (∑ j, ‖ofLp ζ j‖ ^ 2) = ‖ζ‖ ^ 2 := by
    intro ζ
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_self_eq_norm_sq])
  have hco : ∀ (ζ : PiLp 2 (fun _ : Fin N => E)) (j : Fin N), ‖ofLp ζ j‖ ≤ ‖ζ‖ := by
    intro ζ j
    have h1 : ‖ofLp ζ j‖ ^ 2 ≤ ∑ i, ‖ofLp ζ i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin N => ‖ofLp ζ i‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ j)
    rw [hpyth ζ] at h1
    nlinarith [norm_nonneg (ofLp ζ j), norm_nonneg ζ]
  -- ============ Step 1: a good point ============
  have hΥscB : SemiconvexOn lam (ball (0 : PiLp 2 (fun _ : Fin N => E)) R) Υ := by
    have hc1 : ConvexOn ℝ (Set.univ : Set (PiLp 2 (fun _ : Fin N => E)))
        (fun z => Υ z + lam * ‖z‖ ^ 2 / 2) := hΥsc
    exact hc1.subset (Set.subset_univ _) (convex_ball _ _)
  have hstrict : ∀ Z ∈ closedBall (0 : PiLp 2 (fun _ : Fin N => E)) R,
      Z ≠ 0 → Υ Z < Υ 0 := by
    intro Z _ hne
    rw [hΥ0]
    exact hΥneg Z hne
  have hK := JensenLemma
    (Measure.addHaar : Measure (PiLp 2 (fun _ : Fin N => E))) lam R hlam0 hR Υ 0
    hΥc.continuousOn hΥscB hstrict δ' hδ'
  have hae := SemiconvexSecondOrderAe
    (Measure.addHaar : Measure (PiLp 2 (fun _ : Fin N => E))) lam hlam0.le
    (ball (0 : PiLp 2 (fun _ : Fin N => E)) R) isOpen_ball Υ hΥscB
  obtain ⟨Zh, hZhK, hZhgood⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt hK) (MeasureTheory.ae_restrict_of_ae hae)
  obtain ⟨hZhball, Q, hQn, hQmax⟩ := hZhK
  obtain ⟨qU, AU, hAUsym, hAUlb, hAUexp⟩ := hZhgood hZhball
  have hZhR : ‖Zh‖ < R := by
    have := hZhball
    simpa [mem_ball, dist_eq_norm] using this
  -- ============ Step 2: first- and second-order conditions ============
  -- the local maximum on the open ball gives a genuine radius
  obtain ⟨ρ₁, hρ₁, hmax⟩ : ∃ ρ₁ > 0, ∀ ζ : PiLp 2 (fun _ : Fin N => E), ‖ζ‖ < ρ₁ →
      Υ (Zh + ζ) - Υ Zh ≤ -(inner ℝ Q ζ : ℝ) := by
    rw [IsLocalMaxOn, IsMaxFilter, isOpen_ball.nhdsWithin_eq hZhball] at hQmax
    obtain ⟨r0, hr0, hb⟩ := Metric.eventually_nhds_iff.mp hQmax
    refine ⟨r0, hr0, fun ζ hζ => ?_⟩
    have hd : dist (Zh + ζ) Zh < r0 := by
      simp only [dist_eq_norm, add_sub_cancel_left]
      exact hζ
    have h1 := hb hd
    simp only [inner_add_right] at h1
    linarith
  -- the scaling identity for the Hessian form
  have hscale : ∀ (s : ℝ) (v : PiLp 2 (fun _ : Fin N => E)),
      AU (s • v) (s • v) = s ^ 2 * AU v v := by
    intro s v
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hAUb : ∀ ζ : PiLp 2 (fun _ : Fin N => E), |AU ζ ζ| ≤ ‖AU‖ * ‖ζ‖ ^ 2 := by
    intro ζ
    have h1 : ‖AU ζ ζ‖ ≤ ‖AU‖ * ‖ζ‖ * ‖ζ‖ := AU.le_opNorm₂ ζ ζ
    rw [Real.norm_eq_abs] at h1
    nlinarith [h1]
  -- the combined first/second-order inequality
  have hcomb : ∀ δ > 0, ∃ ρ > 0, ∀ ζ : PiLp 2 (fun _ : Fin N => E), ‖ζ‖ < ρ →
      (inner ℝ (qU + Q) ζ : ℝ) ≤ -(AU ζ ζ) / 2 + δ * ‖ζ‖ ^ 2 := by
    intro δ hδ
    obtain ⟨ρ, hρ, hexp⟩ := hAUexp δ hδ
    refine ⟨min ρ₁ ρ, lt_min hρ₁ hρ, fun ζ hζ => ?_⟩
    have h1 := hmax ζ (lt_of_lt_of_le hζ (min_le_left _ _))
    have h2 := abs_le.mp (hexp ζ (lt_of_lt_of_le hζ (min_le_right _ _)))
    rw [inner_add_left]
    linarith [h2.1]
  -- (eq:srjj-first): the linear term is pinned, qU = -Q
  have hfirst : qU + Q = 0 := by
    obtain ⟨ρ, hρ, hc1⟩ := hcomb 1 one_pos
    by_contra hdne
    have hdpos : 0 < ‖qU + Q‖ := norm_pos_iff.mpr hdne
    obtain ⟨Kc, hKcd⟩ : ∃ x : ℝ, x = ‖AU‖ / 2 + 1 := ⟨_, rfl⟩
    have hKc0 : 0 < Kc := by rw [hKcd]; positivity
    obtain ⟨t, ht0, htρ, htK⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖qU + Q‖ < ρ ∧ t * Kc < 1 :=
      ⟨min (ρ / (2 * ‖qU + Q‖)) (1 / (2 * Kc)), lt_min (by positivity) (by positivity),
        by
          have h1 : min (ρ / (2 * ‖qU + Q‖)) (1 / (2 * Kc)) ≤ ρ / (2 * ‖qU + Q‖) :=
            min_le_left _ _
          have h2 : ρ / (2 * ‖qU + Q‖) * ‖qU + Q‖ = ρ / 2 := by field_simp
          nlinarith [hdpos],
        by
          have h1 : min (ρ / (2 * ‖qU + Q‖)) (1 / (2 * Kc)) ≤ 1 / (2 * Kc) :=
            min_le_right _ _
          have h2 : 1 / (2 * Kc) * Kc = 1 / 2 := by field_simp
          nlinarith [hKc0]⟩
    have hnt : ‖t • (qU + Q)‖ = t * ‖qU + Q‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have hstep := hc1 (t • (qU + Q)) (by rw [hnt]; exact htρ)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hnt] at hstep
    have hq := hAUb (t • (qU + Q))
    rw [hnt] at hq
    have hqa := abs_le.mp hq
    -- `t‖d‖² ≤ Kc t²‖d‖²` with `t Kc < 1` is a contradiction
    have hP : 0 < t * ‖qU + Q‖ ^ 2 := by positivity
    have hone : 1 ≤ t * Kc := by
      refine le_of_mul_le_mul_right ?_ hP
      have heq : t * Kc * (t * ‖qU + Q‖ ^ 2)
          = (‖AU‖ / 2) * (t * ‖qU + Q‖) ^ 2 + (t * ‖qU + Q‖) ^ 2 := by
        rw [hKcd]; ring
      rw [one_mul, heq]
      linarith [hqa.1, hstep]
    linarith
  -- (eq:srjj-second): the Hessian form is nonpositive
  have hsecond : ∀ ζ : PiLp 2 (fun _ : Fin N => E), AU ζ ζ ≤ 0 := by
    intro ζ
    rcases eq_or_ne ζ 0 with h0 | h0
    · rw [h0]; simp
    · have hζp : 0 < ‖ζ‖ := norm_pos_iff.mpr h0
      refine le_of_forall_pos_le_add (fun η hη => ?_)
      obtain ⟨ρ, hρ, hc⟩ := hcomb (η / (2 * ‖ζ‖ ^ 2)) (by positivity)
      obtain ⟨t, ht0, htρ⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖ζ‖ < ρ :=
        ⟨ρ / (2 * ‖ζ‖), by positivity, by
          have h2 : ρ / (2 * ‖ζ‖) * ‖ζ‖ = ρ / 2 := by field_simp
          nlinarith [hζp]⟩
      have hnt : ‖t • ζ‖ = t * ‖ζ‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have hstep := hc (t • ζ) (by rw [hnt]; exact htρ)
      rw [hfirst, inner_zero_left, hscale t ζ, hnt] at hstep
      have ht2 : 0 < t ^ 2 := by positivity
      have hkey : t ^ 2 * (AU ζ ζ) ≤ t ^ 2 * η := by
        have hrw : η / (2 * ‖ζ‖ ^ 2) * (t * ‖ζ‖) ^ 2 = t ^ 2 * η / 2 := by
          field_simp
        rw [hrw] at hstep
        linarith
      have := le_of_mul_le_mul_left hkey ht2
      linarith
  -- ============ Step 3: the shifted linear term Π, the form A', and the X j ============
  have hqU : qU = -Q := by linear_combination (norm := module) hfirst
  obtain ⟨Pv0, hPv0d⟩ : ∃ v : PiLp 2 (fun _ : Fin N => E), v = qU + Aeps Zh := ⟨_, rfl⟩
  -- the bundled inner-product form must be BOUND FIRST: written inline, the summand
  -- elaborates at `V →L⋆[ℝ] V →L[ℝ] ℝ` and the `HAdd` instance fails
  obtain ⟨Gin, hGin⟩ : ∃ Gi : PiLp 2 (fun _ : Fin N => E) →L[ℝ]
      PiLp 2 (fun _ : Fin N => E) →L[ℝ] ℝ, ∀ a b, Gi a b = (inner ℝ a b : ℝ) :=
    ⟨innerSL ℝ, fun _ _ => rfl⟩
  obtain ⟨A', hA'app⟩ : ∃ A : PiLp 2 (fun _ : Fin N => E) →L[ℝ]
        PiLp 2 (fun _ : Fin N => E) →L[ℝ] ℝ,
      ∀ u v, A u v = AU u v + (inner ℝ (Aeps u) v : ℝ) :=
    ⟨AU + Gin.comp Aeps, fun u v => by
      simp only [add_apply, ContinuousLinearMap.coe_comp, Function.comp_apply]
      rw [hGin]⟩
  obtain ⟨X, hXapp⟩ : ∃ X : Fin N → (E →L[ℝ] E →L[ℝ] ℝ),
      ∀ (j : Fin N) (a b : E), X j a b = A' (iota j a) (iota j b) :=
    ⟨fun j => A'.bilinearComp (iota j) (iota j), fun j a b => rfl⟩
  have hA'sym : ∀ u v : PiLp 2 (fun _ : Fin N => E), A' u v = A' v u := by
    intro u v
    rw [hA'app, hA'app, hAUsym u v, hAs u v, real_inner_comm]
  have hXsym : ∀ (j : Fin N) (a b : E), X j a b = X j b a := by
    intro j a b
    rw [hXapp, hXapp, hA'sym]
  -- `SupConvolution` of the sum, written through Υ
  have hSCeq : ∀ Z : PiLp 2 (fun _ : Fin N => E),
      SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Z
        = Υ Z + (inner ℝ (Aeps Z) Z : ℝ) / 2 := by
    intro Z; rw [hΥdef Z]; ring
  have hAexp2 : ∀ u v : PiLp 2 (fun _ : Fin N => E),
      (inner ℝ (Aeps (u + v)) (u + v) : ℝ)
        = (inner ℝ (Aeps u) u : ℝ) + 2 * (inner ℝ (Aeps u) v : ℝ)
          + (inner ℝ (Aeps v) v : ℝ) := by
    intro u v
    rw [map_add]
    simp only [inner_add_left, inner_add_right]
    rw [hAs v u, real_inner_comm v (Aeps u)]
    ring
  -- (eq:srjj-Gexp): the V-level expansion of the sup-convolution
  have hGexpV : ∀ δ > 0, ∃ ρ > 0, ∀ ζ : PiLp 2 (fun _ : Fin N => E), ‖ζ‖ < ρ →
      |SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) (Zh + ζ)
        - SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Zh
        - (inner ℝ Pv0 ζ : ℝ) - A' ζ ζ / 2| ≤ δ * ‖ζ‖ ^ 2 := by
    intro δ hδ
    obtain ⟨ρ, hρ, hexp⟩ := hAUexp δ hδ
    refine ⟨ρ, hρ, fun ζ hζ => ?_⟩
    have h1 := hexp ζ hζ
    have hPin : (inner ℝ Pv0 ζ : ℝ) = (inner ℝ qU ζ : ℝ) + (inner ℝ (Aeps Zh) ζ : ℝ) := by
      rw [hPv0d, inner_add_left]
    have heq : SupConvolution ε
          (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) (Zh + ζ)
        - SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Zh
        - (inner ℝ Pv0 ζ : ℝ) - A' ζ ζ / 2
        = Υ (Zh + ζ) - Υ Zh - (inner ℝ qU ζ : ℝ) - AU ζ ζ / 2 := by
      rw [hSCeq (Zh + ζ), hSCeq Zh, hPin, hA'app, hAexp2 Zh ζ]
      ring
    rw [heq]
    exact h1
  -- the single-coordinate shift, where separability does its work
  have hshift1 : ∀ (j : Fin N) (h : E),
      SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ i, G i (ofLp W i))
          (Zh + iota j h)
        - SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ i, G i (ofLp W i)) Zh
        = SupConvolution ε (G j) (ofLp Zh j + h)
          - SupConvolution ε (G j) (ofLp Zh j) := by
    intro j h
    rw [hsep (Zh + iota j h), hsep Zh, ← Finset.sum_sub_distrib,
      Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
    · have hj : ofLp (Zh + iota j h) j = ofLp Zh j + h := by simp [hiota j h]
      rw [hj]
    · intro i _ hij
      have hi : ofLp (Zh + iota j h) i = ofLp Zh i := by
        simp [hiota j h, hij]
      rw [hi, sub_self]
  -- (eq:srjj-Gjexp): the per-coordinate expansion, with a radius uniform in j
  have hGjexp : ∀ δ > 0, ∃ ρ > 0, ∀ (j : Fin N) (h : E), ‖h‖ < ρ →
      |SupConvolution ε (G j) (ofLp Zh j + h) - SupConvolution ε (G j) (ofLp Zh j)
        - (inner ℝ (ofLp Pv0 j) h : ℝ) - X j h h / 2| ≤ δ * ‖h‖ ^ 2 := by
    intro δ hδ
    obtain ⟨ρ, hρ, hV⟩ := hGexpV δ hδ
    refine ⟨ρ, hρ, fun j h hh => ?_⟩
    have h1 := hV (iota j h) (by rw [hiotan j h]; exact hh)
    rw [hshift1 j h, hiotai j Pv0 h, hiotan j h, ← hXapp j h h] at h1
    exact h1
  -- (the sum of the per-coordinate expansions) = the V-level expansion with the diagonal form
  have hGexpD : ∀ δ > 0, ∃ ρ > 0, ∀ ζ : PiLp 2 (fun _ : Fin N => E), ‖ζ‖ < ρ →
      |SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) (Zh + ζ)
        - SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Zh
        - (inner ℝ Pv0 ζ : ℝ) - (∑ j, X j (ofLp ζ j) (ofLp ζ j)) / 2| ≤ δ * ‖ζ‖ ^ 2 := by
    intro δ hδ
    obtain ⟨ρ, hρ, hj⟩ := hGjexp δ hδ
    refine ⟨ρ, hρ, fun ζ hζ => ?_⟩
    have hsum1 : SupConvolution ε
          (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) (Zh + ζ)
        - SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Zh
        = ∑ j, (SupConvolution ε (G j) (ofLp Zh j + ofLp ζ j)
                - SupConvolution ε (G j) (ofLp Zh j)) := by
      rw [hsep (Zh + ζ), hsep Zh, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hi : ofLp (Zh + ζ) i = ofLp Zh i + ofLp ζ i := by simp
      rw [hi]
    have hsum2 : (inner ℝ Pv0 ζ : ℝ)
        = ∑ j, (inner ℝ (ofLp Pv0 j) (ofLp ζ j) : ℝ) := PiLp.inner_apply _ _
    calc |SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) (Zh + ζ)
          - SupConvolution ε (fun W : PiLp 2 (fun _ : Fin N => E) => ∑ j, G j (ofLp W j)) Zh
          - (inner ℝ Pv0 ζ : ℝ) - (∑ j, X j (ofLp ζ j) (ofLp ζ j)) / 2|
        = |∑ j, ((SupConvolution ε (G j) (ofLp Zh j + ofLp ζ j)
              - SupConvolution ε (G j) (ofLp Zh j))
            - (inner ℝ (ofLp Pv0 j) (ofLp ζ j) : ℝ) - X j (ofLp ζ j) (ofLp ζ j) / 2)| := by
          rw [hsum1, hsum2, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      _ ≤ ∑ j, |(SupConvolution ε (G j) (ofLp Zh j + ofLp ζ j)
              - SupConvolution ε (G j) (ofLp Zh j))
            - (inner ℝ (ofLp Pv0 j) (ofLp ζ j) : ℝ) - X j (ofLp ζ j) (ofLp ζ j) / 2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, δ * ‖ofLp ζ j‖ ^ 2 :=
          Finset.sum_le_sum (fun j _ => hj j (ofLp ζ j) (lt_of_le_of_lt (hco ζ j) hζ))
      _ = δ * ‖ζ‖ ^ 2 := by rw [← Finset.mul_sum, hpyth ζ]
  -- ============ Step 4: the diagonal identity ============
  have hA'scale : ∀ (s : ℝ) (v : PiLp 2 (fun _ : Fin N => E)),
      A' (s • v) (s • v) = s ^ 2 * A' v v := by
    intro s v
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hXscale : ∀ (j : Fin N) (s : ℝ) (a : E), X j (s • a) (s • a) = s ^ 2 * X j a a := by
    intro j s a
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  have hofsmul : ∀ (s : ℝ) (ζ : PiLp 2 (fun _ : Fin N => E)) (j : Fin N),
      ofLp (s • ζ) j = s • ofLp ζ j := fun _ _ _ => rfl
  have hdiag : ∀ ζ : PiLp 2 (fun _ : Fin N => E),
      (∑ j, X j (ofLp ζ j) (ofLp ζ j)) = A' ζ ζ := by
    intro ζ
    rcases eq_or_ne ζ 0 with h0 | h0
    · subst h0; simp
    · have hζp : 0 < ‖ζ‖ := norm_pos_iff.mpr h0
      have hstep : ∀ δ > 0,
          |A' ζ ζ - (∑ j, X j (ofLp ζ j) (ofLp ζ j))| ≤ 4 * δ * ‖ζ‖ ^ 2 := by
        intro δ hδ
        obtain ⟨ρ1, hρ1, hV⟩ := hGexpV δ hδ
        obtain ⟨ρ2, hρ2, hD⟩ := hGexpD δ hδ
        obtain ⟨t, ht0, htn⟩ : ∃ t : ℝ, 0 < t ∧ t * ‖ζ‖ < min ρ1 ρ2 :=
          ⟨min ρ1 ρ2 / (2 * ‖ζ‖), by positivity, by
            have h3 : (0:ℝ) < min ρ1 ρ2 := lt_min hρ1 hρ2
            have h2 : min ρ1 ρ2 / (2 * ‖ζ‖) * ‖ζ‖ = min ρ1 ρ2 / 2 := by field_simp
            rw [h2]; linarith⟩
        have hnt : ‖t • ζ‖ = t * ‖ζ‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have h1 := hV (t • ζ) (by rw [hnt]; exact lt_of_lt_of_le htn (min_le_left _ _))
        have h2 := hD (t • ζ) (by rw [hnt]; exact lt_of_lt_of_le htn (min_le_right _ _))
        rw [hnt, hA'scale t ζ] at h1
        have hDs : (∑ j, X j (ofLp (t • ζ) j) (ofLp (t • ζ) j))
            = t ^ 2 * ∑ j, X j (ofLp ζ j) (ofLp ζ j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun j _ => ?_)
          rw [hofsmul t ζ j, hXscale j t (ofLp ζ j)]
        rw [hnt, hDs] at h2
        have hb1 := abs_le.mp h1
        have hb2 := abs_le.mp h2
        have ht2 : (0:ℝ) < t ^ 2 := by positivity
        have hup : t ^ 2 * (A' ζ ζ - (∑ j, X j (ofLp ζ j) (ofLp ζ j)))
            ≤ t ^ 2 * (4 * δ * ‖ζ‖ ^ 2) := by nlinarith only [hb1.1, hb1.2, hb2.1, hb2.2]
        have hlo : t ^ 2 * (-(4 * δ * ‖ζ‖ ^ 2))
            ≤ t ^ 2 * (A' ζ ζ - (∑ j, X j (ofLp ζ j) (ofLp ζ j))) := by
          nlinarith only [hb1.1, hb1.2, hb2.1, hb2.2]
        rw [abs_le]
        exact ⟨le_of_mul_le_mul_left hlo ht2, le_of_mul_le_mul_left hup ht2⟩
      have hzero : |A' ζ ζ - (∑ j, X j (ofLp ζ j) (ofLp ζ j))| ≤ 0 := by
        refine le_of_forall_pos_le_add (fun η hη => ?_)
        have h1 := hstep (η / (4 * ‖ζ‖ ^ 2)) (by positivity)
        have h2 : 4 * (η / (4 * ‖ζ‖ ^ 2)) * ‖ζ‖ ^ 2 = η := by field_simp
        rw [h2] at h1
        linarith
      have := abs_nonpos_iff.mp hzero
      linarith [this]
  -- the diagonal bound on each X j, from the two-sided bound on AU and on Aeps
  have hXdiagb : ∀ (j : Fin N) (a : E), |X j a a| ≤ (lam + ‖Aeps‖) * ‖a‖ ^ 2 := by
    intro j a
    rw [hXapp j a a, hA'app]
    have h1 := hAUlb (iota j a)
    have h2 := hsecond (iota j a)
    have hi1 : |(inner ℝ (Aeps (iota j a)) (iota j a) : ℝ)|
        ≤ ‖Aeps (iota j a)‖ * ‖iota j a‖ := abs_real_inner_le_norm _ _
    have hi2 : ‖Aeps (iota j a)‖ ≤ ‖Aeps‖ * ‖iota j a‖ := Aeps.le_opNorm _
    rw [hiotan j a] at h1 hi1 hi2
    have h3 : |(inner ℝ (Aeps (iota j a)) (iota j a) : ℝ)| ≤ ‖Aeps‖ * ‖a‖ ^ 2 := by
      nlinarith [norm_nonneg a, norm_nonneg (Aeps (iota j a))]
    have h4 := abs_le.mp h3
    have h5 : 0 ≤ lam * ‖a‖ ^ 2 := by positivity
    rw [abs_le]
    constructor <;> linarith
  have hXnorm : ∀ j : Fin N, ‖X j‖ ≤ 1 / ε + 2 * ‖Aeps‖ := by
    intro j
    have h := SymmetricFormNormFromDiagonal (X j) (lam + ‖Aeps‖)
      (by linarith [norm_nonneg Aeps, hlam0]) (hXsym j) (hXdiagb j)
    rw [hlamd] at h
    linarith
  -- ============ Step 5: transfer to G j ============
  have hjet : ∀ j : Fin N,
      ((ofLp Pv0 j), X j) ∈ Superjet (G j) (ofLp Zh j + ε • ofLp Pv0 j) := by
    intro j
    have hgj : ∀ w : E, G j w ≤ C + ‖w‖ := fun w => by linarith [hGb j w, norm_nonneg w]
    have hpre : ((ofLp Pv0 j), X j) ∈ Superjet (SupConvolution ε (G j)) (ofLp Zh j) := by
      refine ⟨hXsym j, fun ε' hε' => ?_⟩
      obtain ⟨ρ, hρ, hj⟩ := hGjexp ε' hε'
      refine ⟨ρ, hρ, fun h hh => ?_⟩
      have h1 := abs_le.mp (hj j h hh)
      linarith [h1.2]
    exact (SupConvolutionMagic ε C hε (G j) (hGc j) hgj
      (ofLp Zh j) (ofLp Pv0 j) (X j) hpre).2
  -- (J1), second half
  have hPvn : ‖Pv0‖ ≤ δ' + ‖Aeps‖ * R := by
    have h1 : Pv0 = Aeps Zh - Q := by rw [hPv0d, hqU]; abel
    have h2 : ‖Pv0‖ ≤ ‖Aeps Zh‖ + ‖Q‖ := by rw [h1]; exact norm_sub_le _ _
    have h3 : ‖Aeps Zh‖ ≤ ‖Aeps‖ * ‖Zh‖ := Aeps.le_opNorm Zh
    have h4 : ‖Aeps‖ * ‖Zh‖ ≤ ‖Aeps‖ * R :=
      mul_le_mul_of_nonneg_left hZhR.le (norm_nonneg Aeps)
    linarith
  -- (J4)
  have hJ4 : ∀ ζ : PiLp 2 (fun _ : Fin N => E),
      (∑ j, X j (ofLp ζ j) (ofLp ζ j)) ≤ (inner ℝ (Aeps ζ) ζ : ℝ) := by
    intro ζ
    rw [hdiag ζ, hA'app]
    linarith [hsecond ζ]
  exact ⟨Zh, Pv0, X, hZhR, hPvn, hXsym, hXnorm, hjet, hJ4⟩
