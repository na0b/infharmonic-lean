import InfHarmonic.Preamble
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A real convex function on an open convex set has a subgradient at every
point of that set. -/
theorem ConvexSubgradientExists (Ω : Set E) (hΩo : IsOpen Ω)
    (ψ : E → ℝ) (hψ : ConvexOn ℝ Ω ψ) (z : E) (hz : z ∈ Ω) :
    ∃ q : E, ∀ x ∈ Ω, ψ z + inner ℝ q (x - z) ≤ ψ x := by
  -- Step 1: a ball `B(z,2ρ) ⊆ Ω` on which `ψ` is `L`-Lipschitz (preamble)
  have hcont : ContinuousOn ψ Ω := hψ.continuousOn hΩo
  obtain ⟨L, U, hU, hLU⟩ := hψ.locallyLipschitzOn hΩo hz
  rw [hΩo.nhdsWithin_eq hz] at hU
  obtain ⟨ε₁, hε₁, hb₁⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨ε₂, hε₂, hb₂⟩ := Metric.mem_nhds_iff.1 (hΩo.mem_nhds hz)
  obtain ⟨ρ, hρ, hsubΩ, hLip⟩ :
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball z (2 * ρ) ⊆ Ω ∧
        LipschitzOnWith L ψ (Metric.ball z (2 * ρ)) := by
    have h1 : min ε₁ ε₂ ≤ ε₁ := min_le_left _ _
    have h2 : min ε₁ ε₂ ≤ ε₂ := min_le_right _ _
    have hm : 0 < min ε₁ ε₂ := lt_min hε₁ hε₂
    refine ⟨min ε₁ ε₂ / 3, by positivity, ?_, ?_⟩
    · exact fun x hx => hb₂ (Metric.ball_subset_ball (by linarith) hx)
    · exact hLU.mono (fun x hx => hb₁ (Metric.ball_subset_ball (by linarith) hx))
  -- Step 3: at a differentiability point the gradient is a subgradient
  have hsub : ∀ w ∈ Ω, DifferentiableAt ℝ ψ w →
      ∀ x ∈ Ω, ψ w + inner ℝ (gradient ψ w) (x - w) ≤ ψ x := by
    intro w hw hdw x hx
    have hline : HasDerivAt (fun s : ℝ => w + s • (x - w)) (x - w) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (x - w)).const_add w
    have hcomp : HasDerivAt (fun s : ℝ => ψ (w + s • (x - w)))
        (fderiv ℝ ψ w (x - w)) 0 := by
      have hfd : HasFDerivAt ψ (fderiv ℝ ψ w) (w + (0:ℝ) • (x - w)) := by
        simpa using hdw.hasFDerivAt
      exact hfd.comp_hasDerivAt 0 hline
    have hquot : ∀ s : ℝ, 0 < s → s < 1 →
        (ψ (w + s • (x - w)) - ψ w) / s ≤ ψ x - ψ w := by
      intro s hs hs1
      have hmem := hψ.2 hw hx (by linarith : (0:ℝ) ≤ 1 - s) hs.le (by ring)
      have heq : (1 - s) • w + s • x = w + s • (x - w) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [heq] at hmem
      simp only [smul_eq_mul] at hmem
      rw [div_le_iff₀ hs]
      nlinarith [hmem]
    have hmono : nhdsWithin (0:ℝ) (Set.Ioi 0) ≤ nhdsWithin (0:ℝ) {(0:ℝ)}ᶜ :=
      nhdsWithin_mono _ (fun s hs => ne_of_gt hs)
    have htend := hcomp.tendsto_slope.mono_left hmono
    have hbound : fderiv ℝ ψ w (x - w) ≤ ψ x - ψ w := by
      refine le_of_tendsto htend ?_
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with s hs
      have hsl : slope (fun s : ℝ => ψ (w + s • (x - w))) 0 s
          = (ψ (w + s • (x - w)) - ψ w) / s := by
        simp [slope_def_field, zero_smul]
      rw [hsl]
      exact hquot s hs.1 hs.2
    rw [inner_gradient_left]
    linarith [hbound]
  -- Step 2: differentiability points accumulating at `z` (Rademacher, preamble)
  have hnear : ∀ n : ℕ, ∃ v : E, ‖v - z‖ < ρ / ((n:ℝ) + 1) ∧
      v ∈ Metric.ball z (2 * ρ) ∧ DifferentiableAt ℝ ψ v := by
    intro n
    borelize E
    set μ : MeasureTheory.Measure E := MeasureTheory.Measure.addHaar with hμ
    have hrpos : 0 < ρ / ((n:ℝ) + 1) := by positivity
    have hrle : ρ / ((n:ℝ) + 1) ≤ 2 * ρ := by
      have h1 : ρ / ((n:ℝ) + 1) ≤ ρ := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      linarith
    have hae : ∀ᵐ x ∂μ, x ∈ Metric.ball z (2 * ρ) → DifferentiableAt ℝ ψ x := by
      filter_upwards [hLip.ae_differentiableWithinAt_of_mem (μ := μ)] with x hx hxb
      exact (hx hxb).differentiableAt (Metric.isOpen_ball.mem_nhds hxb)
    set N : Set E := {x | x ∈ Metric.ball z (2 * ρ) ∧ ¬ DifferentiableAt ℝ ψ x} with hN
    have hNnull : μ N = 0 := by
      have heq : {x : E | ¬ (x ∈ Metric.ball z (2 * ρ) → DifferentiableAt ℝ ψ x)} = N := by
        ext x; exact Classical.not_imp
      rw [← heq]; exact hae
    have hpos : 0 < μ (Metric.ball z (ρ / ((n:ℝ) + 1))) :=
      Metric.measure_ball_pos μ z hrpos
    obtain ⟨v, hv⟩ : (Metric.ball z (ρ / ((n:ℝ) + 1)) \ N).Nonempty := by
      refine MeasureTheory.nonempty_of_measure_ne_zero (μ := μ) ?_
      rw [MeasureTheory.measure_sdiff_null hNnull]; exact ne_of_gt hpos
    have hvb : v ∈ Metric.ball z (2 * ρ) := Metric.ball_subset_ball hrle hv.1
    refine ⟨v, ?_, hvb, ?_⟩
    · simpa [Metric.mem_ball, dist_eq_norm] using hv.1
    · by_contra hnd; exact hv.2 ⟨hvb, hnd⟩
  choose w hwnear hwball hwdiff using hnear
  -- Step 4: the gradients at the `w n` are bounded by `L`
  have hqbound : ∀ n : ℕ, ‖gradient ψ (w n)‖ ≤ (L:ℝ) := by
    intro n
    rcases eq_or_lt_of_le (norm_nonneg (gradient ψ (w n))) with h0 | hqpos
    · rw [← h0]; exact L.coe_nonneg
    · have hspos : 0 < ρ / (‖gradient ψ (w n)‖ + 1) := by positivity
      have hsq : ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖ < ρ := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [hqpos]
      have hxmem : w n + (ρ / (‖gradient ψ (w n)‖ + 1)) • gradient ψ (w n)
          ∈ Metric.ball z (2 * ρ) := by
        have hrw : w n + (ρ / (‖gradient ψ (w n)‖ + 1)) • gradient ψ (w n) - z
            = (w n - z) + (ρ / (‖gradient ψ (w n)‖ + 1)) • gradient ψ (w n) := by abel
        have h1 : ‖w n + (ρ / (‖gradient ψ (w n)‖ + 1)) • gradient ψ (w n) - z‖
            ≤ ‖w n - z‖ + ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖ := by
          rw [hrw]
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
        have h2 := hwnear n
        have h3 : ρ / ((n:ℝ) + 1) ≤ ρ := by
          rw [div_le_iff₀ (by positivity)]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]
        simp only [Metric.mem_ball, dist_eq_norm]
        linarith
      have hsg := hsub (w n) (hsubΩ (hwball n)) (hwdiff n) _ (hsubΩ hxmem)
      have hinn : inner ℝ (gradient ψ (w n))
          (w n + (ρ / (‖gradient ψ (w n)‖ + 1)) • gradient ψ (w n) - w n)
          = ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖ ^ 2 := by
        rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      rw [hinn] at hsg
      have hlip := hLip.dist_le_mul _ hxmem _ (hwball n)
      rw [Real.dist_eq, dist_eq_norm] at hlip
      have hnormsub : ‖w n + (ρ / (‖gradient ψ (w n)‖ + 1)) • gradient ψ (w n) - w n‖
          = ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖ := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hspos]
      rw [hnormsub] at hlip
      have habs := abs_le.1 hlip
      have hkey : ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖ ^ 2
          ≤ (L:ℝ) * (ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖) := by
        linarith [habs.2, hsg]
      -- divide by the single positive product, supplied explicitly
      have hprod : 0 < ρ / (‖gradient ψ (w n)‖ + 1) * ‖gradient ψ (w n)‖ :=
        mul_pos hspos hqpos
      by_contra hcon
      replace hcon : (L:ℝ) < ‖gradient ψ (w n)‖ := not_le.mp hcon
      nlinarith [hkey, mul_pos hprod (sub_pos.mpr hcon)]
  -- Step 5: Bolzano-Weierstrass and the limit (preamble)
  have hqmem : ∀ n : ℕ, gradient ψ (w n) ∈ Metric.closedBall (0:E) (L:ℝ) := by
    intro n; simpa [Metric.mem_closedBall, dist_zero_right] using hqbound n
  obtain ⟨q, -, φ, hφ, hφtend⟩ :=
    (isCompact_closedBall (0:E) (L:ℝ)).tendsto_subseq hqmem
  have hwtend0 : Filter.Tendsto w Filter.atTop (nhds z) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt (ρ / ε)
    refine ⟨N, fun n hn => ?_⟩
    have hcast : (N:ℝ) ≤ (n:ℝ) := Nat.cast_le.2 hn
    have h1 : ρ / ε < (n:ℝ) + 1 := by linarith
    have h2 : ρ / ((n:ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hε] at h1
      linarith
    have h3 := hwnear n
    simp only [dist_eq_norm]
    linarith
  have hwtend : Filter.Tendsto (fun i => w (φ i)) Filter.atTop (nhds z) :=
    hwtend0.comp hφ.tendsto_atTop
  refine ⟨q, fun x hx => ?_⟩
  have hψtend : Filter.Tendsto (fun i => ψ (w (φ i))) Filter.atTop (nhds (ψ z)) :=
    ((hcont.continuousAt (hΩo.mem_nhds hz)).tendsto).comp hwtend
  have hinner : Filter.Tendsto
      (fun i => inner ℝ (gradient ψ (w (φ i))) (x - w (φ i)))
      Filter.atTop (nhds (inner ℝ q (x - z))) :=
    Filter.Tendsto.inner hφtend (tendsto_const_nhds.sub hwtend)
  refine le_of_tendsto (hψtend.add hinner) ?_
  filter_upwards with i
  exact hsub (w (φ i)) (hsubΩ (hwball (φ i))) (hwdiff (φ i)) x hx
