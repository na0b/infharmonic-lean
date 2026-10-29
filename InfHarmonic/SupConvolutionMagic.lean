module

public import InfHarmonic.SupConvolutionSemiconvex
public import InfHarmonic.Superjet

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The magic property of the sup-convolution: a superjet of `φ^ε` at `z` locates
the maximizer at `z + ε • p` and is a superjet of `φ` there. -/
theorem SupConvolutionMagic (ε C : ℝ) (hε : 0 < ε) (φ : E → ℝ) (hφc : Continuous φ)
    (hφ : ∀ w : E, φ w ≤ C + ‖w‖) (z p : E) (X : E →L[ℝ] E →L[ℝ] ℝ)
    (hpX : (p, X) ∈ Superjet (SupConvolution ε φ) z) :
    SupConvolution ε φ z = φ (z + ε • p) - ε * ‖p‖ ^ 2 / 2 ∧
      (p, X) ∈ Superjet φ (z + ε • p) := by
  obtain ⟨hbdd, -, -⟩ := SupConvolutionSemiconvex ε C hε φ hφ
  have h2e : (0:ℝ) < 2 * ε := by linarith
  -- Handshake B: the `t ↓ 0` step, with no limit.
  have hsmall : ∀ c d K δ : ℝ, 0 < δ → (∀ t : ℝ, 0 < t → t < δ → c ≤ d + t * K) → c ≤ d := by
    intro c d K δ hδ H
    refine le_of_forall_pos_le_add ?_
    intro η hη
    have hK : (0:ℝ) < |K| + 1 := by positivity
    set t : ℝ := min (δ / 2) (η / (|K| + 1)) with ht
    have ht0 : 0 < t := lt_min (by linarith) (by positivity)
    have htδ : t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have h1 : t ≤ η / (|K| + 1) := min_le_right _ _
    have h2 : t * K ≤ t * |K| := mul_le_mul_of_nonneg_left (le_abs_self K) ht0.le
    have h3 : t * (|K| + 1) ≤ η := by rw [← le_div_iff₀ hK]; exact h1
    nlinarith [H t ht0 htδ, h2, h3, ht0, abs_nonneg K]
  -- (eq:scm-ub)
  have hub : ∀ y w : E, φ w - ‖y - w‖ ^ 2 / (2 * ε) ≤ SupConvolution ε φ y := by
    intro y w
    have := le_csSup (hbdd y) (Set.mem_range_self
      (f := fun w : E => φ w - ‖y - w‖ ^ 2 / (2 * ε)) w)
    simpa [SupConvolution] using this
  -- Step 1: the supremum at `z` is attained.
  obtain ⟨ŵ, hsup⟩ : ∃ ŵ : E, SupConvolution ε φ z = φ ŵ - ‖z - ŵ‖ ^ 2 / (2 * ε) := by
    set Θ : E → ℝ := fun w => φ w - ‖z - w‖ ^ 2 / (2 * ε) with hΘdef
    have hΘc : Continuous Θ := by
      have : Continuous fun w : E => ‖z - w‖ ^ 2 / (2 * ε) :=
        (((continuous_const.sub continuous_id).norm).pow 2).div_const _
      exact hφc.sub this
    have hfar : ∀ᶠ w in Filter.cocompact E, Θ w ≤ Θ z := by
      refine Metric.mem_cocompact_of_closedBall_compl_subset z
        ⟨2 * ε + |C + ‖z‖ - φ z|, ?_⟩
      intro w hw
      have hs : 2 * ε + |C + ‖z‖ - φ z| < ‖z - w‖ := by
        have hw' := hw
        simp only [mem_compl_iff, Metric.mem_closedBall, not_le, dist_eq_norm] at hw'
        calc 2 * ε + |C + ‖z‖ - φ z| < ‖w - z‖ := hw'
          _ = ‖z - w‖ := by rw [norm_sub_rev]
      have htri : ‖w‖ ≤ ‖z‖ + ‖z - w‖ := by
        have hrw : ‖w‖ = ‖z - (z - w)‖ := by rw [sub_sub_cancel]
        rw [hrw]; exact norm_sub_le z (z - w)
      have hd : ‖z - w‖ ^ 2 / (2 * ε) * (2 * ε) = ‖z - w‖ ^ 2 :=
        div_mul_cancel₀ _ (ne_of_gt h2e)
      have hA : C + ‖z‖ - φ z ≤ |C + ‖z‖ - φ z| := le_abs_self _
      have hA0 : (0:ℝ) ≤ |C + ‖z‖ - φ z| := abs_nonneg _
      have hzz : ‖z - z‖ ^ 2 / (2 * ε) = 0 := by simp
      simp only [hΘdef, Set.mem_ofPred_eq, hzz, sub_zero]
      nlinarith [hφ w, htri, hd, hs, hA, hA0, hε]
    obtain ⟨ŵ, hmax⟩ := hΘc.exists_forall_ge' z hfar
    refine ⟨ŵ, le_antisymm ?_ ?_⟩
    · rw [SupConvolution]
      exact csSup_le (Set.range_nonempty _) (by rintro v ⟨w, rfl⟩; exact hmax w)
    · exact hub z ŵ
  -- division-free forms of the two facts Step 3 needs
  have hub' : ∀ y w : E, 2 * ε * φ w - ‖y - w‖ ^ 2 ≤ 2 * ε * SupConvolution ε φ y := by
    intro y w
    have h0 := mul_le_mul_of_nonneg_left (hub y w) h2e.le
    have hid : 2 * ε * (φ w - ‖y - w‖ ^ 2 / (2 * ε)) = 2 * ε * φ w - ‖y - w‖ ^ 2 := by
      field_simp
    rw [hid] at h0
    exact h0
  have hsup' : 2 * ε * SupConvolution ε φ z = 2 * ε * φ ŵ - ‖z - ŵ‖ ^ 2 := by
    rw [hsup]; field_simp
  -- Step 2: a one-sided comparison of increments (eq:scm-increment)
  have hincr : ∀ h : E, φ (ŵ + h) - φ ŵ
      ≤ SupConvolution ε φ (z + h) - SupConvolution ε φ z := by
    intro h
    have h1 := hub (z + h) (ŵ + h)
    have h2 : z + h - (ŵ + h) = z - ŵ := by abel
    rw [h2] at h1
    linarith [hsup]
  -- Step 3, lower bound (eq:scm-lower), division-free
  have hlow : ∀ h : E, -(2 * inner ℝ (z - ŵ) h + ‖h‖ ^ 2)
      ≤ 2 * ε * (SupConvolution ε φ (z + h) - SupConvolution ε φ z) := by
    intro h
    have h1 := hub' (z + h) ŵ
    have h2 : z + h - ŵ = (z - ŵ) + h := by abel
    rw [h2, norm_add_sq_real (z - ŵ) h] at h1
    linarith [h1, hsup']
  -- Step 3: `0 ≤ ⟪(z - ŵ) + ε • p, v⟫` for EVERY `v` (no normalization needed)
  have hkey : ∀ v : E, 0 ≤ inner ℝ ((z - ŵ) + ε • p) v := by
    intro v
    obtain ⟨δ, hδ, hb⟩ := hpX.2 1 one_pos
    have hv1 : (0:ℝ) < ‖v‖ + 1 := by positivity
    refine hsmall 0 (inner ℝ ((z - ŵ) + ε • p) v)
      (‖v‖ ^ 2 / 2 + ε * X v v / 2 + ε * ‖v‖ ^ 2) (δ / (‖v‖ + 1)) (by positivity) ?_
    intro t ht0 htd
    have hnv : ‖t • v‖ < δ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      have := (lt_div_iff₀ hv1).mp htd
      nlinarith [norm_nonneg v, ht0]
    have e1 : inner ℝ (z - ŵ) (t • v) = t * inner ℝ (z - ŵ) v :=
      real_inner_smul_right (z - ŵ) v t
    have e2 : ‖t • v‖ ^ 2 = t ^ 2 * ‖v‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]; ring
    have e3 : inner ℝ p (t • v) = t * inner ℝ p v := real_inner_smul_right p v t
    have e4 : X (t • v) (t • v) = t ^ 2 * X v v := by
      simp only [map_smul, smul_apply, smul_eq_mul]; ring
    have e5 : inner ℝ ((z - ŵ) + ε • p) v = inner ℝ (z - ŵ) v + ε * inner ℝ p v := by
      rw [inner_add_left, real_inner_smul_left]
    have h1 := hlow (t • v)
    have h2 := hb (t • v) hnv
    rw [e1, e2] at h1
    rw [e3, e2, e4] at h2
    have h2e' := mul_le_mul_of_nonneg_left h2 h2e.le
    rw [e5]
    by_contra hcon
    rw [not_le] at hcon
    linarith [h1, h2e', mul_pos ht0 (neg_pos.mpr hcon)]
  -- hence `ŵ = z + ε • p`
  have hu0 : (z - ŵ) + ε • p = 0 := by
    have h1 := hkey (-((z - ŵ) + ε • p))
    rw [inner_neg_right, real_inner_self_eq_norm_sq] at h1
    have h2 : ‖(z - ŵ) + ε • p‖ = 0 := by
      nlinarith [norm_nonneg ((z - ŵ) + ε • p), h1]
    exact norm_eq_zero.mp h2
  have hŵ : ŵ = z + ε • p := by
    have hid : (z + ε • p) - ŵ = (z - ŵ) + ε • p := by abel
    have h0 : (z + ε • p) - ŵ = 0 := by rw [hid, hu0]
    exact (eq_of_sub_eq_zero h0).symm
  have hnorm : ‖z - ŵ‖ = ε * ‖p‖ := by
    have hzw : z - ŵ = -(ε • p) := by rw [hŵ]; abel
    rw [hzw, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
  have heq1 : φ ŵ - ‖z - ŵ‖ ^ 2 / (2 * ε) = φ (z + ε • p) - ε * ‖p‖ ^ 2 / 2 := by
    rw [hnorm, hŵ]; field_simp
  -- Step 4: the jet transfers
  refine ⟨hsup.trans heq1, ?_⟩
  rw [← hŵ]
  refine ⟨hpX.1, ?_⟩
  intro ε' hε'
  obtain ⟨δ', hδ', hb'⟩ := hpX.2 ε' hε'
  refine ⟨δ', hδ', ?_⟩
  intro h hh
  show φ (ŵ + h) ≤ φ ŵ + inner ℝ p h + X h h / 2 + ε' * ‖h‖ ^ 2
  have h1 := hincr h
  have h2 := hb' h hh
  linarith
