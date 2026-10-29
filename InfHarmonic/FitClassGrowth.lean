import InfHarmonic.CenteredGrowth
import InfHarmonic.SubquadraticGrowth
import InfHarmonic.UniformSubquadratic
import InfHarmonic.FrameInvariance
set_option maxHeartbeats 400000
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.3) released from the centering hypothesis: every member of
`A_{m,C₀}` grows at most like `C K L(K)²` on the box of size `K`, measured from
its value at the origin, and therefore has subquadratic spatial growth on
compact time intervals of `ℝ`. -/
theorem FitClassGrowth (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (w : WithLp 2 (F × ℝ) → ℝ)
    (hw : IsFitClass C₀ w) :
    ∃ C : ℝ, 0 < C ∧
      (∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
          ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
          |w z - w 0| ≤ C * K * (1 + Real.log K) ^ 2) ∧
      SubquadraticGrowth (Set.univ : Set ℝ) w := by
  classical
  -- the normalizing fit at the origin and the centered frame change
  obtain ⟨p₁, a₁, hfit⟩ := hw.2 0 1 one_pos
  obtain ⟨W, hW⟩ : ∃ g : WithLp 2 (F × ℝ) → ℝ, g = FrameChange w 0 1 p₁ a₁ := ⟨_, rfl⟩
  have hp1nn : (0 : ℝ) ≤ ‖p₁‖ := norm_nonneg p₁
  have hWform : ∀ z : WithLp 2 (F × ℝ),
      W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))
        = w z - w 0 - inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)
          - (a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2 := by
    intro z
    rw [hW]
    simp only [FrameChange, ofLp_toLp, one_smul, one_mul, div_one, zero_add]
    rw [sub_add_cancel, Prod.mk.eta, toLp_ofLp]
  have hWclass : IsFitClass C₀ W := by
    rw [hW]
    exact (FrameInvariance C₀ w hw 0 1 one_pos p₁ a₁).1
  have hW0 : W 0 = 0 := by
    have h := hWform 0
    simp only [ofLp_zero, zero_smul, sub_zero, inner_zero_right, mul_zero,
      Prod.fst_zero, Prod.snd_zero] at h
    rw [show ((0 : F), (0 : ℝ)) = (0 : F × ℝ) from rfl, toLp_zero] at h
    linarith [h]
  have hWcent : IsCenteredAt C₀ W 0 := by
    refine ⟨hW0, ?_⟩
    have hpt : (0 : WithLp 2 (F × ℝ))
        + toLp 2 ((1 : ℝ) • ((ofLp (0 : WithLp 2 (F × ℝ))).1
          + (ofLp (0 : WithLp 2 (F × ℝ))).2 • p₁), (1 : ℝ) * (ofLp (0 : WithLp 2 (F × ℝ))).2)
        = 0 := by
      simp
    have h := (FrameInvariance C₀ w hw 0 1 one_pos p₁ a₁).2 0 1 p₁ a₁ (by
      rw [hpt, one_mul]
      exact hfit)
    rw [hW]
    simpa using h
  -- the box bound, transported back
  obtain ⟨Cg, hCg0, hCgbd⟩ := CenteredGrowth (F := F) C₀ hC₀
  obtain ⟨CC, hCC⟩ : ∃ C : ℝ, C = Cg * (1 + ‖p₁‖) * (1 + Real.log (1 + ‖p₁‖)) ^ 2
      + ‖p₁‖ * (1 + ‖p₁‖) + (|a₁| + ‖p₁‖ ^ 2 / 2) := ⟨_, rfl⟩
  have hlog1 : (0 : ℝ) ≤ Real.log (1 + ‖p₁‖) := Real.log_nonneg (by linarith)
  have hCC0 : 0 < CC := by
    rw [hCC]
    have h1 : 0 < Cg * (1 + ‖p₁‖) * (1 + Real.log (1 + ‖p₁‖)) ^ 2 := by
      have hL : (0 : ℝ) < 1 + Real.log (1 + ‖p₁‖) := by linarith
      have := mul_pos hCg0 (show (0:ℝ) < 1 + ‖p₁‖ by linarith)
      exact mul_pos this (by positivity)
    have h2 : (0 : ℝ) ≤ ‖p₁‖ * (1 + ‖p₁‖) := by positivity
    have h3 : (0 : ℝ) ≤ |a₁| + ‖p₁‖ ^ 2 / 2 := by positivity
    linarith
  have hbox : ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
      ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
      |w z - w 0| ≤ CC * K * (1 + Real.log K) ^ 2 := by
    intro K hK z hz1 hz2
    have hLK : (1 : ℝ) ≤ 1 + Real.log K := by
      have : (0 : ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
      linarith
    have hLK2 : (1 : ℝ) ≤ (1 + Real.log K) ^ 2 := by nlinarith [hLK]
    obtain ⟨K', hK'⟩ : ∃ K' : ℝ, K' = K * (1 + ‖p₁‖) := ⟨_, rfl⟩
    have hK'ge : K ≤ K' := by
      rw [hK']
      nlinarith [hp1nn, hK]
    have hK'2 : 2 ≤ K' := by linarith
    have hshift : ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ≤ K' := by
      have h1 : ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ≤ ‖(ofLp z).1‖ + ‖(ofLp z).2 • p₁‖ :=
        norm_sub_le _ _
      have h2 : ‖(ofLp z).2 • p₁‖ = |(ofLp z).2| * ‖p₁‖ := by
        rw [norm_smul, Real.norm_eq_abs]
      have h3 : |(ofLp z).2| * ‖p₁‖ ≤ K * ‖p₁‖ := mul_le_mul_of_nonneg_right hz2 hp1nn
      rw [hK']
      nlinarith [h1, h2, h3, hz1]
    have hWbd : |W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))|
        ≤ Cg * K' * (1 + Real.log K') ^ 2 := by
      refine hCgbd W hWclass (Or.inl hWcent) K' hK'2 _ ?_ ?_
      · simpa using hshift
      · simpa using le_trans hz2 hK'ge
    have hlogK' : Real.log K' = Real.log K + Real.log (1 + ‖p₁‖) := by
      rw [hK', Real.log_mul (by linarith) (by linarith)]
    have hLK'le : (1 + Real.log K') ≤ (1 + Real.log (1 + ‖p₁‖)) * (1 + Real.log K) := by
      rw [hlogK']
      nlinarith [hlog1, hLK]
    have hLK'nn : (0 : ℝ) ≤ 1 + Real.log K' := by
      have : (0 : ℝ) ≤ Real.log K' := Real.log_nonneg (by linarith)
      linarith
    have hterm1 : Cg * K' * (1 + Real.log K') ^ 2
        ≤ Cg * (1 + ‖p₁‖) * (1 + Real.log (1 + ‖p₁‖)) ^ 2 * K * (1 + Real.log K) ^ 2 := by
      have hsq : (1 + Real.log K') ^ 2
          ≤ (1 + Real.log (1 + ‖p₁‖)) ^ 2 * (1 + Real.log K) ^ 2 := by
        have := pow_le_pow_left₀ hLK'nn hLK'le 2
        calc (1 + Real.log K') ^ 2
            ≤ ((1 + Real.log (1 + ‖p₁‖)) * (1 + Real.log K)) ^ 2 := this
          _ = (1 + Real.log (1 + ‖p₁‖)) ^ 2 * (1 + Real.log K) ^ 2 := by ring
      have hc : (0 : ℝ) ≤ Cg * K' := by
        have : (0 : ℝ) ≤ K' := by linarith
        positivity
      calc Cg * K' * (1 + Real.log K') ^ 2
          ≤ Cg * K' * ((1 + Real.log (1 + ‖p₁‖)) ^ 2 * (1 + Real.log K) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq hc
        _ = Cg * (1 + ‖p₁‖) * (1 + Real.log (1 + ‖p₁‖)) ^ 2 * K * (1 + Real.log K) ^ 2 := by
            rw [hK']; ring
    have hterm2 : |inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)|
        ≤ ‖p₁‖ * (1 + ‖p₁‖) * K * (1 + Real.log K) ^ 2 := by
      have h1 : |inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)|
          ≤ ‖p₁‖ * ‖(ofLp z).1 - (ofLp z).2 • p₁‖ := by
        simpa [Real.norm_eq_abs] using abs_real_inner_le_norm p₁ ((ofLp z).1 - (ofLp z).2 • p₁)
      have h2 : ‖p₁‖ * ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ≤ ‖p₁‖ * (1 + ‖p₁‖) * K := by
        have h3 := mul_le_mul_of_nonneg_left hshift hp1nn
        rw [hK'] at h3
        calc ‖p₁‖ * ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ≤ ‖p₁‖ * (K * (1 + ‖p₁‖)) := h3
          _ = ‖p₁‖ * (1 + ‖p₁‖) * K := by ring
      have h4 : ‖p₁‖ * (1 + ‖p₁‖) * K
          ≤ ‖p₁‖ * (1 + ‖p₁‖) * K * (1 + Real.log K) ^ 2 := by
        refine le_mul_of_one_le_right ?_ hLK2
        have : (0 : ℝ) ≤ K := by linarith
        positivity
      linarith
    have hterm3 : |(a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2|
        ≤ (|a₁| + ‖p₁‖ ^ 2 / 2) * K * (1 + Real.log K) ^ 2 := by
      have h1 : |(a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2|
          = |a₁ + ‖p₁‖ ^ 2 / 2| * |(ofLp z).2| := abs_mul _ _
      have h2 : |a₁ + ‖p₁‖ ^ 2 / 2| ≤ |a₁| + ‖p₁‖ ^ 2 / 2 := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_of_nonneg (show (0:ℝ) ≤ ‖p₁‖ ^ 2 / 2 by positivity)]
      have h3 : (0 : ℝ) ≤ |a₁| + ‖p₁‖ ^ 2 / 2 := by positivity
      have h5 : |a₁ + ‖p₁‖ ^ 2 / 2| * |(ofLp z).2| ≤ (|a₁| + ‖p₁‖ ^ 2 / 2) * K :=
        mul_le_mul h2 hz2 (abs_nonneg _) h3
      have h6 : (|a₁| + ‖p₁‖ ^ 2 / 2) * K
          ≤ (|a₁| + ‖p₁‖ ^ 2 / 2) * K * (1 + Real.log K) ^ 2 := by
        refine le_mul_of_one_le_right ?_ hLK2
        have : (0 : ℝ) ≤ K := by linarith
        positivity
      rw [h1]
      linarith
    have hinv := hWform z
    have hsplit : |w z - w 0|
        ≤ |W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))|
          + |inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)|
          + |(a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2| := by
      have hrw : w z - w 0
          = W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))
            + inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)
            + (a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2 := by rw [hinv]; ring
      rw [hrw]
      refine le_trans (abs_add_le _ _) ?_
      have := abs_add_le (W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2)))
        (inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁))
      linarith
    rw [hCC]
    have hfin : CC * K * (1 + Real.log K) ^ 2
        = Cg * (1 + ‖p₁‖) * (1 + Real.log (1 + ‖p₁‖)) ^ 2 * K * (1 + Real.log K) ^ 2
          + ‖p₁‖ * (1 + ‖p₁‖) * K * (1 + Real.log K) ^ 2
          + (|a₁| + ‖p₁‖ ^ 2 / 2) * K * (1 + Real.log K) ^ 2 := by
      rw [hCC]; ring
    rw [← hCC, hfin]
    linarith [hsplit, hWbd, hterm1, hterm2, hterm3]
  refine ⟨CC, hCC0, hbox, ?_⟩
  -- subquadratic growth, via the uniform statement for the centered frame change
  intro J _ hJcpt ε hε
  obtain ⟨r, hr⟩ := hJcpt.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨KJ, hKJ⟩ : ∃ KJ : ℝ, KJ = max r 1 := ⟨_, rfl⟩
  have hKJ1 : (1 : ℝ) ≤ KJ := by rw [hKJ]; exact le_max_right _ _
  have hJbd : ∀ σ ∈ J, |σ| ≤ KJ := by
    intro σ hσ
    have h := hr hσ
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    rw [hKJ]
    exact le_trans h (le_max_left _ _)
  obtain ⟨M₁, hM₁0, hM₁⟩ := UniformSubquadratic C₀ hC₀ (0 : WithLp 2 (F × ℝ))
    (Or.inl rfl) J hJcpt (ε / 8) (by positivity)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = |w 0| + ‖p₁‖ * (KJ * ‖p₁‖)
      + (|a₁| + ‖p₁‖ ^ 2 / 2) * KJ := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by
    rw [hA]
    have h1 : (0 : ℝ) ≤ |w 0| := abs_nonneg _
    have h2 : (0 : ℝ) ≤ ‖p₁‖ * (KJ * ‖p₁‖) := by positivity
    have h3 : (0 : ℝ) ≤ (|a₁| + ‖p₁‖ ^ 2 / 2) * KJ := by positivity
    linarith
  refine ⟨max (max 1 (M₁ + KJ * ‖p₁‖)) (max (KJ * ‖p₁‖) (2 * (A + ‖p₁‖) / ε)),
    lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro z hzM hzJ
  have hy1 : (1 : ℝ) ≤ ‖(ofLp z).1‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hzM
  have hy2 : M₁ + KJ * ‖p₁‖ ≤ ‖(ofLp z).1‖ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hzM
  have hy3 : KJ * ‖p₁‖ ≤ ‖(ofLp z).1‖ :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hzM
  have hy4 : 2 * (A + ‖p₁‖) / ε ≤ ‖(ofLp z).1‖ :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hzM
  have hsKJ : |(ofLp z).2| ≤ KJ := hJbd _ hzJ
  have hspn : ‖(ofLp z).2 • p₁‖ ≤ KJ * ‖p₁‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hsKJ hp1nn
  have hshift1 : ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ≤ 2 * ‖(ofLp z).1‖ := by
    have h := norm_sub_le (ofLp z).1 ((ofLp z).2 • p₁)
    linarith [hspn, hy3]
  have hshift2 : M₁ ≤ ‖(ofLp z).1 - (ofLp z).2 • p₁‖ := by
    have h := norm_sub_norm_le (ofLp z).1 ((ofLp z).2 • p₁)
    linarith [hspn, hy2]
  have hWsq : |W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))|
      ≤ ε / 8 * ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ^ 2 := by
    refine hM₁ W hWclass hWcent _ ?_ ?_
    · simpa using hshift2
    · simpa using hzJ
  have hWsq2 : |W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))|
      ≤ ε / 2 * ‖(ofLp z).1‖ ^ 2 := by
    have h1 : ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ^ 2 ≤ (2 * ‖(ofLp z).1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hshift1 2
    have h2 : (2 * ‖(ofLp z).1‖) ^ 2 = 4 * ‖(ofLp z).1‖ ^ 2 := by ring
    rw [h2] at h1
    have h3 : ε / 8 * ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ^ 2
        ≤ ε / 8 * (4 * ‖(ofLp z).1‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : ε / 8 * (4 * ‖(ofLp z).1‖ ^ 2) = ε / 2 * ‖(ofLp z).1‖ ^ 2 := by ring
    linarith [hWsq, h3, h4]
  have hlin : |inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)|
      + |(a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2| + |w 0|
      ≤ A + ‖p₁‖ * ‖(ofLp z).1‖ := by
    have h1 : |inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)|
        ≤ ‖p₁‖ * ‖(ofLp z).1 - (ofLp z).2 • p₁‖ := by
      simpa [Real.norm_eq_abs] using abs_real_inner_le_norm p₁ ((ofLp z).1 - (ofLp z).2 • p₁)
    have h2 : ‖(ofLp z).1 - (ofLp z).2 • p₁‖ ≤ ‖(ofLp z).1‖ + KJ * ‖p₁‖ := by
      have h := norm_sub_le (ofLp z).1 ((ofLp z).2 • p₁)
      linarith [hspn]
    have h2' : ‖p₁‖ * ‖(ofLp z).1 - (ofLp z).2 • p₁‖
        ≤ ‖p₁‖ * (‖(ofLp z).1‖ + KJ * ‖p₁‖) := mul_le_mul_of_nonneg_left h2 hp1nn
    have h3 : |(a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2| ≤ (|a₁| + ‖p₁‖ ^ 2 / 2) * KJ := by
      rw [abs_mul]
      have h4 : |a₁ + ‖p₁‖ ^ 2 / 2| ≤ |a₁| + ‖p₁‖ ^ 2 / 2 := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_of_nonneg (show (0:ℝ) ≤ ‖p₁‖ ^ 2 / 2 by positivity)]
      have h5 : (0 : ℝ) ≤ |a₁| + ‖p₁‖ ^ 2 / 2 := by positivity
      exact mul_le_mul h4 hsKJ (abs_nonneg _) h5
    rw [hA]
    nlinarith [h1, h2', h3]
  have hAy : A + ‖p₁‖ * ‖(ofLp z).1‖ ≤ ε / 2 * ‖(ofLp z).1‖ ^ 2 := by
    have h1 : A + ‖p₁‖ * ‖(ofLp z).1‖ ≤ (A + ‖p₁‖) * ‖(ofLp z).1‖ := by
      nlinarith [hA0, hy1]
    have h2 : 2 * (A + ‖p₁‖) ≤ ε * ‖(ofLp z).1‖ := by
      rw [div_le_iff₀ hε] at hy4
      linarith
    nlinarith [h1, h2, hy1]
  have hinv := hWform z
  have hfinal : |w z|
      ≤ |W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))|
        + |inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)|
        + |(a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2| + |w 0| := by
    have hrw : w z = W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))
        + inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)
        + (a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2 + w 0 := by rw [hinv]; ring
    rw [hrw]
    refine le_trans (abs_add_le _ _) ?_
    have ha := abs_add_le (W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2))
      + inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁)) ((a₁ + ‖p₁‖ ^ 2 / 2) * (ofLp z).2)
    have hb := abs_add_le (W (toLp 2 ((ofLp z).1 - (ofLp z).2 • p₁, (ofLp z).2)))
      (inner ℝ p₁ ((ofLp z).1 - (ofLp z).2 • p₁))
    linarith
  linarith [hfinal, hWsq2, hlin, hAy]
