module

public import InfHarmonic.SemiconvexOn
public import InfHarmonic.ConvexSubgradientExists
public import InfHarmonic.MaxMultiplierPinsSubgradient

@[expose] public section
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Quantitative Lipschitz dependence of the multiplier on the point: if `z₁` and `z₂`
are nearby interior maximum points of the linear perturbations `φ + ⟪p₁, ·⟫` and
`φ + ⟪p₂, ·⟫` of a `lam`-semiconvex function over a common set `A`, then
`‖p₁ - p₂‖ ≤ 2 lam ‖z₁ - z₂‖`. -/
theorem SemiconvexMultiplierLipschitz (lam : ℝ) (hlam : 0 < lam) (Ω : Set E) (hΩo : IsOpen Ω)
    (φ : E → ℝ) (hφ : SemiconvexOn lam Ω φ) (A : Set E)
    (z₁ z₂ p₁ p₂ : E) (η : ℝ) (hη : 0 < η)
    (hb₁ : ball z₁ η ⊆ A ∩ Ω) (hb₂ : ball z₂ η ⊆ A ∩ Ω)
    (hz : ‖z₁ - z₂‖ < η)
    (hm₁ : ∀ w ∈ A, φ w + inner ℝ p₁ w ≤ φ z₁ + inner ℝ p₁ z₁)
    (hm₂ : ∀ w ∈ A, φ w + inner ℝ p₂ w ≤ φ z₂ + inner ℝ p₂ z₂) :
    ‖p₁ - p₂‖ ≤ 2 * lam * ‖z₁ - z₂‖ := by
  set ψ : E → ℝ := fun w => φ w + lam * ‖w‖ ^ 2 / 2 with hψ
  have hψc : ConvexOn ℝ Ω ψ := hφ
  have hz₂Ω : z₂ ∈ Ω := (hb₂ (mem_ball_self hη)).2
  -- the subgradient of ψ at z₂ is pinned to lam • z₂ - p₂
  obtain ⟨s, hs⟩ := ConvexSubgradientExists Ω hΩo ψ hψc z₂ hz₂Ω
  have hs' : ∀ w ∈ Ω, φ z₂ + lam * ‖z₂‖ ^ 2 / 2 + inner ℝ s (w - z₂)
      ≤ φ w + lam * ‖w‖ ^ 2 / 2 := hs
  have hspin : s = lam • z₂ - p₂ :=
    MaxMultiplierPinsSubgradient lam φ A Ω z₂ p₂ s η hη hb₂ hm₂ hs'
  have hSG : ∀ w ∈ Ω, φ z₂ + lam * ‖z₂‖ ^ 2 / 2 + inner ℝ (lam • z₂ - p₂) (w - z₂)
      ≤ φ w + lam * ‖w‖ ^ 2 / 2 := by rw [← hspin]; exact hs'
  -- the quadratic identity, used twice
  have hid : ∀ u v : E, lam * ‖u‖ ^ 2 / 2 - lam * ‖v‖ ^ 2 / 2
      = lam * inner ℝ v (u - v) + lam * ‖u - v‖ ^ 2 / 2 := by
    intro u v
    have h := norm_add_sq_real (u - v) v
    rw [sub_add_cancel] at h
    rw [h, real_inner_comm (u - v) v]
    ring
  -- z₁ lies in A ∩ Ω
  have hz₁mem : z₁ ∈ A ∩ Ω := hb₂ (by simpa [mem_ball, dist_eq_norm] using hz)
  rcases eq_or_lt_of_le (norm_nonneg (z₁ - z₂)) with hD0 | hDpos
  · -- z₁ = z₂: the multiplier is unique, so p₁ = p₂
    have hzeq : z₁ = z₂ := by
      have : z₁ - z₂ = 0 := by
        rw [← norm_eq_zero]; exact hD0.symm
      linear_combination (norm := module) this
    have hs1 : ∀ w ∈ Ω, φ z₁ + lam * ‖z₁‖ ^ 2 / 2 + inner ℝ s (w - z₁)
        ≤ φ w + lam * ‖w‖ ^ 2 / 2 := by rw [hzeq]; exact hs'
    have hb₁' : ball z₁ η ⊆ A ∩ Ω := hb₁
    have hspin1 : s = lam • z₁ - p₁ :=
      MaxMultiplierPinsSubgradient lam φ A Ω z₁ p₁ s η hη hb₁' hm₁ hs1
    have : p₁ = p₂ := by
      rw [hzeq] at hspin1
      have := hspin1.symm.trans hspin
      linear_combination (norm := module) -this
    rw [this, sub_self, norm_zero]
    positivity
  · -- the main case
    set D : ℝ := ‖z₁ - z₂‖ with hDdef
    set σ : ℝ := φ z₁ + lam * ‖z₁‖ ^ 2 / 2 - (φ z₂ + lam * ‖z₂‖ ^ 2 / 2)
      - inner ℝ (lam • z₂ - p₂) (z₁ - z₂) with hσ
    have hσ0 : 0 ≤ σ := by
      have := hSG z₁ hz₁mem.2
      simp only [hσ]
      linarith
    have hσu : σ ≤ lam * D ^ 2 / 2 := by
      have h1 := hm₂ z₁ hz₁mem.1
      have h2 : (inner ℝ (lam • z₂ - p₂) (z₁ - z₂) : ℝ)
          = lam * inner ℝ z₂ (z₁ - z₂) - inner ℝ p₂ (z₁ - z₂) := by
        simp only [inner_sub_left, real_inner_smul_left]
      have h3 : (inner ℝ p₂ z₁ : ℝ) - inner ℝ p₂ z₂ = inner ℝ p₂ (z₁ - z₂) := by
        rw [inner_sub_right]
      have h4 := hid z₁ z₂
      simp only [hσ, hDdef]
      linarith
    set Δ : E := (p₁ - p₂) - lam • (z₁ - z₂) with hΔ
    -- the key one-sided estimate around z₁
    have hkey : ∀ w ∈ ball z₁ η, inner ℝ Δ (w - z₁) ≤ σ + lam * ‖w - z₁‖ ^ 2 / 2 := by
      intro w hw
      have hwA : w ∈ A := (hb₁ hw).1
      have hwΩ : w ∈ Ω := (hb₁ hw).2
      have h1 := hm₁ w hwA
      have h2 := hSG w hwΩ
      have h3 : (inner ℝ p₁ w : ℝ) - inner ℝ p₁ z₁ = inner ℝ p₁ (w - z₁) := by
        rw [inner_sub_right]
      have h4 := hid w z₁
      have h5 : (inner ℝ (lam • z₂ - p₂) (w - z₂) : ℝ)
          - inner ℝ (lam • z₂ - p₂) (z₁ - z₂)
          = inner ℝ (lam • z₂ - p₂) (w - z₁) := by
        rw [← inner_sub_right]
        congr 1
        abel
      have h6 : (inner ℝ Δ (w - z₁) : ℝ)
          = inner ℝ (lam • z₂ - p₂) (w - z₁) - lam * inner ℝ z₁ (w - z₁)
            + inner ℝ p₁ (w - z₁) := by
        simp only [hΔ, inner_sub_left, real_inner_smul_left]
        ring
      simp only [hσ]
      linarith
    -- test in the direction Δ with step D
    have hΔb : ‖Δ‖ ≤ lam * D := by
      rcases eq_or_ne Δ 0 with h0 | hne
      · rw [h0]; simp; positivity
      · have hnp : 0 < ‖Δ‖ := norm_pos_iff.mpr hne
        set w : E := z₁ + (D / ‖Δ‖) • Δ with hw
        have hwz : w - z₁ = (D / ‖Δ‖) • Δ := by rw [hw]; abel
        have hcoef : 0 < D / ‖Δ‖ := by positivity
        have hne' : ‖Δ‖ ≠ 0 := ne_of_gt hnp
        have hnw : ‖w - z₁‖ = D := by
          rw [hwz, norm_smul, Real.norm_eq_abs, abs_of_pos hcoef]
          field_simp
        have hwmem : w ∈ ball z₁ η := by
          simp only [mem_ball, dist_eq_norm, hnw]
          exact hz
        have hnw2 : ‖(D / ‖Δ‖) • Δ‖ = D := by rw [← hwz]; exact hnw
        have hstep := hkey w hwmem
        rw [hwz, real_inner_smul_right, real_inner_self_eq_norm_sq, hnw2] at hstep
        have hval : D / ‖Δ‖ * ‖Δ‖ ^ 2 = D * ‖Δ‖ := by field_simp
        rw [hval] at hstep
        -- D‖Δ‖ ≤ σ + lam D²/2 ≤ lam D²
        have h7 : D * ‖Δ‖ ≤ lam * D ^ 2 := by linarith
        have hDp : 0 < D := hDpos
        refine le_of_mul_le_mul_left ?_ hDp
        calc D * ‖Δ‖ ≤ lam * D ^ 2 := h7
          _ = D * (lam * D) := by ring
    have hfin : ‖p₁ - p₂‖ ≤ ‖Δ‖ + lam * D := by
      have heq : p₁ - p₂ = Δ + lam • (z₁ - z₂) := by rw [hΔ]; abel
      have h1 : ‖Δ + lam • (z₁ - z₂)‖ ≤ ‖Δ‖ + ‖lam • (z₁ - z₂)‖ := norm_add_le _ _
      have h2 : ‖lam • (z₁ - z₂)‖ = lam * D := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam, hDdef]
      rw [heq]
      linarith
    linarith
