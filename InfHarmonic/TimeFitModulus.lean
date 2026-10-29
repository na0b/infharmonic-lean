module

public import InfHarmonic.FitParamBound

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.6): the time modulus of continuity of a centered member of
`A_{m,C₀}` on the box of size `K`, with its squared logarithmic factor. -/
theorem TimeFitModulus (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      (IsCenteredAt C₀ v 0 ∨ IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ)))) →
      ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
        ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
        ∀ τ : ℝ, 0 < |τ| → |τ| ≤ 1 / 2 →
          |v (z + toLp 2 ((0 : F), τ)) - v z|
            ≤ C * |τ| * ((1 + Real.log K) + abs (Real.log (abs τ))) ^ 2 := by
  have _unused_fd : FiniteDimensional ℝ F := inferInstance
  have hC₀0 : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  -- the self-referential choice of `A'`, lifted verbatim from `FitParamBound`:
  -- elementary because `Real.log x ≤ 2 * Real.sqrt x`.
  have hlogsqrt : ∀ x : ℝ, 0 < x → Real.log x ≤ 2 * Real.sqrt x := by
    intro x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
    have h2 : Real.log x = Real.log (Real.sqrt x) + Real.log (Real.sqrt x) := by
      rw [← Real.log_mul (ne_of_gt hs) (ne_of_gt hs), Real.mul_self_sqrt hx.le]
    rw [h2]; linarith
  have hAexists : ∀ α β : ℝ, 0 ≤ α → 0 ≤ β →
      ∃ A : ℝ, 8 ≤ A ∧ α + β * Real.log A ≤ A := by
    intro α β hα0 hβ0
    refine ⟨max 8 (max (2 * α) (16 * β ^ 2)), le_max_left _ _, ?_⟩
    have hA8 : (8:ℝ) ≤ max 8 (max (2 * α) (16 * β ^ 2)) := le_max_left _ _
    have hApos : (0:ℝ) < max 8 (max (2 * α) (16 * β ^ 2)) := by linarith
    have hα : 2 * α ≤ max 8 (max (2 * α) (16 * β ^ 2)) :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have hβsq : 16 * β ^ 2 ≤ max 8 (max (2 * α) (16 * β ^ 2)) :=
      le_trans (le_max_right _ _) (le_max_right _ _)
    have hsq : 4 * β ≤ Real.sqrt (max 8 (max (2 * α) (16 * β ^ 2))) := by
      have h1 : Real.sqrt ((4 * β) ^ 2) ≤ Real.sqrt (max 8 (max (2 * α) (16 * β ^ 2))) :=
        Real.sqrt_le_sqrt (by nlinarith [hβsq])
      rwa [Real.sqrt_sq (by positivity)] at h1
    have hs2 : Real.sqrt (max 8 (max (2 * α) (16 * β ^ 2)))
        * Real.sqrt (max 8 (max (2 * α) (16 * β ^ 2)))
        = max 8 (max (2 * α) (16 * β ^ 2)) := Real.mul_self_sqrt hApos.le
    have hlog := hlogsqrt _ hApos
    nlinarith [hα, hlog, hsq, hs2, Real.sqrt_nonneg (max 8 (max (2 * α) (16 * β ^ 2))), hβ0]
  -- the constant of `FitParamBound`, then `A'`
  obtain ⟨C₁, hC₁, hfpb⟩ := FitParamBound (F := F) C₀ hC₀
  obtain ⟨A, hA8, hAb⟩ := hAexists (3 * C₁) C₁ (by positivity) hC₁.le
  have hA1 : (1:ℝ) ≤ A := by linarith
  have hApos : (0:ℝ) < A := by linarith
  have hAlog0 : 0 ≤ Real.log A := Real.log_nonneg hA1
  have hA' : C₁ * (3 + Real.log A) ≤ A := by linarith only [hAb]
  refine ⟨A + A ^ 2 / 2 + C₀ * A, by positivity, ?_⟩
  intro v hclass hcenter K hK z hzx hzt τ hτpos hτhalf
  -- `B` and the fit radius `ρ`, each obtained with exactly the facts used
  have hLK1 : (1:ℝ) ≤ 1 + Real.log K := by
    have := Real.log_nonneg (show (1:ℝ) ≤ K by linarith); linarith
  obtain ⟨B, hB1, hBlog, hBLK, hBdef⟩ : ∃ B : ℝ, 1 ≤ B ∧ abs (Real.log (abs τ)) ≤ B
      ∧ (1 + Real.log K) ≤ B ∧ B = (1 + Real.log K) + abs (Real.log (abs τ)) := by
    refine ⟨(1 + Real.log K) + abs (Real.log (abs τ)), ?_, ?_, ?_, rfl⟩
    · have := abs_nonneg (Real.log (abs τ)); linarith
    · have := hLK1; linarith
    · have := abs_nonneg (Real.log (abs τ)); linarith
  have hB0 : (0:ℝ) ≤ B := by linarith only [hB1]
  rw [← hBdef]
  obtain ⟨ρ, hρpos, hρτ, hρlog, hρdef⟩ : ∃ ρ : ℝ, 0 < ρ ∧ |τ| ≤ ρ
      ∧ |Real.log ρ| ≤ Real.log A + 2 * B ∧ ρ = A * |τ| * B := by
    have hpos : (0:ℝ) < A * |τ| * B := by positivity
    have hτρ : |τ| ≤ A * |τ| * B := by
      calc |τ| = 1 * |τ| * 1 := by ring
        _ ≤ A * |τ| * B := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hA1 hτpos.le) hB1 zero_le_one
              (by positivity)
    refine ⟨A * |τ| * B, hpos, hτρ, ?_, rfl⟩
    have hBpos : (0:ℝ) < B := by linarith only [hB1]
    have hlogB : Real.log B ≤ B := by
      have h := Real.log_le_sub_one_of_pos hBpos
      linarith only [h]
    have hlogBnn : (0:ℝ) ≤ Real.log B := Real.log_nonneg hB1
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (ne_of_gt hApos) (ne_of_gt hτpos)]
    calc |Real.log A + Real.log (abs τ) + Real.log B|
        ≤ |Real.log A + Real.log (abs τ)| + |Real.log B| := abs_add_le _ _
      _ ≤ (|Real.log A| + abs (Real.log (abs τ))) + |Real.log B| := by
          have := abs_add_le (Real.log A) (Real.log (abs τ)); linarith
      _ = Real.log A + abs (Real.log (abs τ)) + Real.log B := by
          rw [abs_of_nonneg hAlog0, abs_of_nonneg hlogBnn]
      _ ≤ Real.log A + 2 * B := by linarith only [hBlog, hlogB]
  -- the fit of radius `ρ` at `z`, and its parameter bound
  obtain ⟨p, a, hfit⟩ := hclass.2 z ρ hρpos
  have hparam : ‖p‖ + |a| ≤ A * B := by
    have h := hfpb v hclass hcenter K hK z hzx hzt ρ hρpos p a hfit
    have h1 : (1 + Real.log K) + |Real.log ρ| ≤ 3 * B + Real.log A := by
      linarith only [hBLK, hρlog]
    have h2 : C₁ * ((1 + Real.log K) + |Real.log ρ|) ≤ C₁ * (3 * B + Real.log A) :=
      mul_le_mul_of_nonneg_left h1 hC₁.le
    have h3 : (0:ℝ) ≤ C₁ * Real.log A * (B - 1) :=
      mul_nonneg (mul_nonneg hC₁.le hAlog0) (by linarith only [hB1])
    have h4 : C₁ * (3 + Real.log A) * B ≤ A * B := mul_le_mul_of_nonneg_right hA' hB0
    linarith only [h, h2, h3, h4]
  have hpn : ‖p‖ ≤ A * B := by linarith only [hparam, abs_nonneg a]
  have han : |a| ≤ A * B := by linarith only [hparam, norm_nonneg p]
  -- Step 3: the vertical increment `(0, τ)` lies in the fitted box
  have hbox2 : ‖(0 : F) - τ • p‖ ≤ ρ := by
    rw [zero_sub, norm_neg, norm_smul, Real.norm_eq_abs, hρdef]
    calc |τ| * ‖p‖ ≤ |τ| * (A * B) := mul_le_mul_of_nonneg_left hpn (abs_nonneg τ)
      _ = A * |τ| * B := by ring
  -- Step 4: the fit estimate at `(0, τ)`, the spatial term vanishing
  have hmain := hfit (0 : F) τ hρτ hbox2
  rw [inner_zero_right, sub_zero] at hmain
  have hsplit : |v (z + toLp 2 ((0 : F), τ)) - v z|
      ≤ |v (z + toLp 2 ((0 : F), τ)) - v z - (a - ‖p‖ ^ 2 / 2) * τ|
        + |(a - ‖p‖ ^ 2 / 2) * τ| := by
    calc |v (z + toLp 2 ((0 : F), τ)) - v z|
        = |(v (z + toLp 2 ((0 : F), τ)) - v z - (a - ‖p‖ ^ 2 / 2) * τ)
            + (a - ‖p‖ ^ 2 / 2) * τ| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  have hcoef : |(a - ‖p‖ ^ 2 / 2) * τ| ≤ (|a| + ‖p‖ ^ 2 / 2) * |τ| := by
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg τ)
    have h := abs_sub a (‖p‖ ^ 2 / 2)
    rwa [abs_of_nonneg (show (0:ℝ) ≤ ‖p‖ ^ 2 / 2 by positivity)] at h
  -- the three pieces, each linear once the one product is supplied
  have hBsq0 : (0:ℝ) ≤ B ^ 2 - B := by nlinarith only [hB1]
  have hpsq : ‖p‖ ^ 2 ≤ (A * B) ^ 2 := by nlinarith only [hpn, norm_nonneg p]
  have e1 : C₀ * ρ ≤ C₀ * A * |τ| * B ^ 2 := by
    rw [hρdef]
    linarith only [mul_nonneg (mul_nonneg (mul_nonneg hC₀0.le hApos.le) (abs_nonneg τ)) hBsq0]
  have e2 : |a| * |τ| ≤ A * |τ| * B ^ 2 := by
    linarith only [mul_le_mul_of_nonneg_right han (abs_nonneg τ),
      mul_nonneg (mul_nonneg hApos.le (abs_nonneg τ)) hBsq0]
  have e3 : ‖p‖ ^ 2 / 2 * |τ| ≤ A ^ 2 / 2 * |τ| * B ^ 2 := by
    linarith only [mul_nonneg (sub_nonneg.mpr hpsq) (abs_nonneg τ)]
  linarith only [hsplit, hcoef, hmain, e1, e2, e3]
