import InfHarmonic.Preamble
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (7.2): at a large length, a position that beats the undisplaced
competitor in the forward quadratic envelope of a function with the box growth
`C K (1 + log K)²` cannot be farther than `C' l (1 + log l)²` from the origin. -/
theorem FarOptimizerBound (CV : ℝ) (hCV : 0 < CV) (W : WithLp 2 (F × ℝ) → ℝ)
    (hbox : ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
      ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K → |W z| ≤ CV * K * (1 + Real.log K) ^ 2)
    (x : F) (t : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℝ, 1 ≤ l → ∀ y : F,
      W (toLp 2 (x, t + l)) ≤ W (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l) →
      ‖y‖ ≤ C * l * (1 + Real.log l) ^ 2 := by
  classical
  obtain ⟨c₁, hc₁⟩ : ∃ c : ℝ, c = ‖x‖ + |t| + 3 := ⟨_, rfl⟩
  have hc₁3 : (3 : ℝ) ≤ c₁ := by
    rw [hc₁]
    have := norm_nonneg x
    have := abs_nonneg t
    linarith
  have hlog2c₁ : (0 : ℝ) ≤ Real.log (2 * c₁) := Real.log_nonneg (by linarith)
  obtain ⟨c₂, hc₂⟩ : ∃ c : ℝ, c = 16 * CV * c₁ * (1 + Real.log (2 * c₁)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨c₃, hc₃⟩ : ∃ c : ℝ, c = 16 * CV * c₁ := ⟨_, rfl⟩
  have hc₂0 : 0 < c₂ := by
    rw [hc₂]
    have h1 : (0 : ℝ) < 16 * CV * c₁ := by positivity
    have h2 : (0 : ℝ) < (1 + Real.log (2 * c₁)) ^ 2 := by
      have : (0 : ℝ) < 1 + Real.log (2 * c₁) := by linarith
      positivity
    exact mul_pos h1 h2
  have hc₃0 : 0 < c₃ := by rw [hc₃]; positivity
  -- the elementary absorption of the logarithm
  have hlogfour : ∀ u : ℝ, 1 ≤ u → Real.log u ≤ 4 * Real.sqrt (Real.sqrt u) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := by linarith
    have hs1 : (0 : ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
    have hs2 : (1 : ℝ) ≤ Real.sqrt u := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hu
    have h1 : Real.log u = 2 * Real.log (Real.sqrt u) := by
      rw [Real.log_sqrt hu0.le]; ring
    have h2 : Real.log (Real.sqrt u) = 2 * Real.log (Real.sqrt (Real.sqrt u)) := by
      rw [Real.log_sqrt hs1]; ring
    have h3 : Real.log (Real.sqrt (Real.sqrt u)) ≤ Real.sqrt (Real.sqrt u) := by
      have hpos : (0 : ℝ) < Real.sqrt (Real.sqrt u) := by
        refine Real.sqrt_pos.mpr ?_
        linarith
      have := Real.log_le_sub_one_of_pos hpos
      linarith
    rw [h1, h2]
    linarith
  have habsorb : ∀ u : ℝ, 1 ≤ u → (32 * c₃) ^ 2 ≤ u → c₃ * (Real.log u) ^ 2 ≤ u / 2 := by
    intro u hu1 hu2
    have hu0 : (0 : ℝ) < u := by linarith
    have hs : (0 : ℝ) ≤ Real.sqrt u := Real.sqrt_nonneg u
    have hlognn : (0 : ℝ) ≤ Real.log u := Real.log_nonneg hu1
    have h4 := hlogfour u hu1
    have hsq : (Real.log u) ^ 2 ≤ 16 * Real.sqrt u := by
      have h5 : (Real.log u) ^ 2 ≤ (4 * Real.sqrt (Real.sqrt u)) ^ 2 :=
        pow_le_pow_left₀ hlognn h4 2
      have h6 : (4 * Real.sqrt (Real.sqrt u)) ^ 2 = 16 * Real.sqrt u := by
        have := Real.sq_sqrt hs
        calc (4 * Real.sqrt (Real.sqrt u)) ^ 2
            = 16 * (Real.sqrt (Real.sqrt u)) ^ 2 := by ring
          _ = 16 * Real.sqrt u := by rw [Real.sq_sqrt hs]
      linarith [h5, h6]
    have hsqrtge : 32 * c₃ ≤ Real.sqrt u := by
      rw [show (32 : ℝ) * c₃ = Real.sqrt ((32 * c₃) ^ 2) from by
        rw [Real.sqrt_sq (by positivity)]]
      exact Real.sqrt_le_sqrt hu2
    have hmul : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
    nlinarith [hsq, hsqrtge, hmul, hc₃0, hs]
  obtain ⟨b₀, hb₀⟩ : ∃ b : ℝ, b = max 2 ((32 * c₃) ^ 2) := ⟨_, rfl⟩
  have hb₀2 : (2 : ℝ) ≤ b₀ := by rw [hb₀]; exact le_max_left _ _
  have hb₀sq : ((32 : ℝ) * c₃) ^ 2 ≤ b₀ := by rw [hb₀]; exact le_max_right _ _
  refine ⟨‖x‖ + 2 + (2 * c₂ + b₀), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ ‖x‖ := norm_nonneg x
    have h2 : (0 : ℝ) < 2 * c₂ := by linarith [hc₂0]
    linarith [hb₀2]
  intro l hl y hcomp
  have hl0 : (0 : ℝ) < l := by linarith
  have hLl : (1 : ℝ) ≤ 1 + Real.log l := by
    have : (0 : ℝ) ≤ Real.log l := Real.log_nonneg hl
    linarith
  have hLl2 : (1 : ℝ) ≤ (1 + Real.log l) ^ 2 := by nlinarith [hLl]
  obtain ⟨β, hβ⟩ : ∃ b : ℝ, b = ‖y - x‖ / l := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β := by
    rw [hβ]
    positivity
  have hβl : ‖y - x‖ = β * l := by
    rw [hβ]
    field_simp
  have hynorm : ‖y‖ ≤ ‖x‖ + β * l := by
    have h := norm_le_norm_add_norm_sub' y x
    rw [← hβl]
    linarith [h, norm_sub_rev y x]
  -- one finishing computation, used in each regime
  have hfinish : ∀ D : ℝ, 0 ≤ D → β ≤ D * (1 + Real.log l) ^ 2 →
      D ≤ 2 + (2 * c₂ + b₀) →
      ‖y‖ ≤ (‖x‖ + 2 + (2 * c₂ + b₀)) * l * (1 + Real.log l) ^ 2 := by
    intro D hD hβD hDle
    have h1 : β * l ≤ D * (1 + Real.log l) ^ 2 * l :=
      mul_le_mul_of_nonneg_right hβD hl0.le
    have h2 : ‖x‖ ≤ ‖x‖ * l * (1 + Real.log l) ^ 2 := by
      have h3 : ‖x‖ * 1 ≤ ‖x‖ * l := mul_le_mul_of_nonneg_left hl (norm_nonneg x)
      have h4 : ‖x‖ * l * 1 ≤ ‖x‖ * l * (1 + Real.log l) ^ 2 :=
        mul_le_mul_of_nonneg_left hLl2 (by positivity)
      linarith
    have h5 : D * (1 + Real.log l) ^ 2 * l
        ≤ (2 + (2 * c₂ + b₀)) * (1 + Real.log l) ^ 2 * l := by
      have h6 : (0 : ℝ) ≤ (1 + Real.log l) ^ 2 * l := by positivity
      have h7 : D * ((1 + Real.log l) ^ 2 * l)
          ≤ (2 + (2 * c₂ + b₀)) * ((1 + Real.log l) ^ 2 * l) :=
        mul_le_mul_of_nonneg_right hDle h6
      calc D * (1 + Real.log l) ^ 2 * l = D * ((1 + Real.log l) ^ 2 * l) := by ring
        _ ≤ (2 + (2 * c₂ + b₀)) * ((1 + Real.log l) ^ 2 * l) := h7
        _ = (2 + (2 * c₂ + b₀)) * (1 + Real.log l) ^ 2 * l := by ring
    have h8 : (‖x‖ + 2 + (2 * c₂ + b₀)) * l * (1 + Real.log l) ^ 2
        = ‖x‖ * l * (1 + Real.log l) ^ 2
          + (2 + (2 * c₂ + b₀)) * (1 + Real.log l) ^ 2 * l := by ring
    rw [h8]
    linarith [hynorm, h1, h2, h5]
  rcases le_or_gt β 2 with hcase | hcase
  · refine hfinish 2 (by norm_num) ?_ (by linarith [hc₂0, hb₀2])
    have h1 : (2 : ℝ) * 1 ≤ 2 * (1 + Real.log l) ^ 2 :=
      mul_le_mul_of_nonneg_left hLl2 (by norm_num)
    linarith [hcase, h1]
  · -- the far regime: the box bound forces `β` to be logarithmic
    have hβ2 : (2 : ℝ) < β := hcase
    have hbl : (2 : ℝ) ≤ β * l := by
      have h1 : β * 1 ≤ β * l := mul_le_mul_of_nonneg_left hl (by linarith)
      linarith
    have hblpos : (0 : ℝ) < β * l := by linarith
    have hc1bl : c₁ ≤ c₁ * (β * l) := by
      refine le_mul_of_one_le_right (by linarith) (by linarith)
    have hblc1 : β * l ≤ c₁ * (β * l) := by
      refine le_mul_of_one_le_left (by linarith) (by linarith)
    have hc1bl6 : (6 : ℝ) ≤ c₁ * (β * l) :=
      le_trans (by norm_num) (mul_le_mul hc₁3 hbl (by norm_num) (by linarith))
    obtain ⟨Θ, hΘ⟩ : ∃ T : ℝ, T = 2 * (c₁ * (β * l)) := ⟨_, rfl⟩
    have hΘ2 : (2 : ℝ) ≤ Θ := by rw [hΘ]; linarith
    have hΘpos : (0 : ℝ) < Θ := by linarith
    have hxc₁ : ‖x‖ ≤ c₁ := by rw [hc₁]; linarith [abs_nonneg t]
    have htc₁ : |t| ≤ c₁ := by rw [hc₁]; linarith [norm_nonneg x]
    have hymem : ‖y‖ ≤ Θ := by
      rw [hΘ]
      linarith [hynorm, hxc₁, hc1bl, hblc1]
    have hxmem : ‖x‖ ≤ Θ := by
      rw [hΘ]
      linarith [hxc₁, hc1bl, hblc1]
    have htmem : |t + l| ≤ Θ := by
      have h1 : |t + l| ≤ |t| + l := by
        refine le_trans (abs_add_le t l) ?_
        rw [abs_of_nonneg hl0.le]
      have h2 : l ≤ β * l := by
        have := mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ β by linarith) hl0.le
        linarith
      rw [hΘ]
      linarith [h1, htc₁, hc1bl, hblc1, h2]
    have hWy : |W (toLp 2 (y, t + l))| ≤ CV * Θ * (1 + Real.log Θ) ^ 2 := by
      refine hbox Θ hΘ2 _ ?_ ?_
      · simpa using hymem
      · simpa using htmem
    have hWx : |W (toLp 2 (x, t + l))| ≤ CV * Θ * (1 + Real.log Θ) ^ 2 := by
      refine hbox Θ hΘ2 _ ?_ ?_
      · simpa using hxmem
      · simpa using htmem
    have hcost : β * (β * l) / 2 ≤ 2 * (CV * Θ * (1 + Real.log Θ) ^ 2) := by
      have h1 : ‖y - x‖ ^ 2 / (2 * l) = β * (β * l) / 2 := by
        rw [hβl]
        field_simp
      have h2 : ‖y - x‖ ^ 2 / (2 * l)
          ≤ W (toLp 2 (y, t + l)) - W (toLp 2 (x, t + l)) := by linarith [hcomp]
      rw [h1] at h2
      have h3 : W (toLp 2 (y, t + l)) ≤ |W (toLp 2 (y, t + l))| := le_abs_self _
      have h4 : -(W (toLp 2 (x, t + l))) ≤ |W (toLp 2 (x, t + l))| := neg_le_abs _
      linarith [h2, h3, h4, hWy, hWx]
    have hlogΘ : Real.log Θ = Real.log (2 * c₁) + Real.log (β * l) := by
      rw [hΘ, show (2 : ℝ) * (c₁ * (β * l)) = (2 * c₁) * (β * l) from by ring,
        Real.log_mul (by positivity) (by linarith)]
    have hlogβl : Real.log (β * l) = Real.log β + Real.log l :=
      Real.log_mul (by linarith) (by linarith)
    have hlogβnn : (0 : ℝ) ≤ Real.log β := Real.log_nonneg (by linarith)
    have hLΘle : 1 + Real.log Θ
        ≤ (1 + Real.log (2 * c₁)) * (1 + Real.log l) + Real.log β := by
      rw [hlogΘ, hlogβl]
      have hprod : (1 + Real.log (2 * c₁)) * (1 + Real.log l)
          = 1 + Real.log (2 * c₁) + Real.log l
            + Real.log (2 * c₁) * Real.log l := by ring
      have hnn : (0 : ℝ) ≤ Real.log (2 * c₁) * Real.log l := by
        have : (0 : ℝ) ≤ Real.log l := by linarith
        exact mul_nonneg hlog2c₁ this
      linarith [hprod, hnn]
    have hLΘnn : (0 : ℝ) ≤ 1 + Real.log Θ := by
      have : (0 : ℝ) ≤ Real.log Θ := Real.log_nonneg (by linarith)
      linarith
    have hLΘsq : (1 + Real.log Θ) ^ 2
        ≤ 2 * ((1 + Real.log (2 * c₁)) ^ 2 * (1 + Real.log l) ^ 2)
          + 2 * (Real.log β) ^ 2 := by
      have h1 : (1 + Real.log Θ) ^ 2
          ≤ ((1 + Real.log (2 * c₁)) * (1 + Real.log l) + Real.log β) ^ 2 :=
        pow_le_pow_left₀ hLΘnn hLΘle 2
      have h2 : ((1 + Real.log (2 * c₁)) * (1 + Real.log l) + Real.log β) ^ 2
          ≤ 2 * ((1 + Real.log (2 * c₁)) * (1 + Real.log l)) ^ 2
            + 2 * (Real.log β) ^ 2 := by
        nlinarith [sq_nonneg ((1 + Real.log (2 * c₁)) * (1 + Real.log l) - Real.log β)]
      have h3 : ((1 + Real.log (2 * c₁)) * (1 + Real.log l)) ^ 2
          = (1 + Real.log (2 * c₁)) ^ 2 * (1 + Real.log l) ^ 2 := by ring
      linarith [h1, h2, h3]
    -- divide the cost inequality by `β l / 2`
    have hdiv : β ≤ 8 * CV * c₁ * (1 + Real.log Θ) ^ 2 := by
      have h1 : β * (β * l) / 2 ≤ 4 * CV * (c₁ * (β * l)) * (1 + Real.log Θ) ^ 2 := by
        have h0 : 2 * (CV * Θ * (1 + Real.log Θ) ^ 2)
            = 4 * CV * (c₁ * (β * l)) * (1 + Real.log Θ) ^ 2 := by
          rw [hΘ]; ring
        linarith [hcost, h0]
      have h2 : β * ((β * l) / 2) ≤ (8 * CV * c₁ * (1 + Real.log Θ) ^ 2) * ((β * l) / 2) := by
        have h3 : (8 * CV * c₁ * (1 + Real.log Θ) ^ 2) * ((β * l) / 2)
            = 4 * CV * (c₁ * (β * l)) * (1 + Real.log Θ) ^ 2 := by ring
        rw [h3]
        linarith [h1, show β * ((β * l) / 2) = β * (β * l) / 2 from by ring]
      have h4 : (0 : ℝ) < (β * l) / 2 := by linarith
      exact le_of_mul_le_mul_right (by linarith [h2]) h4
    have hkey : β ≤ c₂ * (1 + Real.log l) ^ 2 + c₃ * (Real.log β) ^ 2 := by
      have h1 : 8 * CV * c₁ * (1 + Real.log Θ) ^ 2
          ≤ 8 * CV * c₁ * (2 * ((1 + Real.log (2 * c₁)) ^ 2 * (1 + Real.log l) ^ 2)
            + 2 * (Real.log β) ^ 2) := by
        refine mul_le_mul_of_nonneg_left hLΘsq ?_
        positivity
      have h2 : 8 * CV * c₁ * (2 * ((1 + Real.log (2 * c₁)) ^ 2 * (1 + Real.log l) ^ 2)
            + 2 * (Real.log β) ^ 2)
          = c₂ * (1 + Real.log l) ^ 2 + c₃ * (Real.log β) ^ 2 := by
        rw [hc₂, hc₃]; ring
      linarith [hdiv, h1, h2]
    -- absorb
    rcases le_or_gt b₀ β with hbig | hsmall
    · have h1 : c₃ * (Real.log β) ^ 2 ≤ β / 2 :=
        habsorb β (by linarith) (le_trans hb₀sq hbig)
      have h2 : β ≤ 2 * c₂ * (1 + Real.log l) ^ 2 := by linarith [hkey, h1]
      exact hfinish (2 * c₂) (by linarith [hc₂0]) h2 (by linarith [hb₀2])
    · have h2 : β ≤ b₀ * (1 + Real.log l) ^ 2 := by
        have hb : (0 : ℝ) ≤ b₀ := by linarith
        have h3 : b₀ * 1 ≤ b₀ * (1 + Real.log l) ^ 2 := mul_le_mul_of_nonneg_left hLl2 hb
        linarith [hsmall, h3]
      exact hfinish b₀ (by linarith [hb₀2]) h2 (by linarith [hc₂0])
