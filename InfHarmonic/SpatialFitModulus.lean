module

public import InfHarmonic.FitParamBound

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.5): the spatial modulus of continuity of a centered member of
`A_{m,C₀}` on the box of size `K`. -/
theorem SpatialFitModulus (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      (IsCenteredAt C₀ v 0 ∨ IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ)))) →
      ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
        ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
        ∀ r : ℝ, 0 < r → ∀ h : F, ‖h‖ ≤ r →
          |v (z + toLp 2 (h, (0 : ℝ))) - v z|
            ≤ C * r * ((1 + Real.log K) + |Real.log r|) := by
  have _unused_fd : FiniteDimensional ℝ F := inferInstance
  have hC₀0 : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  -- the constant of `FitParamBound`, consumed as a black box
  obtain ⟨C₁, hC₁, hfpb⟩ := FitParamBound (F := F) C₀ hC₀
  refine ⟨C₁ + C₀, by positivity, ?_⟩
  intro v hclass hcenter K hK z hzx hzt r hrpos h hhr
  -- `L(K) = 1 + log K ≥ 1 + log 2 ≥ 1`, so the whole factor is at least one
  have hLK1 : (1:ℝ) ≤ (1 + Real.log K) + |Real.log r| := by
    have h1 : (0:ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
    have h2 : (0:ℝ) ≤ |Real.log r| := abs_nonneg _
    linarith only [h1, h2]
  -- the fit of radius `r` at `z`, and its parameter bound
  obtain ⟨p, a, hfit⟩ := hclass.2 z r hrpos
  have hparam : ‖p‖ + |a| ≤ C₁ * ((1 + Real.log K) + |Real.log r|) :=
    hfpb v hclass hcenter K hK z hzx hzt r hrpos p a hfit
  have hpn : ‖p‖ ≤ C₁ * ((1 + Real.log K) + |Real.log r|) := by
    linarith only [hparam, abs_nonneg a]
  -- the increment `(h, 0)` lies in the fitted box
  have hbox1 : |(0:ℝ)| ≤ r := by rw [abs_zero]; exact hrpos.le
  have hbox2 : ‖h - (0:ℝ) • p‖ ≤ r := by rw [zero_smul, sub_zero]; exact hhr
  -- the fit estimate at `(h, 0)`, the time term dropping out because `l = 0`
  have hmain := hfit h (0:ℝ) hbox1 hbox2
  rw [mul_zero, sub_zero] at hmain
  -- Cauchy-Schwarz on the spatial term, then `‖h‖ ≤ r`
  have hcs : |inner ℝ p h| ≤ ‖p‖ * ‖h‖ := abs_real_inner_le_norm p h
  have hprod : ‖p‖ * ‖h‖ ≤ ‖p‖ * r := mul_le_mul_of_nonneg_left hhr (norm_nonneg p)
  have hsplit : |v (z + toLp 2 (h, (0 : ℝ))) - v z|
      ≤ |v (z + toLp 2 (h, (0 : ℝ))) - v z - inner ℝ p h| + |inner ℝ p h| := by
    calc |v (z + toLp 2 (h, (0 : ℝ))) - v z|
        = |(v (z + toLp 2 (h, (0 : ℝ))) - v z - inner ℝ p h) + inner ℝ p h| := by
          congr 1; ring
      _ ≤ _ := abs_add_le _ _
  -- the two products, each supplied explicitly so the last step is linear
  have e1 : ‖p‖ * r ≤ C₁ * ((1 + Real.log K) + |Real.log r|) * r :=
    mul_le_mul_of_nonneg_right hpn hrpos.le
  have e2 : C₀ * r ≤ C₀ * r * ((1 + Real.log K) + |Real.log r|) := by
    have hle := mul_le_mul_of_nonneg_left hLK1 (show (0:ℝ) ≤ C₀ * r by positivity)
    linarith only [hle]
  linarith only [hsplit, hmain, hcs, hprod, e1, e2]
