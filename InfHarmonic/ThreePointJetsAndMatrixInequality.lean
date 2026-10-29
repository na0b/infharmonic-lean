module

public import InfHarmonic.SumRuleJets
public import InfHarmonic.InfSubsolutionClosedSuperjet

@[expose] public section
set_option maxHeartbeats 400000
open Set Metric WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 5(b)(c) of paper Proposition 2.6: the bounds on the three jets of the
three-point test at a maximizing triple, and the positivity of the second
variation in the direction they span.

The three gradients of the paper are `p₁ = q + ½f(r)DB(c) - h/r² + a e`,
`p₂ = q + ½f(r)DB(c) - h/r² - a e` and `p₀ = q - h/r²`, with
`a = B(c)f'(r) - 2|h|²/r³` and `e` the unit vector along `x - y`; they are given
here as data together with the hypothesis that the three gradient blocks of
`∇Ψ(Z)` are `p₁`, `p₂` and `-2p₀`, which is what reading off the derivative of
the test at the maximizing triple supplies.

Three of the conclusions are the paper's bounds. Since `f'(r) = 1 - 3√r/16` and
`|h| ≤ 2Cr²`, the smallness of `r` gives `f'(r) ≥ 3/4` and
`2|h|²/r³ ≤ 8C²r ≤ δ/8`, so `a ≥ δ/4`; the same two ingredients and
`B(c) ≤ B_out` give `a ≤ B_out`; and in the mean `½(p₁ + p₂)` the radial parts
`±a e` cancel, so that mean is bounded by `K₃ = C + ¾K₁ + 2C` with no bound on
`e` needed. The fourth conclusion is the matrix inequality: applying the sum
rule to the three functions `g₀, g₁, g₂`, each an infinity subsolution on the
unit ball, at the local maximum `Z` of `∑ⱼ gⱼ - Ψ` produces, for each
regularization parameter `η > 0`, three closed superjets whose gradients are
`p₁`, `p₂` and `-2p₀`; the viscosity inequality at each gives
`Xⱼ[·] ≥ 0` there, and the sum-rule matrix inequality evaluated at
`σ = (p₁, p₂, p₀)` gives `0 ≤ D²Ψ(Z)[σ,σ] + η‖D²Ψ(Z)σ‖²`. The maximum, the
Hessian and `σ` are all fixed as `η` decreases to zero --- only the jets `Xⱼ`
vary with `η` --- so `D²Ψ(Z)[σ,σ] ≥ 0`. The ambient space is an arbitrary
finite-dimensional real inner-product space `E`. -/
theorem ThreePointJetsAndMatrixInequality
    (psi : PiLp 2 (fun _ : Fin 3 => E) → ℝ) (Z σ : PiLp 2 (fun _ : Fin 3 => E))
    (g : Fin 3 → E → ℝ)
    (p₀ p₁ p₂ pq ev cm hv : E) (Bf : E → ℝ) (f f₁ : ℝ → ℝ)
    (av r δ C K₁ K₃ B_out : ℝ)
    (hav : av = Bf cm * f₁ r - 2 * ‖hv‖ ^ 2 / r ^ 3)
    (hp₁ : p₁ = pq + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm - (r ^ 2)⁻¹ • hv + av • ev)
    (hp₂ : p₂ = pq + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm - (r ^ 2)⁻¹ • hv - av • ev)
    (hσ0 : ofLp σ 0 = p₁) (hσ1 : ofLp σ 1 = p₂) (hσ2 : ofLp σ 2 = p₀)
    (hq0 : ofLp (gradient psi Z) 0 = p₁) (hq1 : ofLp (gradient psi Z) 1 = p₂)
    (hq2 : ofLp (gradient psi Z) 2 = -(2 : ℝ) • p₀)
    (hgsub : ∀ j : Fin 3, IsInfSubsolutionOn (ball (0 : E) 1) (g j))
    (hZmem : ∀ j : Fin 3, ofLp Z j ∈ ball (0 : E) 1)
    (hpsiC2 : ContDiffAt ℝ 2 psi Z)
    (hlocmax : IsLocalMax (fun Y : PiLp 2 (fun _ : Fin 3 => E) =>
      (∑ j, g j (ofLp Y j)) - psi Y) Z)
    (hrpos : 0 < r) (hrle : r ≤ 3 / 2)
    (hf₁r : f₁ r = 1 - 3 * Real.sqrt r / 16) (hf₁le : f₁ r ≤ 1)
    (hsmall : 3 / 16 * Real.sqrt r ≤ 1 / 4 ∧ 8 * C ^ 2 * r ≤ δ / 8)
    (hhvbd : ‖hv‖ ≤ 2 * C * r ^ 2)
    (hBfge : δ / 2 ≤ Bf cm) (hBfle : Bf cm ≤ B_out) (hδ : 0 < δ)
    (hgK : ‖gradient Bf cm‖ ≤ K₁) (hfrle : f r ≤ r) (hfr0 : 0 ≤ f r)
    (hpqn : ‖pq‖ ≤ C) (hK₃ : K₃ = C + 3 / 4 * K₁ + 2 * C) :
    δ / 4 ≤ av ∧ av ≤ B_out ∧ ‖(2 : ℝ)⁻¹ • (p₁ + p₂)‖ ≤ K₃
      ∧ 0 ≤ fderiv ℝ (fderiv ℝ psi) Z σ σ := by
  classical
  -- (5b) `a ≥ δ/4` for small `r`
  have tpf_alow : δ / 4 ≤ av := by
    have hf₁ge : 3 / 4 ≤ f₁ r := by rw [hf₁r]; linarith only [hsmall.1]
    have hr3 : (0 : ℝ) < r ^ 3 := pow_pos hrpos 3
    -- `2|h|²/r³ ≤ 2(2Cr²)²/r³ = 8C²r ≤ δ/8`
    have hpen : 2 * ‖hv‖ ^ 2 / r ^ 3 ≤ δ / 8 := by
      have h1 : ‖hv‖ ^ 2 ≤ (2 * C * r ^ 2) ^ 2 := by
        nlinarith only [hhvbd, norm_nonneg hv]
      have h2 : 2 * ‖hv‖ ^ 2 / r ^ 3 ≤ 2 * (2 * C * r ^ 2) ^ 2 / r ^ 3 := by
        apply div_le_div_of_nonneg_right _ hr3.le
        · linarith only [h1]
      have h3 : 2 * (2 * C * r ^ 2) ^ 2 / r ^ 3 = 8 * C ^ 2 * r := by
        field_simp; ring
      rw [h3] at h2
      linarith only [hsmall.2, h2]
    have hprod : δ / 2 * (3 / 4) ≤ Bf cm * f₁ r := by
      have u1 : δ / 2 * (3 / 4) ≤ δ / 2 * f₁ r :=
        mul_le_mul_of_nonneg_left hf₁ge (by linarith only [hδ])
      have u2 : δ / 2 * f₁ r ≤ Bf cm * f₁ r :=
        mul_le_mul_of_nonneg_right hBfge (by linarith only [hf₁ge])
      linarith only [u1, u2]
    rw [hav]
    linarith only [hprod, hpen]
  -- (5a) eq:tpf-bounds: `a ≤ B_out`
  have tpf_aub : av ≤ B_out := by
    have hBf0 : 0 ≤ Bf cm := by linarith only [hBfge, hδ]
    have hpen0 : 0 ≤ 2 * ‖hv‖ ^ 2 / r ^ 3 :=
      div_nonneg (by linarith only [sq_nonneg ‖hv‖]) (le_of_lt (pow_pos hrpos 3))
    have s1 : Bf cm * f₁ r ≤ Bf cm * 1 := mul_le_mul_of_nonneg_left hf₁le hBf0
    have s2 : Bf cm * 1 ≤ B_out * 1 := mul_le_mul_of_nonneg_right hBfle (by norm_num)
    rw [hav]
    linarith only [s1, s2, hpen0]
  -- (5a) eq:tpf-bounds: the mean endpoint velocity is bounded by `K₃`.  The radial
  -- parts `± a e` cancel in the mean, which is why no bound on `e` is needed.
  have hmean : (2 : ℝ)⁻¹ • (p₁ + p₂)
      = pq + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm - (r ^ 2)⁻¹ • hv := by
    rw [hp₁, hp₂]; module
  have tpf_K₃ : ‖(2 : ℝ)⁻¹ • (p₁ + p₂)‖ ≤ K₃ := by
    have t1 : ‖((2 : ℝ)⁻¹ * f r) • gradient Bf cm‖ ≤ 3 / 4 * K₁ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith only [hfr0])]
      exact mul_le_mul (by linarith only [hfrle, hrle]) hgK (norm_nonneg _) (by norm_num)
    have t2 : ‖(r ^ 2)⁻¹ • hv‖ ≤ 2 * C := by
      have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hrpos 2
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hr2))]
      have h1 : (r ^ 2)⁻¹ * ‖hv‖ ≤ (r ^ 2)⁻¹ * (2 * C * r ^ 2) :=
        mul_le_mul_of_nonneg_left hhvbd (le_of_lt (inv_pos.mpr hr2))
      have h2 : (r ^ 2)⁻¹ * (2 * C * r ^ 2) = 2 * C := by
        field_simp
      linarith only [h1, h2]
    have hsplit : ‖pq + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm‖
        ≤ ‖pq‖ + ‖((2 : ℝ)⁻¹ * f r) • gradient Bf cm‖ :=
      norm_add_le _ _
    have hsub : ‖pq + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm - (r ^ 2)⁻¹ • hv‖
        ≤ ‖pq + ((2 : ℝ)⁻¹ * f r) • gradient Bf cm‖ + ‖(r ^ 2)⁻¹ • hv‖ :=
      norm_sub_le _ _
    rw [hmean, hK₃]
    linarith only [hsub, hsplit, hpqn, t1, t2]
  -- (5c) eq:tpf-jets, eq:tpf-matrix and the `η ↓ 0` passage: eq:tpf-Apos
  have tpf_Apos : 0 ≤ fderiv ℝ (fderiv ℝ psi) Z σ σ := by
    have hall : ∀ η : ℝ, 0 < η → 0 ≤ fderiv ℝ (fderiv ℝ psi) Z σ σ
        + η * ‖fderiv ℝ (fderiv ℝ psi) Z σ‖ ^ 2 := by
      intro η hη
      borelize E
      obtain ⟨X, -, hXjet, hXmat⟩ := SumRuleJets 3 (fun _ => ball (0 : E) 1)
        (fun _ => Metric.isOpen_ball) g (fun j => (hgsub j).2.1) psi Z hZmem hpsiC2
        hlocmax η hη
      -- the viscosity inequality at each of the three jets
      have hj0 : 0 ≤ X 0 p₁ p₁ := by
        have h := hXjet 0
        rw [hq0] at h
        exact InfSubsolutionClosedSuperjet (ball (0 : E) 1) (g 0) (hgsub 0)
          (ofLp Z 0) (hZmem 0) p₁ (X 0) h
      have hj1 : 0 ≤ X 1 p₂ p₂ := by
        have h := hXjet 1
        rw [hq1] at h
        exact InfSubsolutionClosedSuperjet (ball (0 : E) 1) (g 1) (hgsub 1)
          (ofLp Z 1) (hZmem 1) p₂ (X 1) h
      have hj2 : 0 ≤ X 2 p₀ p₀ := by
        have h := hXjet 2
        rw [hq2] at h
        have h4 := InfSubsolutionClosedSuperjet (ball (0 : E) 1) (g 2) (hgsub 2)
          (ofLp Z 2) (hZmem 2) (-(2 : ℝ) • p₀) (X 2) h
        have he : X 2 (-(2 : ℝ) • p₀) (-(2 : ℝ) • p₀) = 4 * X 2 p₀ p₀ := by
          simp only [map_smul, smul_apply, smul_eq_mul]
          ring
        rw [he] at h4
        linarith only [h4]
      -- the diagonal sum at `σ = (p₁, p₂, p₀)`
      have hsum : (∑ j, X j (ofLp σ j) (ofLp σ j))
          = X 0 p₁ p₁ + X 1 p₂ p₂ + X 2 p₀ p₀ := by
        rw [Fin.sum_univ_three, hσ0, hσ1, hσ2]
      have hmat := hXmat σ
      rw [hsum] at hmat
      linarith only [hmat, hj0, hj1, hj2]
    -- the `η ↓ 0` passage: neither the Hessian nor `σ` depends on `η`
    by_contra hcon
    rw [not_le] at hcon
    have hden : (0 : ℝ) < 2 * (‖fderiv ℝ (fderiv ℝ psi) Z σ‖ ^ 2 + 1) := by
      have := sq_nonneg ‖fderiv ℝ (fderiv ℝ psi) Z σ‖
      linarith only [this]
    have hη0 : 0 < -(fderiv ℝ (fderiv ℝ psi) Z σ σ)
        / (2 * (‖fderiv ℝ (fderiv ℝ psi) Z σ‖ ^ 2 + 1)) :=
      div_pos (by linarith only [hcon]) hden
    have hstep := hall _ hη0
    have hkey : -(fderiv ℝ (fderiv ℝ psi) Z σ σ)
        / (2 * (‖fderiv ℝ (fderiv ℝ psi) Z σ‖ ^ 2 + 1))
        * ‖fderiv ℝ (fderiv ℝ psi) Z σ‖ ^ 2
        ≤ -(fderiv ℝ (fderiv ℝ psi) Z σ σ) / 2 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hden (by norm_num)]
      have h1 := sq_nonneg ‖fderiv ℝ (fderiv ℝ psi) Z σ‖
      nlinarith only [h1, hcon]
    linarith only [hstep, hkey, hcon]
  exact ⟨tpf_alow, tpf_aub, tpf_K₃, tpf_Apos⟩
