module

public import InfHarmonic.ProfileProductSecondVariation
public import InfHarmonic.RadialQuotientSecondVariation
public import InfHarmonic.SecondVariationAlongLine

@[expose] public section
set_option maxHeartbeats 400000
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 6 of paper Proposition 2.6: the second variation of the three-point
test along the straight-line joint motion is very negative at small radius.

The test is read through three block maps of the jet product space
`ℓ²(E × E × E)`: `Ld` is the endpoint difference `x - y`, `Lc` the endpoint
midpoint `c`, and `Lh` the deviation `h` of the third point from that midpoint,
so that `psi Y = aff Y + B(c) f(r) + |h|² / r²` with `r = ‖Ld Y‖`. At the
evaluation point `Zm` the endpoint difference is `r • ev` with `‖ev‖ = 1`, and
the velocity `σ` realizes the paper's four exact identities of the joint motion:
`ṙ = 2a` (here `Ld σ = (2 av) • ev`), `r̈ = 0` (the motion is a straight line),
`ċ = ½(p₁ + p₂)` (here `Lc σ`) and `ḣ = -½ f(r) DB(c)` (here `Lh σ`). The
constant `Mc` collects the five `O(1)` contributions --- the three penalty terms
coming from `|h|² / r²` and the two localizing terms of `B(c) f(r)` --- while
the dominant term carries the blow-up `f''(r) = -3/(32 √r)` of the profile and
is made explicit through `δ/4 ≤ av` and `δ/2 ≤ B(c)`, turning the paper's
`-3B(c)a²/(8 √r)` into `-3δ³/(256 √r)`. The ambient space is an arbitrary
finite-dimensional real inner-product space `E`. -/
theorem ThreePointTestSecondVariation
    (Lc Ld Lh : PiLp 2 (fun _ : Fin 3 => E) →L[ℝ] E)
    (aff : PiLp 2 (fun _ : Fin 3 => E) →L[ℝ] ℝ)
    (psi : PiLp 2 (fun _ : Fin 3 => E) → ℝ)
    (Zm σ : PiLp 2 (fun _ : Fin 3 => E))
    (Bf : E → ℝ) (f f₁ : ℝ → ℝ) (cm hv ev p₁ p₂ : E)
    (r av δ C B_out K₁ K₂ K₃ Mc : ℝ)
    (hpsi : ∀ Y : PiLp 2 (fun _ : Fin 3 => E),
      psi Y = aff Y + Bf (Lc Y) * f ‖Ld Y‖ + ‖Lh Y‖ ^ 2 / ‖Ld Y‖ ^ 2)
    (hpsiC2 : ContDiffAt ℝ 2 psi Zm)
    (hLcZm : Lc Zm = cm) (hLdZm : Ld Zm = r • ev) (hLhZm : Lh Zm = hv)
    (hLcσv : Lc σ = (2 : ℝ)⁻¹ • (p₁ + p₂))
    (hLdσ : Ld σ = (2 * av) • ev)
    (hLhσv : Lh σ = -(((2 : ℝ)⁻¹ * f r) • gradient Bf cm))
    (hevn : ‖ev‖ = 1) (hrpos : 0 < r) (hrle : r ≤ 3 / 2)
    (hfr0 : 0 ≤ f r) (hfrle : f r ≤ r)
    (hfnear : ∀ᶠ ρ : ℝ in nhds r, HasDerivAt f (f₁ ρ) ρ)
    (hf2r : HasDerivAt f₁ (-(3 / (32 * Real.sqrt r))) r)
    (hf₁0 : 0 ≤ f₁ r) (hf₁le : f₁ r ≤ 1)
    (hBfC2 : ContDiff ℝ 2 Bf) (hBfge : δ / 2 ≤ Bf cm)
    (hD1n : ‖fderiv ℝ Bf cm‖ ≤ K₁)
    (hD2n : ‖fderiv ℝ (fderiv ℝ Bf) cm‖ ≤ K₂)
    (hgK : ‖gradient Bf cm‖ ≤ K₁) (hK₁0 : 0 ≤ K₁) (hK₂0 : 0 ≤ K₂)
    (hcdK : ‖(2 : ℝ)⁻¹ • (p₁ + p₂)‖ ≤ K₃)
    (hδ : 0 < δ) (hav0 : 0 < av) (halow : δ / 4 ≤ av) (haub : av ≤ B_out)
    (hCpos : 0 < C) (hhvbd : ‖hv‖ ≤ 2 * C * r ^ 2)
    (hMc : Mc = K₁ ^ 2 / 2 + 16 * B_out * C * K₁ + 96 * B_out ^ 2 * C ^ 2
      + 3 / 2 * K₂ * K₃ ^ 2 + 4 * B_out * K₁ * K₃) :
    fderiv ℝ (fderiv ℝ psi) Zm σ σ ≤ Mc - 3 * δ ^ 3 / (256 * Real.sqrt r) := by
  -- the velocities `ċ` and `ḣ` of the paper's joint motion, named
  obtain ⟨cdot, hcdot⟩ : ∃ cdot : E, cdot = (2 : ℝ)⁻¹ • (p₁ + p₂) := ⟨_, rfl⟩
  obtain ⟨hdot, hhdot⟩ : ∃ hdot : E,
      hdot = -(((2 : ℝ)⁻¹ * f r) • gradient Bf cm) := ⟨_, rfl⟩
  have hLcσ : Lc σ = cdot := by rw [hLcσv, hcdot]
  have hLhσ : Lh σ = hdot := by rw [hLhσv, hhdot]
  have hLdline : ∀ τ : ℝ, Ld (Zm + τ • σ) = (r + τ * (2 * av)) • ev := by
    intro τ
    rw [map_add, ContinuousLinearMap.map_smul, hLdZm, hLdσ]
    module
  have hnormline : ∀ τ : ℝ, 0 ≤ r + τ * (2 * av) →
      ‖Ld (Zm + τ • σ)‖ = r + τ * (2 * av) := by
    intro τ hτ
    rw [hLdline τ, norm_smul, Real.norm_eq_abs, abs_of_nonneg hτ, hevn, mul_one]
  have hLcline : ∀ τ : ℝ, Lc (Zm + τ • σ) = cm + τ • cdot := by
    intro τ; rw [map_add, ContinuousLinearMap.map_smul, hLcZm, hLcσ]
  have hLhline : ∀ τ : ℝ, Lh (Zm + τ • σ) = hv + τ • hdot := by
    intro τ; rw [map_add, ContinuousLinearMap.map_smul, hLhZm, hLhσ]
  have hAffline : ∀ τ : ℝ, aff (Zm + τ • σ) = aff Zm + τ * aff σ := by
    intro τ; rw [map_add, ContinuousLinearMap.map_smul]; rfl
  -- the two derivative packages of Step 6, in the shape SecondVariationAlongLine consumes
  obtain ⟨fc, hfcdef⟩ : ∃ fc : ℝ, fc = -(3 / (32 * Real.sqrt r)) := ⟨_, rfl⟩
  have hf₁der : HasDerivAt f₁ fc r := by rw [hfcdef]; exact hf2r
  obtain ⟨GB, hGB1, hGB2⟩ := ProfileProductSecondVariation Bf f f₁ cm cdot r (2 * av) fc
    hBfC2 hfnear hf₁der
  obtain ⟨GQ, hGQ1, hGQ2⟩ := RadialQuotientSecondVariation hv hdot r (2 * av) hrpos
  -- the whole test along the motion, as a one-variable function
  obtain ⟨ρf, hρf⟩ : ∃ ρf : ℝ → ℝ, ρf = fun τ : ℝ =>
      (aff Zm + τ * aff σ) + Bf (cm + τ • cdot) * f (r + τ * (2 * av))
        + ‖hv + τ • hdot‖ ^ 2 / (r + τ * (2 * av)) ^ 2 := ⟨_, rfl⟩
  obtain ⟨ρf', hρf'⟩ : ∃ ρf' : ℝ → ℝ, ρf' = fun τ : ℝ =>
      aff σ + GB τ + GQ τ := ⟨_, rfl⟩
  have hposline : ∀ᶠ τ : ℝ in nhds (0 : ℝ), 0 < r + τ * (2 * av) := by
    have hc : ContinuousAt (fun τ : ℝ => r + τ * (2 * av)) 0 := by fun_prop
    have h0 : (0 : ℝ) < (fun τ : ℝ => r + τ * (2 * av)) 0 := by
      show 0 < r + 0 * (2 * av)
      rw [zero_mul, add_zero]; exact hrpos
    exact Filter.Tendsto.eventually hc (eventually_gt_nhds h0)
  have hagree : ∀ᶠ τ : ℝ in nhds (0 : ℝ), psi (Zm + τ • σ) = ρf τ := by
    filter_upwards [hposline] with τ hτ
    rw [hpsi (Zm + τ • σ), hρf]
    show aff (Zm + τ • σ) + Bf (Lc (Zm + τ • σ)) * f ‖Ld (Zm + τ • σ)‖
      + ‖Lh (Zm + τ • σ)‖ ^ 2 / ‖Ld (Zm + τ • σ)‖ ^ 2 = _
    rw [hAffline τ, hLcline τ, hLhline τ, hnormline τ (le_of_lt hτ)]
  have hderline : ∀ᶠ τ : ℝ in nhds (0 : ℝ), HasDerivAt ρf (ρf' τ) τ := by
    filter_upwards [hGB1, hGQ1] with τ hB hQ
    have haff : HasDerivAt (fun t : ℝ => aff Zm + t * aff σ) (aff σ) τ := by
      have h := ((hasDerivAt_id τ).mul_const (aff σ)).const_add (aff Zm)
      rw [one_mul] at h
      exact h
    rw [hρf, hρf']
    exact (haff.add hB).add hQ
  have hsecond : HasDerivAt ρf'
      ((fderiv ℝ (fderiv ℝ Bf) cm cdot cdot * f r
          + 2 * (fderiv ℝ Bf cm cdot) * (f₁ r * (2 * av))
          + Bf cm * (fc * (2 * av) ^ 2))
        + (2 * ‖hdot‖ ^ 2 / r ^ 2 - 8 * (2 * av) * (inner ℝ hv hdot) / r ^ 3
          + 6 * (2 * av) ^ 2 * ‖hv‖ ^ 2 / r ^ 4)) 0 := by
    rw [hρf']
    have h := ((hasDerivAt_const (0 : ℝ) (aff σ)).add hGB2).add hGQ2
    exact h.congr_deriv (by ring)
  -- the Hessian in the direction σ, via the one-variable second derivative
  have hhess := (SecondVariationAlongLine (psi) Zm σ hpsiC2 ρf ρf' _
    hagree hderline hsecond).2
  rw [iteratedFDeriv_two_apply] at hhess
  -- the six pieces of the second variation, bounded one by one
  have hcdn : ‖cdot‖ ≤ K₃ := by rw [hcdot]; exact hcdK
  have hcd0 : (0 : ℝ) ≤ ‖cdot‖ := norm_nonneg _
  have hhdn : ‖hdot‖ ≤ r * K₁ / 2 := by
    rw [hhdot, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith only [hfr0] : (0:ℝ) ≤ (2 : ℝ)⁻¹ * f r)]
    have h1 : (2 : ℝ)⁻¹ * f r * ‖gradient Bf cm‖ ≤ (2 : ℝ)⁻¹ * r * K₁ :=
      mul_le_mul (by linarith only [hfrle]) hgK (norm_nonneg _)
        (by linarith only [hrpos])
    linarith only [h1]
  have hhd0 : (0 : ℝ) ≤ ‖hdot‖ := norm_nonneg _
  have hD2 : |fderiv ℝ (fderiv ℝ Bf) cm cdot cdot| ≤ K₂ * K₃ ^ 2 := by
    have h1 : ‖fderiv ℝ (fderiv ℝ Bf) cm cdot cdot‖
        ≤ ‖fderiv ℝ (fderiv ℝ Bf) cm cdot‖ * ‖cdot‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖fderiv ℝ (fderiv ℝ Bf) cm cdot‖
        ≤ ‖fderiv ℝ (fderiv ℝ Bf) cm‖ * ‖cdot‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h3 : ‖fderiv ℝ (fderiv ℝ Bf) cm‖ ≤ K₂ := hD2n
    have h4 : ‖fderiv ℝ (fderiv ℝ Bf) cm cdot‖ ≤ K₂ * ‖cdot‖ :=
      le_trans h2 (mul_le_mul_of_nonneg_right h3 hcd0)
    have h5 : ‖fderiv ℝ (fderiv ℝ Bf) cm cdot‖ * ‖cdot‖ ≤ (K₂ * ‖cdot‖) * ‖cdot‖ :=
      mul_le_mul_of_nonneg_right h4 hcd0
    have h6 : K₂ * (‖cdot‖ * ‖cdot‖) ≤ K₂ * (K₃ * K₃) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hcdn hcdn hcd0 (le_trans hcd0 hcdn)) hK₂0
    rw [← Real.norm_eq_abs]
    nlinarith only [h1, h5, h6]
  have hD1 : |fderiv ℝ Bf cm cdot| ≤ K₁ * K₃ := by
    have h1 : ‖fderiv ℝ Bf cm cdot‖ ≤ ‖fderiv ℝ Bf cm‖ * ‖cdot‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖fderiv ℝ Bf cm‖ ≤ K₁ := hD1n
    have h3 : ‖fderiv ℝ Bf cm‖ * ‖cdot‖ ≤ K₁ * K₃ :=
      mul_le_mul h2 hcdn hcd0 hK₁0
    rw [← Real.norm_eq_abs]
    linarith only [h1, h3]
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hrpos
  -- (6b) the first two localizing terms
  have hT1 : fderiv ℝ (fderiv ℝ Bf) cm cdot cdot * f r ≤ 3 / 2 * (K₂ * K₃ ^ 2) := by
    have u1 : fderiv ℝ (fderiv ℝ Bf) cm cdot cdot * f r
        ≤ |fderiv ℝ (fderiv ℝ Bf) cm cdot cdot| * f r :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hfr0
    have u2 : |fderiv ℝ (fderiv ℝ Bf) cm cdot cdot| * f r ≤ (K₂ * K₃ ^ 2) * (3 / 2) :=
      mul_le_mul hD2 (by linarith only [hfrle, hrle]) hfr0
        (le_trans (abs_nonneg _) hD2)
    linarith only [u1, u2]
  have hT2 : 2 * (fderiv ℝ Bf cm cdot) * (f₁ r * (2 * av)) ≤ 4 * B_out * K₁ * K₃ := by
    have hav2 : 0 < 2 * av := by linarith only [hav0]
    have u0 : 0 ≤ f₁ r * (2 * av) := mul_nonneg hf₁0 (le_of_lt hav2)
    have u1 : f₁ r * (2 * av) ≤ 2 * B_out := by
      have w1 : f₁ r * (2 * av) ≤ 1 * (2 * av) :=
        mul_le_mul_of_nonneg_right hf₁le (le_of_lt hav2)
      have w2 : 2 * av ≤ 2 * B_out := by linarith only [haub]
      linarith only [w1, w2]
    have u2 : (fderiv ℝ Bf cm cdot) * (f₁ r * (2 * av))
        ≤ (K₁ * K₃) * (2 * B_out) :=
      mul_le_mul (le_trans (le_abs_self _) hD1) u1 u0 (le_trans (abs_nonneg _) hD1)
    linarith only [u2]
  -- (6b) the dominant term, which carries the blow-up of `f''`
  have hT3 : Bf cm * (fc * (2 * av) ^ 2) ≤ -(3 * δ ^ 3 / (256 * Real.sqrt r)) := by
    have hX : δ ^ 3 / 32 ≤ Bf cm * av ^ 2 := by
      have w1 : (δ / 4) ^ 2 ≤ av ^ 2 := by
        nlinarith only [halow, hδ]
      have w2 : δ / 2 * ((δ / 4) ^ 2) ≤ Bf cm * av ^ 2 := by
        nlinarith only [hBfge, w1, hδ, halow]
      linarith only [w2]
    have hc0 : (0 : ℝ) ≤ (Real.sqrt r)⁻¹ := le_of_lt (inv_pos.mpr hs0)
    have he1 : Bf cm * (fc * (2 * av) ^ 2)
        = -(3 / 8) * (Real.sqrt r)⁻¹ * (Bf cm * av ^ 2) := by
      rw [hfcdef]; field_simp; ring
    have he2 : 3 * δ ^ 3 / (256 * Real.sqrt r)
        = 3 / 256 * (Real.sqrt r)⁻¹ * δ ^ 3 := by
      field_simp
    have hkey : 0 ≤ (Real.sqrt r)⁻¹ * (Bf cm * av ^ 2 - δ ^ 3 / 32) :=
      mul_nonneg hc0 (by linarith only [hX])
    rw [he1, he2]
    nlinarith only [hkey]
  -- (6a) the three penalty terms
  have hT4 : 2 * ‖hdot‖ ^ 2 / r ^ 2 ≤ K₁ ^ 2 / 2 := by
    have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hrpos 2
    have hsq : ‖hdot‖ ^ 2 ≤ (r * K₁ / 2) ^ 2 := by
      nlinarith only [hhdn, hhd0]
    rw [div_le_iff₀ hr2]
    nlinarith only [hsq]
  have hr3 : (0 : ℝ) < r ^ 3 := pow_pos hrpos 3
  have hT5 : -(8 * (2 * av) * (inner ℝ hv hdot : ℝ) / r ^ 3)
      ≤ 16 * B_out * C * K₁ := by
    have hin : |(inner ℝ hv hdot : ℝ)| ≤ ‖hv‖ * ‖hdot‖ := abs_real_inner_le_norm hv hdot
    have hnn : ‖hv‖ * ‖hdot‖ ≤ (2 * C * r ^ 2) * (r * K₁ / 2) :=
      mul_le_mul hhvbd hhdn hhd0 (by nlinarith only [hCpos, hrpos])
    have hIb : -(inner ℝ hv hdot : ℝ) ≤ C * K₁ * r ^ 3 := by
      have w := (abs_le.mp hin).1
      nlinarith only [w, hnn]
    have hIb0 : 0 ≤ C * K₁ * r ^ 3 :=
      mul_nonneg (mul_nonneg (le_of_lt hCpos) hK₁0) (le_of_lt hr3)
    have he : -(8 * (2 * av) * (inner ℝ hv hdot : ℝ) / r ^ 3)
        = 16 * av * (-(inner ℝ hv hdot : ℝ)) / r ^ 3 := by ring
    rw [he, div_le_iff₀ hr3]
    have w1 : 16 * av * (-(inner ℝ hv hdot : ℝ)) ≤ 16 * av * (C * K₁ * r ^ 3) :=
      mul_le_mul_of_nonneg_left hIb (by linarith only [hav0])
    have w2 : av * (16 * (C * K₁ * r ^ 3)) ≤ B_out * (16 * (C * K₁ * r ^ 3)) :=
      mul_le_mul_of_nonneg_right haub (by linarith only [hIb0])
    nlinarith only [w1, w2]
  have hT6 : 6 * (2 * av) ^ 2 * ‖hv‖ ^ 2 / r ^ 4 ≤ 96 * B_out ^ 2 * C ^ 2 := by
    have hr4 : (0 : ℝ) < r ^ 4 := by
      have := pow_pos hrpos 4; linarith only [this]
    have hav2 : (2 * av) ^ 2 ≤ 4 * B_out ^ 2 := by
      nlinarith only [haub, hav0]
    have hhv2 : ‖hv‖ ^ 2 ≤ 4 * C ^ 2 * r ^ 4 := by
      nlinarith only [hhvbd, norm_nonneg hv]
    rw [div_le_iff₀ hr4]
    have w : (2 * av) ^ 2 * ‖hv‖ ^ 2 ≤ (4 * B_out ^ 2) * (4 * C ^ 2 * r ^ 4) :=
      mul_le_mul hav2 hhv2 (sq_nonneg _) (by positivity)
    nlinarith only [w]  -- eq:tpf-neg
  rw [hhess, hMc]
  linarith only [hT1, hT2, hT3, hT4, hT5, hT6]
