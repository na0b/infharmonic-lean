module

public import InfHarmonic.FitCylinder

@[expose] public section
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The sheared box of the normalized coordinates sits inside the fitting cylinder of the
normalized fit's own slope.  With `A = 1 + λq'`, `N = (A² + λ‖p'‖²)^{1/2}` and
`n = (√λ p', A)/N`, the exact decomposition
`(√λ h, l) = (l N / A) n + (√λ (h - (p'/A) l), 0)`
splits the mapped increment into an axial part of length at most `(1 + 2λ‖p'‖²/A²) S/2`
and a residual whose transverse projection is at most `√λ S` and whose axial projection is
`O(λ S)`.  A smallness threshold on `λ` in terms of the coefficient bound `C` and nothing
else therefore leaves a strict axial margin, and the transverse bound has a factor `√32`
of room. -/
theorem ShearedBoxInFitCylinder
    (Φ : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ))
    (zc : WithLp 2 (F × ℝ)) (cb lam S C rb : ℝ) (p' h : F) (q' l : ℝ)
    (hcb : 0 < cb) (hlam : 0 < lam) (hS : 0 < S) (hrb : 0 < rb)
    (hC : ‖p'‖ + |q'| ≤ C)
    (hA : 1 / 2 ≤ 1 + lam * q')
    (hsmall : lam * (C ^ 2 + C + 1) ≤ 1 / 100)
    (hl : |l| ≤ S / 2)
    (hh : ‖h - (l / (1 + lam * q')) • p'‖ ≤ S) :
    zc + rb • Φ (toLp 2 (Real.sqrt lam • h, l))
      ∈ FitCylinder zc (S * rb) (32 * lam)
          (Φ (toLp 2 ((cb * Real.sqrt lam) • p', cb * (1 + lam * q')))) := by
  have hC0 : 0 ≤ C := le_trans (by positivity) hC
  have hp'C : ‖p'‖ ≤ C := by linarith only [hC, abs_nonneg q']
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hslsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt (le_of_lt hlam)
  -- the orthogonal projection shrinks the norm
  have hprojle : ∀ nn x : WithLp 2 (F × ℝ), ‖nn‖ = 1 →
      ‖x - (inner ℝ nn x : ℝ) • nn‖ ≤ ‖x‖ := by
    intro nn x hnn
    obtain ⟨sv, hsvdef⟩ : ∃ sv : ℝ, sv = (inner ℝ nn x : ℝ) := ⟨_, rfl⟩
    rw [← hsvdef]
    have horth : (inner ℝ (x - sv • nn) (sv • nn) : ℝ) = 0 := by
      rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hnn]
      have hxe : (inner ℝ x nn : ℝ) = sv := by rw [hsvdef, real_inner_comm]
      rw [hxe]; ring
    have hsum : x = (x - sv • nn) + sv • nn := by abel
    have hpyth := norm_add_sq_real (x - sv • nn) (sv • nn)
    rw [← hsum, horth] at hpyth
    have h1 : ‖x - sv • nn‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      linarith only [hpyth, sq_nonneg ‖sv • nn‖]
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h1
  -- the frame vector, its length, and the shear residual
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + lam * q' := ⟨_, rfl⟩
  have hA2 : 1 / 2 ≤ A := by rw [hAdef]; exact hA
  have hA0 : 0 < A := by linarith only [hA2]
  obtain ⟨g, hgdef⟩ : ∃ g : F, g = h - (l / A) • p' := ⟨_, rfl⟩
  have hgS : ‖g‖ ≤ S := by rw [hgdef, hAdef]; exact hh
  obtain ⟨e, hedef⟩ : ∃ e : WithLp 2 (F × ℝ), e = toLp 2 (Real.sqrt lam • p', A) := ⟨_, rfl⟩
  obtain ⟨res, hresdef⟩ : ∃ res : WithLp 2 (F × ℝ),
      res = toLp 2 (Real.sqrt lam • g, (0 : ℝ)) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : WithLp 2 (F × ℝ),
      u = toLp 2 (Real.sqrt lam • h, l) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ‖e‖ := ⟨_, rfl⟩
  -- `N² = A² + λ‖p'‖²`, hence `A ≤ N ≤ A(1 + 2λC²)`
  have hNsq : N ^ 2 = lam * ‖p'‖ ^ 2 + A ^ 2 := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (toLp 2 (Real.sqrt lam • p', A)
      : WithLp 2 (F × ℝ))
    have he1 : ‖(toLp 2 (Real.sqrt lam • p', A) : WithLp 2 (F × ℝ)).fst‖
        = Real.sqrt lam * ‖p'‖ := by
      show ‖Real.sqrt lam • p'‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hsl0)]
    have he2 : ‖(toLp 2 (Real.sqrt lam • p', A) : WithLp 2 (F × ℝ)).snd‖ = |A| := rfl
    rw [he1, he2, abs_of_pos hA0] at hsq
    rw [hNdef, hedef, hsq]
    nlinarith only [hslsq, hsl0]
  have hN0 : 0 < N := by
    rw [hNdef, hedef]
    refine norm_pos_iff.mpr ?_
    intro hz
    have : N ^ 2 = 0 := by rw [hNdef, hedef, hz, norm_zero]; ring
    nlinarith only [this, hNsq, hA0, mul_nonneg (le_of_lt hlam) (sq_nonneg ‖p'‖)]
  have hAN : A ≤ N := by
    have h1 : A ^ 2 ≤ N ^ 2 := by
      nlinarith only [hNsq, mul_nonneg (le_of_lt hlam) (sq_nonneg ‖p'‖)]
    exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hN0) h1
  have hNA : N ≤ A * (1 + 2 * (lam * C ^ 2)) := by
    have hpA : ‖p'‖ ≤ 2 * C * A := by nlinarith only [hp'C, hA2, hC0]
    have hlC : 0 ≤ lam * C ^ 2 := mul_nonneg (le_of_lt hlam) (sq_nonneg C)
    have hub : N ^ 2 ≤ (A * (1 + 2 * (lam * C ^ 2))) ^ 2 := by
      have h1 : lam * ‖p'‖ ^ 2 ≤ lam * (4 * C ^ 2 * A ^ 2) := by
        have := mul_le_mul hpA hpA (norm_nonneg p')
          (by nlinarith only [hC0, hA0])
        nlinarith only [this, hlam]
      have h2 : (0 : ℝ) ≤ A ^ 2 * (lam * C ^ 2) ^ 2 :=
        mul_nonneg (sq_nonneg A) (sq_nonneg _)
      nlinarith only [h1, hNsq, h2]
    have hrhs : 0 ≤ A * (1 + 2 * (lam * C ^ 2)) := by nlinarith only [hA0, hlC]
    exact le_of_pow_le_pow_left₀ (by norm_num) hrhs hub
  -- THE EXACT SHEAR DECOMPOSITION
  have hdec : u = (l / A) • e + res := by
    have hc1 : (l / A) • (Real.sqrt lam • p') + Real.sqrt lam • g
        = Real.sqrt lam • h := by
      rw [hgdef, smul_sub, smul_smul, smul_smul,
        show Real.sqrt lam * (l / A) = l / A * Real.sqrt lam from by ring]
      abel
    have hc2 : l / A * A = l := by field_simp
    have h1 : ofLp ((l / A) • (toLp 2 (Real.sqrt lam • p', A) : WithLp 2 (F × ℝ))
        + toLp 2 (Real.sqrt lam • g, (0 : ℝ)))
        = (Real.sqrt lam • h, l) := by
      simp [hc1, hc2]
    rw [hudef, hedef, hresdef]
    calc (toLp 2 (Real.sqrt lam • h, l) : WithLp 2 (F × ℝ))
        = toLp 2 (ofLp ((l / A) • (toLp 2 (Real.sqrt lam • p', A) : WithLp 2 (F × ℝ))
            + toLp 2 (Real.sqrt lam • g, (0 : ℝ)))) := by rw [h1]
      _ = _ := rfl
  -- the slope, its unit vector, and the displacement
  have hPe : (toLp 2 ((cb * Real.sqrt lam) • p', cb * (1 + lam * q')) : WithLp 2 (F × ℝ))
      = cb • e := by
    have h1 : ofLp (cb • (toLp 2 (Real.sqrt lam • p', A) : WithLp 2 (F × ℝ)))
        = ((cb * Real.sqrt lam) • p', cb * (1 + lam * q')) := by
      refine Prod.ext ?_ ?_
      · show cb • (Real.sqrt lam • p') = (cb * Real.sqrt lam) • p'
        rw [smul_smul]
      · show cb • A = cb * (1 + lam * q')
        rw [smul_eq_mul, hAdef]
    rw [hedef]
    calc (toLp 2 ((cb * Real.sqrt lam) • p', cb * (1 + lam * q')) : WithLp 2 (F × ℝ))
        = toLp 2 (ofLp (cb • (toLp 2 (Real.sqrt lam • p', A) : WithLp 2 (F × ℝ)))) := by
          rw [h1]
      _ = _ := rfl
  obtain ⟨nn, hnndef⟩ : ∃ nn : WithLp 2 (F × ℝ), nn = N⁻¹ • Φ e := ⟨_, rfl⟩
  have hnn1 : ‖nn‖ = 1 := by
    rw [hnndef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (inv_pos.mpr hN0)), LinearIsometryEquiv.norm_map, ← hNdef,
      inv_mul_cancel₀ (ne_of_gt hN0)]
  have hunit : ‖Φ (toLp 2 ((cb * Real.sqrt lam) • p', cb * (1 + lam * q')))‖⁻¹
      • Φ (toLp 2 ((cb * Real.sqrt lam) • p', cb * (1 + lam * q'))) = nn := by
    have hcbne : cb ≠ 0 := ne_of_gt hcb
    rw [hPe, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcb,
      LinearIsometryEquiv.norm_map, ← hNdef, hnndef, smul_smul, mul_inv,
      show cb⁻¹ * N⁻¹ * cb = N⁻¹ from by field_simp]
  have hdisp : zc + rb • Φ (toLp 2 (Real.sqrt lam • h, l)) - zc = rb • Φ u := by
    rw [hudef]; abel
  rw [FitCylinder, Set.mem_ofPred_eq, hdisp, hunit]
  -- `Φ e = N • nn`
  have hPhie : Φ e = N • nn := by
    rw [hnndef, smul_smul, mul_inv_cancel₀ (ne_of_gt hN0), one_smul]
  -- the displacement in the frame
  have hDsplit : rb • Φ u = (rb * (l / A) * N) • nn + rb • Φ res := by
    rw [hdec, map_add, map_smul, hPhie]
    module
  -- the residual's length, and the two inner products
  have hresn : ‖res‖ = Real.sqrt lam * ‖g‖ := by
    rw [hresdef, WithLp.prod_norm_eq_of_L2]
    show Real.sqrt (‖Real.sqrt lam • g‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) = _
    rw [norm_zero, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hsl0)]
    simp [Real.sqrt_sq (mul_nonneg (le_of_lt hsl0) (norm_nonneg g))]
  have hiresn : (inner ℝ nn (Φ res) : ℝ) = N⁻¹ * (lam * (inner ℝ p' g : ℝ)) := by
    rw [hnndef, real_inner_smul_left]
    have h1 : (inner ℝ (Φ e) (Φ res) : ℝ) = (inner ℝ e res : ℝ) :=
      LinearIsometryEquiv.inner_map_map Φ e res
    rw [h1, hedef, hresdef, WithLp.prod_inner_apply]
    rw [real_inner_smul_left, real_inner_smul_right]
    simp only [RCLike.inner_apply, conj_trivial]
    linear_combination (N⁻¹ * (inner ℝ p' g : ℝ)) * hslsq
  have hinnpg : |(inner ℝ p' g : ℝ)| ≤ C * S := by
    have hcs := abs_real_inner_le_norm p' g
    have h1 : ‖p'‖ * ‖g‖ ≤ C * S := mul_le_mul hp'C hgS (norm_nonneg g) hC0
    linarith only [hcs, h1]
  -- the AXIAL bound
  have hsig : (inner ℝ nn (rb • Φ u) : ℝ)
      = rb * (l / A) * N + rb * (inner ℝ nn (Φ res) : ℝ) := by
    rw [hDsplit, inner_add_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hnn1]
    ring
  have hax : |(inner ℝ nn (rb • Φ u) : ℝ)| ≤ S * rb := by
    rw [hsig]
    have hlA : |l / A| * N ≤ S / 2 * (1 + 2 * (lam * C ^ 2)) := by
      rw [abs_div, abs_of_pos hA0, div_mul_eq_mul_div, div_le_iff₀ hA0]
      have hlN : |l| * N ≤ S / 2 * N := mul_le_mul_of_nonneg_right hl (le_of_lt hN0)
      have hNAm : S / 2 * N ≤ S / 2 * (A * (1 + 2 * (lam * C ^ 2))) :=
        mul_le_mul_of_nonneg_left hNA (by linarith only [hS])
      nlinarith only [hlN, hNAm]
    have hterm1 : |rb * (l / A) * N| ≤ rb * (S / 2 * (1 + 2 * (lam * C ^ 2))) := by
      have hh1 : |rb * (l / A) * N| = rb * (|l / A| * N) := by
        rw [abs_mul, abs_mul, abs_of_pos hrb, abs_of_pos hN0]; ring
      rw [hh1]
      exact mul_le_mul_of_nonneg_left hlA (le_of_lt hrb)
    have hterm2 : |rb * (inner ℝ nn (Φ res) : ℝ)| ≤ rb * (2 * (lam * (C * S))) := by
      rw [abs_mul, abs_of_pos hrb]
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hrb)
      rw [hiresn, abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hN0)), abs_mul,
        abs_of_pos hlam]
      have hinv2 : N⁻¹ ≤ 2 := by
        rw [inv_le_comm₀ hN0 (by norm_num)]
        linarith only [hAN, hA2]
      have hb : lam * |(inner ℝ p' g : ℝ)| ≤ lam * (C * S) :=
        mul_le_mul_of_nonneg_left hinnpg (le_of_lt hlam)
      have hnn0 : (0 : ℝ) ≤ lam * |(inner ℝ p' g : ℝ)| :=
        mul_nonneg (le_of_lt hlam) (abs_nonneg _)
      have hcs0 : (0 : ℝ) ≤ lam * (C * S) :=
        mul_nonneg (le_of_lt hlam) (mul_nonneg hC0 (le_of_lt hS))
      calc N⁻¹ * (lam * |(inner ℝ p' g : ℝ)|)
          ≤ N⁻¹ * (lam * (C * S)) := mul_le_mul_of_nonneg_left hb
            (le_of_lt (inv_pos.mpr hN0))
        _ ≤ 2 * (lam * (C * S)) := mul_le_mul_of_nonneg_right hinv2 hcs0
    have hmargin : S / 2 * (1 + 2 * (lam * C ^ 2)) + 2 * (lam * (C * S)) ≤ S := by
      have h1 : lam * C ^ 2 ≤ 1 / 100 := by
        nlinarith only [hsmall, hlam, hC0]
      have h2 : lam * C ≤ 1 / 100 := by
        nlinarith only [hsmall, hlam, hC0]
      nlinarith only [h1, h2, hS]
    have hsplit := abs_add_le (rb * (l / A) * N) (rb * (inner ℝ nn (Φ res) : ℝ))
    have hfin : rb * (S / 2 * (1 + 2 * (lam * C ^ 2))) + rb * (2 * (lam * (C * S)))
        ≤ S * rb := by
      nlinarith only [hmargin, hrb]
    linarith only [hsplit, hterm1, hterm2, hfin]
  refine ⟨hax, ?_⟩
  -- the TRANSVERSE bound
  have htr : rb • Φ u - (inner ℝ nn (rb • Φ u) : ℝ) • nn
      = rb • (Φ res - (inner ℝ nn (Φ res) : ℝ) • nn) := by
    rw [hsig, hDsplit, smul_sub, smul_smul, add_smul]
    abel
  rw [htr, norm_smul, Real.norm_eq_abs, abs_of_pos hrb]
  have hpr : ‖Φ res - (inner ℝ nn (Φ res) : ℝ) • nn‖ ≤ Real.sqrt lam * S := by
    refine le_trans (hprojle nn (Φ res) hnn1) ?_
    rw [LinearIsometryEquiv.norm_map, hresn]
    exact mul_le_mul_of_nonneg_left hgS (le_of_lt hsl0)
  have hroom : Real.sqrt lam * S ≤ Real.sqrt (32 * lam) * S := by
    refine mul_le_mul_of_nonneg_right ?_ (le_of_lt hS)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32) lam]
    have h32 : (1 : ℝ) ≤ Real.sqrt 32 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith only [h32, hsl0]
  calc rb * ‖Φ res - (inner ℝ nn (Φ res) : ℝ) • nn‖
      ≤ rb * (Real.sqrt (32 * lam) * S) :=
        mul_le_mul_of_nonneg_left (le_trans hpr hroom) (le_of_lt hrb)
    _ = Real.sqrt (32 * lam) * (S * rb) := by ring
