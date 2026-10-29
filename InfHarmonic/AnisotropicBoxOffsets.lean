module

public import InfHarmonic.Preamble

@[expose] public section
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Claim 4a of the nonaffine-limit argument: the image of a box `|x|, |t| ≤ K` under the
anisotropic map `(x,t) ↦ r Φ(s x, t)` has axial offset at most `R r / 4` and transverse
offset at most `θ R r / 4` relative to any unit direction `n` within `C θ` of the frame
direction `Φ(e_b)`, provided `s √Λ = θ`, `s ≤ 1`, `1 ≤ K`, `16 K < R` and
`K(Λ^{-1/2} + C) < R/4`, where `Λ = 32`.  The quarter factors are what the shifted cylinder comparison
consumes; cylinder membership follows a fortiori. -/
theorem AnisotropicBoxOffsets
    (Φ : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ))
    (rb sl th K R Cb : ℝ) (n : WithLp 2 (F × ℝ)) (x : F) (t : ℝ)
    (hrb : 0 < rb) (hth : 0 ≤ th) (hsl0 : 0 ≤ sl) (hsl1 : sl ≤ 1)
    (hslth : sl * Real.sqrt 32 = th) (hK : 1 ≤ K) (hCb : 0 ≤ Cb)
    (hn : ‖n‖ = 1)
    (hdir : ‖Φ (toLp 2 ((0 : F), (1 : ℝ))) - n‖ ≤ Cb * th)
    (h16 : 16 * K < R)
    (hRR : K * ((Real.sqrt 32)⁻¹ + Cb) < R / 4)
    (hx : ‖x‖ ≤ K) (ht : |t| ≤ K) :
    |(inner ℝ n (rb • Φ (toLp 2 (sl • x, t))) : ℝ)| ≤ R * rb / 4 ∧
    ‖rb • Φ (toLp 2 (sl • x, t))
        - (inner ℝ n (rb • Φ (toLp 2 (sl • x, t))) : ℝ) • n‖ ≤ th * (R * rb) / 4 := by
  have hR0 : (0 : ℝ) < R := by linarith only [hK, h16]
  have hRr0 : (0 : ℝ) < R * rb := mul_pos hR0 hrb
  -- the displacement and its norm
  obtain ⟨hh, hhdef⟩ : ∃ hh : WithLp 2 (F × ℝ), hh = rb • Φ (toLp 2 (sl • x, t)) :=
    ⟨_, rfl⟩
  have hnx : ‖(toLp 2 (x, (0 : ℝ)) : WithLp 2 (F × ℝ))‖ = ‖x‖ := by
    rw [WithLp.prod_norm_eq_of_L2]
    show Real.sqrt (‖x‖ ^ 2 + ‖(0 : ℝ)‖ ^ 2) = ‖x‖
    rw [norm_zero]
    simp [Real.sqrt_sq (norm_nonneg x)]
  have hnslx : ‖(toLp 2 (sl • x, t) : WithLp 2 (F × ℝ))‖ ≤ sl * ‖x‖ + |t| := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (toLp 2 (sl • x, t) : WithLp 2 (F × ℝ))
    have he1 : ‖(toLp 2 (sl • x, t) : WithLp 2 (F × ℝ)).fst‖ = sl * ‖x‖ := by
      show ‖sl • x‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsl0]
    have he2 : ‖(toLp 2 (sl • x, t) : WithLp 2 (F × ℝ)).snd‖ = |t| := rfl
    rw [he1, he2] at hsq
    nlinarith only [hsq, mul_nonneg hsl0 (norm_nonneg x), abs_nonneg t,
      norm_nonneg (toLp 2 (sl • x, t) : WithLp 2 (F × ℝ))]
  have hhn : ‖hh‖ ≤ 2 * K * rb := by
    rw [hhdef, norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hrb),
      LinearIsometryEquiv.norm_map]
    have h1 : sl * ‖x‖ + |t| ≤ 2 * K := by
      have h2 : sl * ‖x‖ ≤ ‖x‖ := by
        nlinarith only [hsl1, hsl0, norm_nonneg x]
      linarith only [h2, hx, ht]
    have h2 : rb * ‖(toLp 2 (sl • x, t) : WithLp 2 (F × ℝ))‖ ≤ rb * (2 * K) :=
      mul_le_mul_of_nonneg_left (le_trans hnslx h1) (le_of_lt hrb)
    linarith only [h2]
  rw [← hhdef]
  -- the AXIAL bound
  have hax : |(inner ℝ n hh : ℝ)| ≤ R * rb / 4 := by
    have hcs : |(inner ℝ n hh : ℝ)| ≤ ‖hh‖ := by
      have hb := abs_real_inner_le_norm n hh
      rwa [hn, one_mul] at hb
    have h1 : 16 * K * rb < R * rb := mul_lt_mul_of_pos_right h16 hrb
    linarith only [hcs, hhn, h1, hRr0]
  refine ⟨hax, ?_⟩
  -- the projection inequality: `⟪n,h⟫ n` is the closest multiple of `n` to `h`
  have hproj : ∀ (u : ℝ), ‖hh - (inner ℝ n hh : ℝ) • n‖ ≤ ‖hh - u • n‖ := by
    intro u
    obtain ⟨sv, hsvdef⟩ : ∃ sv : ℝ, sv = (inner ℝ n hh : ℝ) := ⟨_, rfl⟩
    rw [← hsvdef]
    have horth : (inner ℝ (hh - sv • n) ((sv - u) • n) : ℝ) = 0 := by
      rw [real_inner_smul_right, inner_sub_left, real_inner_smul_left,
        real_inner_self_eq_norm_sq, hn]
      have hhe : (inner ℝ hh n : ℝ) = sv := by rw [hsvdef, real_inner_comm]
      rw [hhe]
      ring
    have hsum : hh - u • n = (hh - sv • n) + ((sv - u) • n) := by
      rw [sub_smul]; abel
    have hpyth := norm_add_sq_real (hh - sv • n) ((sv - u) • n)
    rw [← hsum, horth] at hpyth
    have h1 : ‖hh - sv • n‖ ^ 2 ≤ ‖hh - u • n‖ ^ 2 := by
      linarith only [hpyth, sq_nonneg ‖(sv - u) • n‖]
    exact le_of_pow_le_pow_left₀ (by norm_num) (norm_nonneg _) h1
  -- the TRANSVERSE bound: split the displacement in the frame
  obtain ⟨ee, heedef⟩ : ∃ ee : WithLp 2 (F × ℝ),
      ee = Φ (toLp 2 ((0 : F), (1 : ℝ))) := ⟨_, rfl⟩
  have hsplit : (toLp 2 (sl • x, t) : WithLp 2 (F × ℝ))
      = sl • toLp 2 (x, (0 : ℝ)) + t • toLp 2 ((0 : F), (1 : ℝ)) := by
    have h1 : (ofLp (sl • (toLp 2 (x, (0 : ℝ)) : WithLp 2 (F × ℝ))
        + t • toLp 2 ((0 : F), (1 : ℝ)))) = (sl • x, t) := by simp
    calc (toLp 2 (sl • x, t) : WithLp 2 (F × ℝ))
        = toLp 2 (ofLp (sl • (toLp 2 (x, (0 : ℝ)) : WithLp 2 (F × ℝ))
          + t • toLp 2 ((0 : F), (1 : ℝ)))) := by rw [h1]
      _ = _ := rfl
  have hdecomp : hh = (rb * sl) • Φ (toLp 2 (x, (0 : ℝ))) + (rb * t) • ee := by
    rw [hhdef, hsplit, map_add, map_smul, map_smul, heedef, smul_add, smul_smul,
      smul_smul]
  have hrw : hh - (rb * t) • n
      = (rb * sl) • Φ (toLp 2 (x, (0 : ℝ))) + (rb * t) • (ee - n) := by
    rw [hdecomp, smul_sub]; abel
  have hb1 : ‖(rb * sl) • Φ (toLp 2 (x, (0 : ℝ)))‖ = rb * sl * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (le_of_lt hrb) hsl0),
      LinearIsometryEquiv.norm_map, hnx]
  have hb2 : ‖(rb * t) • (ee - n)‖ = rb * |t| * ‖ee - n‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg (le_of_lt hrb)]
  have hdir2 : ‖ee - n‖ ≤ Cb * th := by rw [heedef]; exact hdir
  have hs320 : (0 : ℝ) < Real.sqrt 32 := Real.sqrt_pos.mpr (by norm_num)
  have hslv : sl = (Real.sqrt 32)⁻¹ * th := by
    rw [← hslth]; field_simp
  have hsum2 : ‖hh - (rb * t) • n‖
      ≤ rb * K * ((Real.sqrt 32)⁻¹ + Cb) * th := by
    have htri : ‖hh - (rb * t) • n‖
        ≤ ‖(rb * sl) • Φ (toLp 2 (x, (0 : ℝ)))‖ + ‖(rb * t) • (ee - n)‖ := by
      rw [hrw]; exact norm_add_le _ _
    rw [hb1, hb2] at htri
    have hfac : (0 : ℝ) ≤ rb * ((Real.sqrt 32)⁻¹ * th) :=
      mul_nonneg (le_of_lt hrb) (mul_nonneg (le_of_lt (inv_pos.mpr hs320)) hth)
    have h1 : rb * sl * ‖x‖ ≤ rb * ((Real.sqrt 32)⁻¹ * th) * K := by
      rw [hslv]
      exact mul_le_mul_of_nonneg_left hx hfac
    have hA : rb * |t| ≤ rb * K := mul_le_mul_of_nonneg_left ht (le_of_lt hrb)
    have hB : (0 : ℝ) ≤ Cb * th := mul_nonneg hCb hth
    have h2a : rb * |t| * ‖ee - n‖ ≤ rb * |t| * (Cb * th) :=
      mul_le_mul_of_nonneg_left hdir2 (mul_nonneg (le_of_lt hrb) (abs_nonneg t))
    have h2b : rb * |t| * (Cb * th) ≤ rb * K * (Cb * th) :=
      mul_le_mul_of_nonneg_right hA hB
    have h2 : rb * |t| * ‖ee - n‖ ≤ rb * K * (Cb * th) := le_trans h2a h2b
    nlinarith only [htri, h1, h2]
  have hkey : rb * K * ((Real.sqrt 32)⁻¹ + Cb) * th ≤ th * (R * rb) / 4 := by
    have hfac : (0 : ℝ) ≤ rb * th := mul_nonneg (le_of_lt hrb) hth
    nlinarith only [hRR, hfac, hrb, hth]
  linarith only [hproj (rb * t), hsum2, hkey]
