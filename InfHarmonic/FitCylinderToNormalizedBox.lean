import InfHarmonic.FitCylinder
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The converse inclusion to the sheared-box one: a point of the fitting cylinder of the
anisotropic slope `Φ(c√λ p, c(1+λq))`, read in normalized coordinates `(x,t)` through
`z + r Φ(√λ x, t)`, lies in ONE FIXED BOX.  With `A = 1 + λq` and
`N = (λ‖p‖² + A²)^{1/2}`, the cylinder point is `σ e + (residual)` with `|σ| ≤ 1/N`, and the
two bounds come from two SEPARATE uses of `N`: `|t| ≤ 1 + √λ` needs only `N ≥ |A|`, which is
immediate from `N² = λ‖p‖² + A² ≥ A²`, whereas `‖x‖ ≤ 2‖p‖ + 1` needs the hypothesis
`N ≥ 1/2`. -/
theorem FitCylinderToNormalizedBox
    (Φ : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ))
    (zc : WithLp 2 (F × ℝ)) (cb lam rb : ℝ) (p x : F) (q t : ℝ)
    (hcb : 0 < cb) (hlam : 0 < lam) (hrb : 0 < rb)
    (hN : 1 / 2 ≤ Real.sqrt (lam * ‖p‖ ^ 2 + (1 + lam * q) ^ 2))
    (hmem : zc + rb • Φ (toLp 2 (Real.sqrt lam • x, t))
      ∈ FitCylinder zc rb lam
          (Φ (toLp 2 ((cb * Real.sqrt lam) • p, cb * (1 + lam * q))))) :
    ‖x‖ ≤ 2 * ‖p‖ + 1 ∧ |t| ≤ 1 + Real.sqrt lam := by
  have hsl0 : 0 < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hslsq : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt (le_of_lt hlam)
  -- the frame vector and its length
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 1 + lam * q := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : WithLp 2 (F × ℝ), e = toLp 2 (Real.sqrt lam • p, A) := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u : WithLp 2 (F × ℝ), u = toLp 2 (Real.sqrt lam • x, t) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ, N = ‖e‖ := ⟨_, rfl⟩
  have hNsq : N ^ 2 = lam * ‖p‖ ^ 2 + A ^ 2 := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2 (toLp 2 (Real.sqrt lam • p, A)
      : WithLp 2 (F × ℝ))
    have he1 : ‖(toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ)).fst‖
        = Real.sqrt lam * ‖p‖ := by
      show ‖Real.sqrt lam • p‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hsl0)]
    have he2 : ‖(toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ)).snd‖ = |A| := rfl
    rw [he1, he2, sq_abs] at hsq
    rw [hNdef, hedef, hsq]
    nlinarith only [hslsq, hsl0]
  have hNnn : (0 : ℝ) ≤ N := by rw [hNdef]; exact norm_nonneg e
  have hNval : N = Real.sqrt (lam * ‖p‖ ^ 2 + (1 + lam * q) ^ 2) := by
    rw [← hAdef, ← hNsq, Real.sqrt_sq hNnn]
  have hN2 : 1 / 2 ≤ N := by rw [hNval]; exact hN
  have hN0 : 0 < N := by linarith only [hN2]
  have hAN : |A| ≤ N := by
    have h1 : A ^ 2 ≤ N ^ 2 := by
      nlinarith only [hNsq, mul_nonneg (le_of_lt hlam) (sq_nonneg ‖p‖)]
    have h2 : |A| ^ 2 ≤ N ^ 2 := by rw [sq_abs]; exact h1
    exact le_of_pow_le_pow_left₀ (by norm_num) hNnn h2
  -- the slope's unit vector
  have hPe : (toLp 2 ((cb * Real.sqrt lam) • p, cb * (1 + lam * q)) : WithLp 2 (F × ℝ))
      = cb • e := by
    have h1 : ofLp (cb • (toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ)))
        = ((cb * Real.sqrt lam) • p, cb * (1 + lam * q)) := by
      refine Prod.ext ?_ ?_
      · show cb • (Real.sqrt lam • p) = (cb * Real.sqrt lam) • p
        rw [smul_smul]
      · show cb • A = cb * (1 + lam * q)
        rw [smul_eq_mul, hAdef]
    rw [hedef]
    calc (toLp 2 ((cb * Real.sqrt lam) • p, cb * (1 + lam * q)) : WithLp 2 (F × ℝ))
        = toLp 2 (ofLp (cb • (toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ)))) := by
          rw [h1]
      _ = _ := rfl
  obtain ⟨nn, hnndef⟩ : ∃ nn : WithLp 2 (F × ℝ), nn = N⁻¹ • Φ e := ⟨_, rfl⟩
  have hnn1 : ‖nn‖ = 1 := by
    rw [hnndef, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (le_of_lt (inv_pos.mpr hN0)), LinearIsometryEquiv.norm_map, ← hNdef,
      inv_mul_cancel₀ (ne_of_gt hN0)]
  have hunit : ‖Φ (toLp 2 ((cb * Real.sqrt lam) • p, cb * (1 + lam * q)))‖⁻¹
      • Φ (toLp 2 ((cb * Real.sqrt lam) • p, cb * (1 + lam * q))) = nn := by
    have hcbne : cb ≠ 0 := ne_of_gt hcb
    rw [hPe, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hcb,
      LinearIsometryEquiv.norm_map, ← hNdef, hnndef, smul_smul, mul_inv,
      show cb⁻¹ * N⁻¹ * cb = N⁻¹ from by field_simp]
  -- the two membership conditions, in the frame
  have hdisp : zc + rb • Φ (toLp 2 (Real.sqrt lam • x, t)) - zc = rb • Φ u := by
    rw [hudef]; abel
  rw [FitCylinder, Set.mem_ofPred_eq, hdisp, hunit] at hmem
  obtain ⟨hax, htr⟩ := hmem
  -- the axial inner product, and the shear coefficient
  have hieu : (inner ℝ e u : ℝ) = lam * (inner ℝ p x : ℝ) + A * t := by
    rw [hedef, hudef, WithLp.prod_inner_apply]
    rw [real_inner_smul_left, real_inner_smul_right]
    simp only [RCLike.inner_apply, conj_trivial]
    linear_combination (inner ℝ p x : ℝ) * hslsq
  have hinnn : (inner ℝ nn (rb • Φ u) : ℝ) = rb * (N⁻¹ * (inner ℝ e u : ℝ)) := by
    rw [hnndef, real_inner_smul_left, real_inner_smul_right,
      LinearIsometryEquiv.inner_map_map Φ e u]
    ring
  obtain ⟨sg, hsgdef⟩ : ∃ sg : ℝ, sg = (inner ℝ e u : ℝ) / N ^ 2 := ⟨_, rfl⟩
  -- (i) gives `|⟪e,u⟫| ≤ N`, hence `|σ| ≤ 1/N`
  have heuN : |(inner ℝ e u : ℝ)| ≤ N := by
    rw [hinnn, abs_mul, abs_of_pos hrb, abs_mul,
      abs_of_nonneg (le_of_lt (inv_pos.mpr hN0))] at hax
    have h1 : N⁻¹ * |(inner ℝ e u : ℝ)| ≤ 1 := by
      nlinarith only [hax, hrb]
    have h2 : N * (N⁻¹ * |(inner ℝ e u : ℝ)|) ≤ N * 1 :=
      mul_le_mul_of_nonneg_left h1 hNnn
    rw [show N * (N⁻¹ * |(inner ℝ e u : ℝ)|) = (N * N⁻¹) * |(inner ℝ e u : ℝ)| from by ring,
      mul_inv_cancel₀ (ne_of_gt hN0), one_mul, mul_one] at h2
    exact h2
  have hsgN : |sg| * N ≤ 1 := by
    rw [hsgdef, abs_div, abs_of_pos (by positivity : (0 : ℝ) < N ^ 2), div_mul_eq_mul_div,
      div_le_one (by positivity : (0 : ℝ) < N ^ 2)]
    nlinarith only [heuN, hN0]
  -- (ii) gives the residual, which splits componentwise
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hN0
  have hres : rb • Φ u - (inner ℝ nn (rb • Φ u) : ℝ) • nn = rb • Φ (u - sg • e) := by
    have hsc : rb * (N⁻¹ * (inner ℝ e u : ℝ)) * N⁻¹ = rb * sg := by
      rw [hsgdef]; field_simp
    rw [hinnn, hnndef, map_sub, map_smul,
      show (rb * (N⁻¹ * (inner ℝ e u : ℝ))) • (N⁻¹ • Φ e) = (rb * sg) • Φ e from by
        rw [smul_smul, hsc]]
    module
  rw [hres, norm_smul, Real.norm_eq_abs, abs_of_pos hrb] at htr
  have hresn : ‖u - sg • e‖ ≤ Real.sqrt lam := by
    rw [LinearIsometryEquiv.norm_map] at htr
    nlinarith only [htr, hrb, norm_nonneg (u - sg • e)]
  -- the residual in coordinates
  have hcomp : u - sg • e = toLp 2 (Real.sqrt lam • (x - sg • p), t - sg * A) := by
    have h1 : ofLp ((toLp 2 (Real.sqrt lam • x, t) : WithLp 2 (F × ℝ))
        - sg • (toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ)))
        = (Real.sqrt lam • (x - sg • p), t - sg * A) := by
      refine Prod.ext ?_ ?_
      · show Real.sqrt lam • x - sg • (Real.sqrt lam • p) = Real.sqrt lam • (x - sg • p)
        rw [smul_sub, smul_smul, smul_smul,
          show sg * Real.sqrt lam = Real.sqrt lam * sg from by ring]
      · show t - sg • A = t - sg * A
        rw [smul_eq_mul]
    rw [hudef, hedef]
    calc (toLp 2 (Real.sqrt lam • x, t) : WithLp 2 (F × ℝ))
          - sg • (toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ))
        = toLp 2 (ofLp ((toLp 2 (Real.sqrt lam • x, t) : WithLp 2 (F × ℝ))
            - sg • (toLp 2 (Real.sqrt lam • p, A) : WithLp 2 (F × ℝ)))) := rfl
      _ = _ := by rw [h1]
  have hsplit : lam * ‖x - sg • p‖ ^ 2 + (t - sg * A) ^ 2 ≤ lam := by
    have hsq := WithLp.prod_norm_sq_eq_of_L2
      (toLp 2 (Real.sqrt lam • (x - sg • p), t - sg * A) : WithLp 2 (F × ℝ))
    have he1 : ‖(toLp 2 (Real.sqrt lam • (x - sg • p), t - sg * A)
        : WithLp 2 (F × ℝ)).fst‖ = Real.sqrt lam * ‖x - sg • p‖ := by
      show ‖Real.sqrt lam • (x - sg • p)‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hsl0)]
    have he2 : ‖(toLp 2 (Real.sqrt lam • (x - sg • p), t - sg * A)
        : WithLp 2 (F × ℝ)).snd‖ = |t - sg * A| := rfl
    rw [he1, he2, sq_abs] at hsq
    rw [hcomp] at hresn
    have hub : ‖(toLp 2 (Real.sqrt lam • (x - sg • p), t - sg * A)
        : WithLp 2 (F × ℝ))‖ ^ 2 ≤ lam := by
      have h0 := norm_nonneg (toLp 2 (Real.sqrt lam • (x - sg • p), t - sg * A)
        : WithLp 2 (F × ℝ))
      nlinarith only [hresn, h0, hslsq, hsl0]
    rw [hsq] at hub
    nlinarith only [hub, hslsq, hsl0, sq_nonneg ‖x - sg • p‖]
  -- the two conclusions, from the two separate uses of `N`
  refine ⟨?_, ?_⟩
  · have h1 : ‖x - sg • p‖ ≤ 1 := by
      have h2 : ‖x - sg • p‖ ^ 2 ≤ 1 := by
        nlinarith only [hsplit, hlam, sq_nonneg (t - sg * A)]
      nlinarith only [h2, norm_nonneg (x - sg • p)]
    have h3 : ‖sg • p‖ ≤ 2 * ‖p‖ := by
      rw [norm_smul, Real.norm_eq_abs]
      have h4 : |sg| * N ≤ 1 := hsgN
      have h5 : |sg| ≤ 2 := by nlinarith only [h4, hN2, abs_nonneg sg]
      exact mul_le_mul_of_nonneg_right h5 (norm_nonneg p)
    have htri : ‖x‖ ≤ ‖x - sg • p‖ + ‖sg • p‖ := by
      have h := norm_add_le (x - sg • p) (sg • p)
      rw [sub_add_cancel] at h
      exact h
    linarith only [htri, h1, h3]
  · have h1 : |t - sg * A| ≤ Real.sqrt lam := by
      have h2 : (t - sg * A) ^ 2 ≤ lam := by
        nlinarith only [hsplit, hlam, mul_nonneg (le_of_lt hlam) (sq_nonneg ‖x - sg • p‖)]
      have h3 : |t - sg * A| ^ 2 ≤ Real.sqrt lam ^ 2 := by
        rw [sq_abs, Real.sq_sqrt (le_of_lt hlam)]; exact h2
      exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hsl0) h3
    have h4 : |sg * A| ≤ 1 := by
      rw [abs_mul]
      have h5 : |sg| * |A| ≤ |sg| * N := mul_le_mul_of_nonneg_left hAN (abs_nonneg sg)
      linarith only [h5, hsgN]
    have h6 := abs_le.mp h1
    have h7 := abs_le.mp h4
    rw [abs_le]
    constructor
    · linarith only [h6.1, h7.1]
    · linarith only [h6.2, h7.2]
