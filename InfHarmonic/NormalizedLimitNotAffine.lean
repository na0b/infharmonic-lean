module

public import InfHarmonic.IsBadScaleData
public import InfHarmonic.IsSpaceTimeAffine
public import InfHarmonic.FitCylinderToNormalizedBox

@[expose] public section
set_option maxHeartbeats 400000
open Metric Set Filter Topology WithLp

/-- Step 12 of Proposition 3.6: the limit of the normalized blow-up family is
not space-time affine.  An affine limit would make the rescaled slope realize a
cylinder fit of parameter `lam i` -- not `32 lam i` -- at `(z i, r i)` for all
large `i`, contradicting the bad-scale hypothesis.  The normalization
`vlim 0 = 0` forces the affine constant to vanish, and every point of every such
cylinder has normalized coordinates in one fixed box. -/
theorem NormalizedLimitNotAffine (d : ℕ) (r lam : ℕ → ℝ)
    (U : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ) (z : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (Φ : ℕ → (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
    (v : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ) (Zi : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (cc : ℕ → ℝ) (L : ℝ) (hL0 : (0 : ℝ) ≤ L) (i₁ i₂ : ℕ) (hi₂i₁ : i₁ ≤ i₂)
    (psi : ℕ → ℕ) (vlim : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ)
    (hlam0 : ∀ i, 0 < lam i) (hlamlim : Tendsto lam atTop (𝓝 0))
    (hr0 : ∀ i, 0 < r i)
    (hbad : ∀ i, ¬ ∃ P, IsCylinderFit (U i) (z i) (r i) (lam i) P)
    (hZidef : Zi = fun i w =>
      z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))
    (hbasenorm : ∀ i ≥ i₂, 1 / 2 ≤ cc i ∧ cc i ≤ L + 1)
    (htail1 : ∀ i ≥ i₂, 32 * lam i ≤ 1)
    (horigin : ∀ i ≥ i₁, v i 0 = 0)
    (hincrement : ∀ i ≥ i₁,
      ∀ (w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (h : EuclideanSpace ℝ (Fin d)) (l : ℝ)
        (pp : EuclideanSpace ℝ (Fin d)) (qp : ℝ) (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
        Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • pp, cc i * (1 + lam i * qp))) →
        U i (Zi i (w + toLp 2 (h, l))) - U i (Zi i w)
            - (inner ℝ Q (Zi i (w + toLp 2 (h, l)) - Zi i w) : ℝ)
          = r i * cc i * lam i *
            (v i (w + toLp 2 (h, l)) - v i w - (inner ℝ pp h : ℝ) - qp * l))
    (hpsimono : StrictMono psi)
    (hvconv : ∀ K : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), IsCompact K →
      TendstoUniformlyOn (fun j => v (psi j)) vlim atTop K)
    (hv0 : vlim 0 = 0) :
    ¬ IsSpaceTimeAffine vlim := by
  rintro ⟨p, qq, cst, haff⟩
  -- eq:nl-v0 forces the constant to vanish
  have hc0 : cst = 0 := by
    have h := haff 0
    rw [hv0] at h
    have h1 : (inner ℝ p (ofLp (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))).1 : ℝ)
        = 0 := by simp
    have h2 : (ofLp (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))).2 = (0 : ℝ) := rfl
    rw [h1, h2] at h
    linarith only [h]
  have hvaff : ∀ y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      vlim y = (inner ℝ p (ofLp y).1 : ℝ) + qq * (ofLp y).2 := by
    intro y; rw [haff y, hc0]; ring
  -- THE FIXED BOX.  `FitCylinderToNormalizedBox` gives `‖x‖ ≤ 2‖p‖+1` and
  -- `|t| ≤ 1 + √λ_i ≤ 2`, so every point of every such cylinder has normalized
  -- coordinates in `closedBall 0 (2‖p‖+3)`, independently of `i`.
  obtain ⟨Rad0, hRad0def⟩ : ∃ Rad0 : ℝ, Rad0 = 2 * ‖p‖ + 3 := ⟨_, rfl⟩
  have hRad00 : (0 : ℝ) < Rad0 := by rw [hRad0def]; positivity
  -- the uniform-convergence threshold on that box: `c_i |v_i - v| ≤ 1` needs
  -- `|v_i - v| < 1/(L+1)`, since `c_i ≤ L+1`
  obtain ⟨ju, hju⟩ := Filter.eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp
      (hvconv (closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) Rad0)
        (isCompact_closedBall _ _)) (1 / (L + 1)) (by positivity))
  -- the λ-smallness threshold: `λ_i(|q|+1) ≤ 1/2`, which gives `1 + λ_i q ≥ 1/2`
  obtain ⟨jl, hjl⟩ := Filter.eventually_atTop.mp
    (hlamlim.eventually_lt_const
      (show (0 : ℝ) < 1 / (2 * (|qq| + 1)) by positivity))
  -- ONE index suffices, because `hbad` holds for EVERY index
  obtain ⟨j, hjdef⟩ : ∃ j : ℕ, j = max (max ju jl) i₂ := ⟨_, rfl⟩
  obtain ⟨i, hidef⟩ : ∃ i : ℕ, i = psi j := ⟨_, rfl⟩
  have hji : j ≤ i := by rw [hidef]; exact hpsimono.le_apply
  have hi2 : i₂ ≤ i := le_trans (by rw [hjdef]; exact le_max_right _ _) hji
  have hi1 : i₁ ≤ i := le_trans hi₂i₁ hi2
  have hjuj : ju ≤ j := by
    rw [hjdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hjlj : jl ≤ j := by
    rw [hjdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hr' := hr0 i
  have hlam' := hlam0 i
  have hccb := hbasenorm i hi2
  have hcc1 : (1 : ℝ) / 2 ≤ cc i := hccb.1
  have hcc2 : cc i ≤ L + 1 := hccb.2
  have hcc0' : (0 : ℝ) < cc i := by linarith only [hcc1]
  have hsl0' : (0 : ℝ) < Real.sqrt (lam i) := Real.sqrt_pos.mpr hlam'
  have hlam1 : lam i ≤ 1 := by linarith only [htail1 i hi2, hlam']
  have hsl1 : Real.sqrt (lam i) ≤ 1 := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hlam1
  -- `1/2 ≤ 1 + λ_i q`
  have hlamq : lam i * (|qq| + 1) ≤ 1 / 2 := by
    have hpos : (0 : ℝ) < 2 * (|qq| + 1) := by positivity
    have h1 : lam i < 1 / (2 * (|qq| + 1)) := hjl i (le_trans hjlj hji)
    have h2 : lam i * (2 * (|qq| + 1)) < 1 := by
      rw [← lt_div_iff₀ hpos]; exact h1
    nlinarith only [h2]
  have hA2 : (1 : ℝ) / 2 ≤ 1 + lam i * qq := by
    have h1 : |lam i * qq| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos hlam']
      nlinarith only [hlamq, hlam', abs_nonneg qq, le_abs_self qq]
    have h2 := abs_le.mp h1
    linarith only [h2.1]
  -- `N_i ≥ 1/2`, the hypothesis the box node asks for
  have hN : (1 : ℝ) / 2 ≤ Real.sqrt (lam i * ‖p‖ ^ 2 + (1 + lam i * qq) ^ 2) := by
    have hge : (1 : ℝ) / 4 ≤ lam i * ‖p‖ ^ 2 + (1 + lam i * qq) ^ 2 := by
      nlinarith only [hA2, mul_nonneg (le_of_lt hlam') (sq_nonneg ‖p‖)]
    have hhalf : Real.sqrt ((1 : ℝ) / 4) = 1 / 2 := by
      rw [show (1 : ℝ) / 4 = (1 / 2) ^ 2 from by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    calc (1 : ℝ) / 2 = Real.sqrt (1 / 4) := hhalf.symm
      _ ≤ _ := Real.sqrt_le_sqrt hge
  -- the proposed slope, `P̃_i = c_i Φ_i(√λ_i p, 1 + λ_i q)`
  obtain ⟨Ptil, hPtildef⟩ : ∃ Ptil : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      Ptil = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p,
        cc i * (1 + lam i * qq))) := ⟨_, rfl⟩
  have hPn2 : ‖Ptil‖ ^ 2 = cc i ^ 2 * (lam i * ‖p‖ ^ 2 + (1 + lam i * qq) ^ 2) := by
    rw [hPtildef, LinearIsometryEquiv.norm_map]
    have hsq := WithLp.prod_norm_sq_eq_of_L2
      (toLp 2 ((cc i * Real.sqrt (lam i)) • p, cc i * (1 + lam i * qq))
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    have he1 : ‖(toLp 2 ((cc i * Real.sqrt (lam i)) • p, cc i * (1 + lam i * qq))
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).fst‖
        = cc i * Real.sqrt (lam i) * ‖p‖ := by
      show ‖(cc i * Real.sqrt (lam i)) • p‖ = _
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (le_of_lt hcc0') (le_of_lt hsl0'))]
    have he2 : ‖(toLp 2 ((cc i * Real.sqrt (lam i)) • p, cc i * (1 + lam i * qq))
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).snd‖
        = |cc i * (1 + lam i * qq)| := rfl
    rw [he1, he2, sq_abs] at hsq
    rw [hsq]
    have hss : Real.sqrt (lam i) * Real.sqrt (lam i) = lam i :=
      Real.mul_self_sqrt (le_of_lt hlam')
    linear_combination (cc i ^ 2 * ‖p‖ ^ 2) * hss
  -- `Z_i` is a bijection of the normalized coordinates onto space-time
  have hsurj : ∀ Z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ∃ w, Zi i w = Z := by
    intro Z
    obtain ⟨hh, hhdef⟩ : ∃ hh : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        hh = (Φ i).symm ((r i)⁻¹ • (Z - z i)) := ⟨_, rfl⟩
    refine ⟨toLp 2 ((Real.sqrt (lam i))⁻¹ • (ofLp hh).1, (ofLp hh).2), ?_⟩
    have hid : (toLp 2 (Real.sqrt (lam i) • ((Real.sqrt (lam i))⁻¹ • (ofLp hh).1),
        (ofLp hh).2) : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) = hh := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hsl0'), one_smul]
    rw [hZidef]
    show z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) •
        ((Real.sqrt (lam i))⁻¹ • (ofLp hh).1), (ofLp hh).2)) = Z
    rw [hid, hhdef, LinearIsometryEquiv.apply_symm_apply, smul_smul,
      mul_inv_cancel₀ (ne_of_gt hr'), one_smul]
    abel
  -- `λ_i` is good for `U_i` at `(z_i, r_i)`, contradicting `hbad`
  refine hbad i ⟨Ptil, ?_, ?_⟩
  · -- the slope is nonzero: `‖P̃_i‖ = c_i N_i ≥ 1/4`
    have hPpos : (0 : ℝ) < ‖Ptil‖ ^ 2 := by
      rw [hPn2]
      have hA4 : (1 : ℝ) / 4 ≤ (1 + lam i * qq) ^ 2 := by nlinarith only [hA2]
      have hinner : (1 : ℝ) / 4 ≤ lam i * ‖p‖ ^ 2 + (1 + lam i * qq) ^ 2 := by
        linarith only [hA4, mul_nonneg (le_of_lt hlam') (sq_nonneg ‖p‖)]
      have h1 : (0 : ℝ) < cc i ^ 2 := pow_pos hcc0' 2
      calc (0 : ℝ) < cc i ^ 2 * (1 / 4) := by linarith only [h1]
        _ ≤ cc i ^ 2 * (lam i * ‖p‖ ^ 2 + (1 + lam i * qq) ^ 2) :=
            mul_le_mul_of_nonneg_left hinner (le_of_lt h1)
    refine norm_ne_zero_iff.mp ?_
    intro h0
    rw [h0] at hPpos
    norm_num at hPpos
  · intro Z hZ
    obtain ⟨w, hw⟩ := hsurj Z
    -- the normalized coordinates of `Z` lie in the fixed box
    have hZmem : z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2))
        ∈ FitCylinder (z i) (r i) (lam i)
          (Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p,
            cc i * (1 + lam i * qq)))) := by
      rw [← hPtildef]
      have hZw : z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1,
          (ofLp w).2)) = Z := by rw [← hw, hZidef]
      rw [hZw]; exact hZ
    obtain ⟨hbx, hbt⟩ := FitCylinderToNormalizedBox (Φ i) (z i) (cc i) (lam i) (r i)
      p (ofLp w).1 qq (ofLp w).2 hcc0' hlam' hr' hN hZmem
    have hwball : w ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) Rad0 := by
      rw [mem_closedBall, dist_zero_right]
      have hsq := WithLp.prod_norm_sq_eq_of_L2 w
      have he1 : ‖w.fst‖ = ‖(ofLp w).1‖ := rfl
      have he2 : ‖w.snd‖ = |(ofLp w).2| := rfl
      rw [he1, he2] at hsq
      have hb1 : ‖(ofLp w).1‖ ≤ 2 * ‖p‖ + 1 := hbx
      have hb2 : |(ofLp w).2| ≤ 2 := by linarith only [hbt, hsl1]
      have hub : ‖w‖ ^ 2 ≤ Rad0 ^ 2 := by
        rw [hRad0def]
        nlinarith only [hsq, hb1, hb2, norm_nonneg (ofLp w).1, abs_nonneg (ofLp w).2,
          norm_nonneg p]
      exact le_of_pow_le_pow_left₀ (by norm_num) (le_of_lt hRad00) hub
    -- THE RESIDUAL IS AN EXACT IDENTITY, by eq:nl-increment at the base point `(0,0)`
    have hy0 : (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
        + toLp 2 ((ofLp w).1, (ofLp w).2) = w := by
      rw [show (toLp 2 ((ofLp w).1, (ofLp w).2)
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) = w from rfl, zero_add]
    have hZ0 : Zi i 0 = z i := by
      rw [hZidef]
      show z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (0 : EuclideanSpace ℝ (Fin d)),
        (0 : ℝ))) = z i
      rw [smul_zero,
        show (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (0 : ℝ))
          : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) = 0 from rfl,
        map_zero, smul_zero, add_zero]
    have hinc := hincrement i hi1 0 (ofLp w).1 (ofLp w).2 p qq Ptil hPtildef
    rw [hy0, hZ0, horigin i hi1, hw] at hinc
    -- the bracket is `v_i - v` by the affineness assumption
    have hbr : v i w - 0 - (inner ℝ p (ofLp w).1 : ℝ) - qq * (ofLp w).2
        = v i w - vlim w := by rw [hvaff w]; ring
    rw [hbr] at hinc
    rw [hinc]
    -- the threshold: `c_i |v_i - v| ≤ 1` on the box, from uniform convergence
    have hdist : dist (vlim w) (v (psi j) w) < 1 / (L + 1) := hju j hjuj w hwball
    have hvd : |v i w - vlim w| < 1 / (L + 1) := by
      rw [hidef, show |v (psi j) w - vlim w| = dist (vlim w) (v (psi j) w) from by
        rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]]
      exact hdist
    have hL1 : (0 : ℝ) < L + 1 := by linarith only [hL0]
    have hkey : cc i * |v i w - vlim w| ≤ 1 := by
      have h1 : cc i * |v i w - vlim w| ≤ (L + 1) * |v i w - vlim w| :=
        mul_le_mul_of_nonneg_right hcc2 (abs_nonneg _)
      have h2 : (L + 1) * |v i w - vlim w| < (L + 1) * (1 / (L + 1)) :=
        mul_lt_mul_of_pos_left hvd hL1
      have h3 : (L + 1) * (1 / (L + 1)) = 1 := by field_simp
      linarith only [h1, h2, h3]
    have habs : |r i * cc i * lam i * (v i w - vlim w)|
        = r i * cc i * lam i * |v i w - vlim w| := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r i * cc i * lam i)]
    rw [habs]
    have hfin : r i * cc i * lam i * |v i w - vlim w| ≤ r i * lam i * 1 := by
      have h1 : (0 : ℝ) < r i * lam i := mul_pos hr' hlam'
      nlinarith only [hkey, h1, abs_nonneg (v i w - vlim w), hcc0']
    nlinarith only [hfin, hr', hlam']
