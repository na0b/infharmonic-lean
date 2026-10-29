module

public import InfHarmonic.Preamble

@[expose] public section
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The two coordinate estimates behind the normalized fit coefficients of (3.8): a
slope `Q` whose unit vector is within `dir` of the frame direction `Φ(e_b)` and whose
norm is within `nrm` of `c` has, in the frame `Φ`, a transverse part controlled by
`dir` alone and a longitudinal part controlled by `nrm` TOGETHER WITH the quadratic
angular error `‖Q‖ dir²/2`.  The two conclusions are stated before dividing by
`c √λ` and `c λ`, so the anisotropic normalization of the coefficients is left to the
caller. -/
theorem NormalizedSlopeCoefficients
    (Φ : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (F × ℝ))
    (cb lam dir nrm : ℝ) (Q : WithLp 2 (F × ℝ))
    (hcb : 0 < cb) (hlam : 0 < lam) (hQ : 0 < ‖Q‖)
    (hdir : ‖‖Q‖⁻¹ • Q - Φ (toLp 2 ((0 : F), (1 : ℝ)))‖ ≤ dir)
    (hnrm : |‖Q‖ - cb| ≤ nrm) :
    ∃ (p' : F) (q' : ℝ),
      Q = Φ (toLp 2 ((cb * Real.sqrt lam) • p', cb * (1 + lam * q'))) ∧
      cb * Real.sqrt lam * ‖p'‖ ≤ ‖Q‖ * dir ∧
      cb * lam * |q'| ≤ nrm + ‖Q‖ * dir ^ 2 / 2 := by
  have hsl0 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam
  have hprod0 : (0 : ℝ) < cb * Real.sqrt lam := mul_pos hcb hsl0
  -- the frame direction, a unit vector because `Φ` is an isometry
  obtain ⟨e, hedef⟩ : ∃ e : WithLp 2 (F × ℝ),
      e = Φ (toLp 2 ((0 : F), (1 : ℝ))) := ⟨_, rfl⟩
  have hen : ‖e‖ = 1 := by
    rw [hedef, LinearIsometryEquiv.norm_map, WithLp.prod_norm_eq_of_L2]
    norm_num
  -- the unit vector of `Q`
  obtain ⟨pu, hpudef⟩ : ∃ pu : WithLp 2 (F × ℝ), pu = ‖Q‖⁻¹ • Q := ⟨_, rfl⟩
  have hpun : ‖pu‖ = 1 := by
    rw [hpudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hQ)]
  have hpe : ‖pu - e‖ ≤ dir := by rw [hpudef, hedef]; exact hdir
  have hw0 : 0 ≤ ‖pu - e‖ := norm_nonneg _
  -- the coordinates of `Q` in the frame `Φ`
  obtain ⟨Qc, hQcdef⟩ : ∃ Qc : WithLp 2 (F × ℝ), Qc = Φ.symm Q := ⟨_, rfl⟩
  obtain ⟨Qx, hQxdef⟩ : ∃ Qx : F, Qx = (ofLp Qc).1 := ⟨_, rfl⟩
  obtain ⟨Qt, hQtdef⟩ : ∃ Qt : ℝ, Qt = (ofLp Qc).2 := ⟨_, rfl⟩
  -- `Q_t = ⟪Q, e⟫`, through the isometry
  have hQt_inner : Qt = (inner ℝ Q e : ℝ) := by
    rw [hQtdef, hedef, hQcdef]
    have h1 : (inner ℝ Q (Φ (toLp 2 ((0 : F), (1 : ℝ)))) : ℝ)
        = (inner ℝ (Φ.symm Q) (toLp 2 ((0 : F), (1 : ℝ))) : ℝ) := by
      have h2 := LinearIsometryEquiv.inner_map_map Φ (Φ.symm Q)
        (toLp 2 ((0 : F), (1 : ℝ)))
      rw [LinearIsometryEquiv.apply_symm_apply] at h2
      exact h2
    rw [h1, WithLp.prod_inner_apply]
    simp
  -- `‖Q_x‖² + Q_t² = ‖Q‖²`, again through the isometry
  have hQcn : ‖Qc‖ = ‖Q‖ := by rw [hQcdef, LinearIsometryEquiv.norm_map]
  have hsumsq : ‖Qx‖ ^ 2 + Qt ^ 2 = ‖Q‖ ^ 2 := by
    have h := WithLp.prod_norm_sq_eq_of_L2 Qc
    rw [hQcn] at h
    rw [show ‖Qc.snd‖ ^ 2 = Qc.snd ^ 2 from by rw [Real.norm_eq_abs, sq_abs]] at h
    rw [hQxdef, hQtdef]
    show ‖Qc.fst‖ ^ 2 + Qc.snd ^ 2 = ‖Q‖ ^ 2
    exact h.symm
  -- the quadratic angular identity `⟪p, e⟫ = 1 - ‖p - e‖²/2`
  have hang : (inner ℝ pu e : ℝ) = 1 - ‖pu - e‖ ^ 2 / 2 := by
    have h := norm_sub_sq_real pu e
    rw [hpun, hen] at h
    linarith only [h]
  have hQpu2 : (inner ℝ Q e : ℝ) = ‖Q‖ * (inner ℝ pu e : ℝ) := by
    rw [hpudef, real_inner_smul_left]
    field_simp
  have hQtval : Qt = ‖Q‖ * (1 - ‖pu - e‖ ^ 2 / 2) := by
    rw [hQt_inner, hQpu2, hang]
  -- the TRANSVERSE estimate: only the direction bound enters
  have hQxb : ‖Qx‖ ≤ ‖Q‖ * dir := by
    have hrhs0 : 0 ≤ ‖Q‖ * dir := mul_nonneg (le_of_lt hQ) (le_trans hw0 hpe)
    have hsq : ‖Qx‖ ^ 2 ≤ (‖Q‖ * ‖pu - e‖) ^ 2 := by
      rw [hQtval] at hsumsq
      have hw4 : (0 : ℝ) ≤ ‖Q‖ ^ 2 * ‖pu - e‖ ^ 4 := by positivity
      nlinarith only [hsumsq, hw4]
    have h1 : ‖Q‖ * ‖pu - e‖ ≤ ‖Q‖ * dir := mul_le_mul_of_nonneg_left hpe (le_of_lt hQ)
    have hsq2 : ‖Qx‖ ^ 2 ≤ (‖Q‖ * dir) ^ 2 := by
      nlinarith only [hsq, h1, mul_nonneg (le_of_lt hQ) hw0, hrhs0]
    exact le_of_pow_le_pow_left₀ (by norm_num) hrhs0 hsq2
  -- the LONGITUDINAL estimate: the norm bound PLUS the quadratic angular error
  have hQtb : |Qt - cb| ≤ nrm + ‖Q‖ * dir ^ 2 / 2 := by
    have hid : Qt - cb = (‖Q‖ - cb) - ‖Q‖ * ‖pu - e‖ ^ 2 / 2 := by
      rw [hQtval]; ring
    have hwsq : ‖pu - e‖ ^ 2 ≤ dir ^ 2 := by
      nlinarith only [hpe, hw0]
    have hw2 : ‖Q‖ * ‖pu - e‖ ^ 2 / 2 ≤ ‖Q‖ * dir ^ 2 / 2 := by
      nlinarith only [hwsq, hQ]
    have hwnn : 0 ≤ ‖Q‖ * ‖pu - e‖ ^ 2 / 2 := by positivity
    have habs := abs_le.mp hnrm
    rw [hid, abs_le]
    constructor <;> linarith only [habs.1, habs.2, hw2, hwnn]
  -- the normalized coefficients
  obtain ⟨p', hp'def⟩ : ∃ p' : F, p' = (cb * Real.sqrt lam)⁻¹ • Qx := ⟨_, rfl⟩
  obtain ⟨q', hq'def⟩ : ∃ q' : ℝ, q' = (Qt - cb) / (cb * lam) := ⟨_, rfl⟩
  refine ⟨p', q', ?_, ?_, ?_⟩
  · -- the slope is rebuilt from its coefficients
    have e1 : (cb * Real.sqrt lam) • p' = Qx := by
      rw [hp'def, smul_smul, mul_inv_cancel₀ (ne_of_gt hprod0), one_smul]
    have e2 : cb * (1 + lam * q') = Qt := by
      have hccne : cb ≠ 0 := ne_of_gt hcb
      have hlamne : lam ≠ 0 := ne_of_gt hlam
      rw [hq'def]
      field_simp
      ring
    rw [e1, e2]
    have e3 : (toLp 2 (Qx, Qt) : WithLp 2 (F × ℝ)) = Qc := by rw [hQxdef, hQtdef]
    rw [e3, hQcdef, LinearIsometryEquiv.apply_symm_apply]
  · have e1 : cb * Real.sqrt lam * ‖p'‖ = ‖Qx‖ := by
      rw [hp'def, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (inv_pos.mpr hprod0)), ← mul_assoc,
        mul_inv_cancel₀ (ne_of_gt hprod0), one_mul]
    rw [e1]
    exact hQxb
  · have e2 : cb * lam * |q'| = |Qt - cb| := by
      rw [hq'def, abs_div, abs_of_pos (mul_pos hcb hlam), mul_div_cancel₀ _
        (ne_of_gt (mul_pos hcb hlam))]
    rw [e2]
    exact hQtb
