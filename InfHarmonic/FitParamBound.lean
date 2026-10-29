import InfHarmonic.IsFitClass
import InfHarmonic.IsCenteredAt
import InfHarmonic.FitComparisonSameCenter
set_option maxHeartbeats 800000
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.4): every fit at a center in the box of size `K`, of any
positive radius `r`, has parameters bounded by `C (L(K) + |log r|)`. -/
theorem FitParamBound (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      (IsCenteredAt C₀ v 0 ∨ IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ)))) →
      ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
        ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
        ∀ r : ℝ, 0 < r → ∀ (p : F) (a : ℝ), IsFit C₀ v z r p a →
          ‖p‖ + |a| ≤ C * ((1 + Real.log K) + |Real.log r|) := by
  have _unused_fd : FiniteDimensional ℝ F := inferInstance
  have hC₀0 : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  -- generic tools
  have habs2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
  have habs3 : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := by
    intro x y
    have h := habs2 x (-y)
    rwa [sub_neg_eq_add, abs_neg] at h
  have hlogsqrt : ∀ x : ℝ, 0 < x → Real.log x ≤ 2 * Real.sqrt x := by
    intro x hx
    have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
    have h1 : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hs
    have h2 : Real.log x = Real.log (Real.sqrt x) + Real.log (Real.sqrt x) := by
      rw [← Real.log_mul (ne_of_gt hs) (ne_of_gt hs), Real.mul_self_sqrt hx.le]
    rw [h2]; linarith
  have hptext : ∀ u w : WithLp 2 (F × ℝ), (ofLp u).1 = (ofLp w).1 →
      (ofLp u).2 = (ofLp w).2 → u = w := by
    intro u w h1 h2
    have h : ofLp u = ofLp w := Prod.ext h1 h2
    calc u = toLp 2 (ofLp u) := (toLp_ofLp 2 u).symm
      _ = toLp 2 (ofLp w) := by rw [h]
      _ = w := toLp_ofLp 2 w
  -- the self-referential choice of `A`, from `log A / A -> 0` in the sharp elementary form
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
  -- the comparison constant, then `A`, then the derived constants
  obtain ⟨C₁, hC₁, hcomp⟩ := FitComparisonSameCenter (F := F) C₀ hC₀
  obtain ⟨A, hA8, hAb⟩ := hAexists (36 * C₁ + 12) (12 * C₁) (by positivity) (by positivity)
  have hApos : (0:ℝ) < A := by linarith
  have hAlog0 : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  have hC₄ : (1:ℝ) ≤ C₁ * (3 + Real.log A) + 1 := by nlinarith [hC₁.le, hAlog0]
  have hAbig : 12 * (C₁ * (3 + Real.log A) + 1) ≤ A := by nlinarith [hAb]
  -- the second compound constant, obtained with exactly the four facts used
  obtain ⟨c, hc0, hc4, hc6, hcinv⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 / 4 ∧ 6 * C₀ * c ≤ 1 / 4
      ∧ 3 * C₀ / c = 12 * C₀ * (1 + 6 * C₀) := by
    have hD : (0:ℝ) < 4 * (1 + 6 * C₀) := by positivity
    have hu : (0:ℝ) < (4 * (1 + 6 * C₀))⁻¹ := by positivity
    have hcc : (4 * (1 + 6 * C₀)) * (4 * (1 + 6 * C₀))⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hD)
    refine ⟨(4 * (1 + 6 * C₀))⁻¹, hu, ?_, ?_, ?_⟩
    · nlinarith [hcc, hu, hC₀0.le]
    · nlinarith [hcc, hu, hC₀0.le]
    · field_simp
      ring
  -- the two derived constants
  obtain ⟨C₄, hC₄1, hC₄def⟩ : ∃ C₄ : ℝ, 1 ≤ C₄ ∧ C₄ = C₁ * (3 + Real.log A) + 1 :=
    ⟨_, hC₄, rfl⟩
  have hA12 : 12 * C₄ ≤ A := by rw [hC₄def]; exact hAbig
  obtain ⟨C₅, hC₅1, hC₅def⟩ : ∃ C₅ : ℝ, 1 ≤ C₅ ∧
      C₅ = C₄ + 6 * C₀ + 12 * C₀ * (1 + 6 * C₀) + 18 * C₀ ^ 2 :=
    ⟨_, by nlinarith [hC₄1, hC₀0.le], rfl⟩
  refine ⟨C₅ + C₁ * (4 + Real.log A), by nlinarith [hC₅1, hC₁.le, hAlog0], ?_⟩
  intro v hclass hcenter K hK z hzx hzt r hr p a hfit
  have hfitsat : ∀ (ζ : WithLp 2 (F × ℝ)) (ρ : ℝ), 0 < ρ →
      ∃ (q : F) (b : ℝ), IsFit C₀ v ζ ρ q b := hclass.2
  -- the centering point, in both cases
  obtain ⟨zc, θ, hθ0, hθ1, hzc1, hzc2, hfitzc⟩ :
      ∃ (zc : WithLp 2 (F × ℝ)) (θ : ℝ), 0 ≤ θ ∧ θ ≤ 1 ∧ (ofLp zc).1 = (0 : F) ∧
        (ofLp zc).2 = θ ∧ IsFit C₀ v zc 1 0 0 := by
    rcases hcenter with h | h
    · exact ⟨0, 0, le_refl 0, zero_le_one, rfl, rfl, h.2⟩
    · exact ⟨toLp 2 ((0:F), (1:ℝ)), 1, zero_le_one, le_refl 1, rfl, rfl, h.2⟩
  -- `L(K)` and the large radius `R`, each obtained with exactly the facts used below
  have hK0 : (0:ℝ) < K := by linarith
  obtain ⟨L, hL1, hLdef⟩ : ∃ L : ℝ, 1 ≤ L ∧ L = 1 + Real.log K := by
    refine ⟨1 + Real.log K, ?_, rfl⟩
    have := Real.log_nonneg (show (1:ℝ) ≤ K by linarith); linarith
  rw [← hLdef]
  obtain ⟨R, hRpos, hR1, hRlog0, hRlog, hR8K, hRmargin⟩ :
      ∃ R : ℝ, 0 < R ∧ 1 < R ∧ 0 ≤ Real.log R ∧ Real.log R ≤ Real.log A + 2 * L
        ∧ 8 * K ≤ R ∧ 3 * (K * (C₄ * L)) ≤ R / 4 := by
    have hpos : (0:ℝ) < A * K * L := by positivity
    have h8K : 8 * K ≤ A * K * L := by
      calc 8 * K = 8 * K * 1 := by ring
        _ ≤ A * K * L := mul_le_mul (mul_le_mul_of_nonneg_right hA8 hK0.le) hL1 zero_le_one
            (by positivity)
    have h1 : (1:ℝ) < A * K * L := by linarith
    have hlog : Real.log (A * K * L) ≤ Real.log A + 2 * L := by
      rw [Real.log_mul (by positivity) (by linarith),
        Real.log_mul (ne_of_gt hApos) (ne_of_gt hK0), hLdef]
      have ha : Real.log K ≤ 1 + Real.log K := by linarith
      have hb : Real.log (1 + Real.log K) ≤ (1 + Real.log K) - 1 :=
        Real.log_le_sub_one_of_pos (by rw [← hLdef]; linarith)
      linarith
    refine ⟨A * K * L, hpos, h1, Real.log_nonneg h1.le, hlog, h8K, ?_⟩
    nlinarith [hA12, mul_nonneg hK0.le (show (0:ℝ) ≤ L by linarith)]
  -- increments from `zc` versus increments from `z`
  have hc1 : ∀ (h : F) (l : ℝ), (ofLp (zc + toLp 2 (h, l))).1 = h := by
    intro h l; show (ofLp zc).1 + h = h; rw [hzc1, zero_add]
  have hc2 : ∀ (h : F) (l : ℝ), (ofLp (zc + toLp 2 (h, l))).2 = θ + l := by
    intro h l; show (ofLp zc).2 + l = θ + l; rw [hzc2]
  have hshift : ∀ (h : F) (l : ℝ),
      zc + toLp 2 ((ofLp z).1 + h, (ofLp z).2 - θ + l) = z + toLp 2 (h, l) := by
    intro h l
    refine hptext _ _ ?_ ?_
    · show (ofLp (zc + toLp 2 ((ofLp z).1 + h, (ofLp z).2 - θ + l))).1 = (ofLp z).1 + h
      rw [hc1]
    · show (ofLp (zc + toLp 2 ((ofLp z).1 + h, (ofLp z).2 - θ + l))).2 = (ofLp z).2 + l
      rw [hc2]; ring
  have hzeq : zc + toLp 2 ((ofLp z).1, (ofLp z).2 - θ) = z := by
    refine hptext _ _ ?_ ?_
    · show (ofLp (zc + toLp 2 ((ofLp z).1, (ofLp z).2 - θ))).1 = (ofLp z).1
      rw [hc1]
    · show (ofLp (zc + toLp 2 ((ofLp z).1, (ofLp z).2 - θ))).2 = (ofLp z).2
      rw [hc2]; ring
  -- Step 1: a fit of radius `R` at the centering point, with parameters `<= C₄ L`
  obtain ⟨pR, aR, hfitR⟩ := hfitsat zc R hRpos
  have hpR : ‖pR‖ + |aR| ≤ C₄ * L := by
    have h := hcomp v zc (hfitsat zc) 1 R 0 pR 0 aR one_pos hRpos hfitzc hfitR
    rw [div_one, zero_sub, norm_neg, zero_sub, abs_neg, abs_of_nonneg hRlog0] at h
    rw [hC₄def]
    linarith [h, mul_le_mul_of_nonneg_left hRlog hC₁.le,
      mul_nonneg hC₁.le (sub_nonneg.mpr hL1),
      mul_nonneg (mul_nonneg hC₁.le hAlog0) (sub_nonneg.mpr hL1)]
  have hpRn : ‖pR‖ ≤ C₄ * L := by linarith [abs_nonneg aR]
  have hC₄L1 : (1:ℝ) ≤ C₄ * L := by nlinarith [hC₄1, hL1]
  -- Step 2: the box of `(pR,aR)` contains the `K`-box with margin
  have htθ : |(ofLp z).2 - θ| ≤ K + 1 := by
    have h := habs2 (ofLp z).2 θ
    rw [abs_of_nonneg hθ0] at h
    linarith [hzt]
  have hmargin1 : |(ofLp z).2 - θ| ≤ R / 4 := by linarith
  have hmargin2 : ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖ ≤ R / 4 := by
    have hbd : ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖ ≤ K + (K + 1) * ‖pR‖ := by
      calc ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖
          ≤ ‖(ofLp z).1‖ + ‖((ofLp z).2 - θ) • pR‖ := norm_sub_le _ _
        _ = ‖(ofLp z).1‖ + |(ofLp z).2 - θ| * ‖pR‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ K + (K + 1) * ‖pR‖ := by
            have := norm_nonneg pR
            nlinarith [hzx, htθ]
    have hstep1 : (K + 1) * ‖pR‖ ≤ 2 * K * (C₄ * L) :=
      mul_le_mul (by linarith) hpRn (norm_nonneg pR) (by linarith)
    have hstep2 : (K:ℝ) ≤ K * (C₄ * L) := by nlinarith [hK0, hC₄L1]
    linarith
  have hm1R : |(ofLp z).2 - θ| ≤ R := by linarith
  have hm2R : ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖ ≤ R := by linarith
  have hshift0 : ∀ h : F,
      zc + toLp 2 ((ofLp z).1 + h, (ofLp z).2 - θ) = z + toLp 2 (h, 0) := by
    intro h
    refine hptext _ _ ?_ ?_
    · show (ofLp (zc + toLp 2 ((ofLp z).1 + h, (ofLp z).2 - θ))).1 = (ofLp z).1 + h
      rw [hc1]
    · show (ofLp (zc + toLp 2 ((ofLp z).1 + h, (ofLp z).2 - θ))).2 = (ofLp z).2 + 0
      rw [hc2]; ring
  -- Step 3(a): the slopes of any radius-`R` fit at `z` are within `6 C₀` of `pR`
  have hslopes : ∀ (pz : F) (az : ℝ), IsFit C₀ v z R pz az → ‖pz - pR‖ ≤ 6 * C₀ := by
    clear hcomp hAexists hlogsqrt hptext hfitsat habs2 habs3 hc1 hc2 hshift hclass hcenter
      hfit hzx hzt htθ hpR hpRn hC₄L1 hR8K hRmargin hRlog hRlog0 hR1 hLdef hL1
      hC₄def hC₅def hAb hA12 hAbig hApos hAlog0 hA8 hzc1 hzc2 hfitzc hθ0 hθ1 hC₄1 hC₅1
    intro pz az hfz
    have hkey : ∀ h : F, ‖h‖ ≤ R / 2 → |(inner ℝ (pz - pR) h : ℝ)| ≤ 3 * C₀ * R := by
      intro h hh
      have hhR : ‖h‖ ≤ R := le_trans hh (by linarith only [hRpos])
      have h1 := hfz h 0 (by rw [abs_zero]; linarith only [hRpos])
        (by rw [zero_smul, sub_zero]; exact hhR)
      simp only [mul_zero, sub_zero] at h1
      have hb2 : ‖((ofLp z).1 + h) - ((ofLp z).2 - θ) • pR‖ ≤ R := by
        calc ‖((ofLp z).1 + h) - ((ofLp z).2 - θ) • pR‖
            = ‖((ofLp z).1 - ((ofLp z).2 - θ) • pR) + h‖ := by rw [sub_add_eq_add_sub]
          _ ≤ ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖ + ‖h‖ := norm_add_le _ _
          _ ≤ R := by linarith only [hmargin2, hh, hRpos]
      have h2 := hfitR ((ofLp z).1 + h) ((ofLp z).2 - θ) hm1R hb2
      rw [hshift0 h, inner_add_right] at h2
      have h3 := hfitR (ofLp z).1 ((ofLp z).2 - θ) hm1R hm2R
      rw [hzeq] at h3
      have a1 := abs_le.mp h1
      have a2 := abs_le.mp h2
      have a3 := abs_le.mp h3
      rw [inner_sub_left, abs_le]
      constructor <;> linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
    rcases eq_or_ne pz pR with rfl | hne
    · rw [sub_self, norm_zero]; positivity
    · have hpos : 0 < ‖pz - pR‖ := by rw [norm_pos_iff]; exact sub_ne_zero_of_ne hne
      have hne0 : ‖pz - pR‖ ≠ 0 := ne_of_gt hpos
      have hscal : (0:ℝ) < R / 2 / ‖pz - pR‖ := div_pos (by linarith only [hRpos]) hpos
      have hnm : ‖(R / 2 / ‖pz - pR‖) • (pz - pR)‖ = R / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hscal]
        exact div_mul_cancel₀ _ hne0
      have hin : (inner ℝ (pz - pR) ((R / 2 / ‖pz - pR‖) • (pz - pR)) : ℝ)
          = R / 2 * ‖pz - pR‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        have hrw : R / 2 / ‖pz - pR‖ * ‖pz - pR‖ ^ 2
            = (R / 2 / ‖pz - pR‖ * ‖pz - pR‖) * ‖pz - pR‖ := by rw [pow_two]; ring
        rw [hrw, div_mul_cancel₀ _ hne0]
      have hk := hkey _ hnm.le
      rw [hin, abs_of_nonneg (mul_nonneg (by linarith only [hRpos]) (norm_nonneg _))] at hk
      have h2 : R / 2 * ‖pz - pR‖ ≤ R / 2 * (6 * C₀) := by linarith only [hk]
      exact le_of_mul_le_mul_left h2 (by linarith only [hRpos])
  -- Step 3(b): the time coefficients
  have htimes : ∀ (pz : F) (az : ℝ), IsFit C₀ v z R pz az →
      |az - aR| ≤ 12 * C₀ * (1 + 6 * C₀) + 18 * C₀ ^ 2 := by
    clear hcomp hAexists hlogsqrt hptext hfitsat habs2 habs3 hc1 hc2 hclass hcenter
      hfit hzx hzt htθ hpR hpRn hC₄L1 hR8K hRmargin hRlog hRlog0 hR1 hLdef hL1
      hC₄def hC₅def hAb hA12 hAbig hApos hAlog0 hA8 hzc1 hzc2 hfitzc hθ0 hθ1 hC₄1 hC₅1
    intro pz az hfz
    have hsl := hslopes pz az hfz
    have hcR : (0:ℝ) < c * R := mul_pos hc0 hRpos
    have hcR4 : c * R ≤ R / 4 := by nlinarith only [hc4, hRpos, hc0]
    have hA1 := hfz ((c * R) • pz) (c * R) (by rw [abs_of_pos hcR]; linarith only [hcR4, hRpos])
      (by rw [sub_self, norm_zero]; linarith only [hRpos])
    have hm1 := abs_le.mp hmargin1
    have hb2t : |(ofLp z).2 - θ + c * R| ≤ R := by
      rw [abs_le]
      constructor <;> linarith only [hm1.1, hm1.2, hcR4, hcR, hRpos]
    have hprod : c * R * ‖pz - pR‖ ≤ R / 4 := by
      have h1 : c * R * ‖pz - pR‖ ≤ c * R * (6 * C₀) := mul_le_mul_of_nonneg_left hsl hcR.le
      nlinarith only [h1, hc6, hRpos, hc0]
    have hb2x : ‖((ofLp z).1 + (c * R) • pz) - ((ofLp z).2 - θ + c * R) • pR‖ ≤ R := by
      calc ‖((ofLp z).1 + (c * R) • pz) - ((ofLp z).2 - θ + c * R) • pR‖
          = ‖((ofLp z).1 - ((ofLp z).2 - θ) • pR) + (c * R) • (pz - pR)‖ := by
            rw [smul_sub, add_smul]; abel_nf
        _ ≤ ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖ + ‖(c * R) • (pz - pR)‖ := norm_add_le _ _
        _ = ‖(ofLp z).1 - ((ofLp z).2 - θ) • pR‖ + c * R * ‖pz - pR‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcR]
        _ ≤ R := by linarith only [hmargin2, hprod, hRpos]
    have hA2 := hfitR ((ofLp z).1 + (c * R) • pz) ((ofLp z).2 - θ + c * R) hb2t hb2x
    rw [hshift ((c * R) • pz) (c * R), inner_add_right, real_inner_smul_right] at hA2
    have hA3 := hfitR (ofLp z).1 ((ofLp z).2 - θ) hm1R hm2R
    rw [hzeq] at hA3
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at hA1
    have hnrmT : c * R * ‖pz - pR‖ ^ 2
        = c * R * (‖pz‖ ^ 2 - 2 * (inner ℝ pR pz : ℝ) + ‖pR‖ ^ 2) := by
      rw [norm_sub_sq_real, real_inner_comm pz pR]
    have a1 := abs_le.mp hA1
    have a2 := abs_le.mp hA2
    have a3 := abs_le.mp hA3
    have hcomb : c * R * |az - aR + ‖pz - pR‖ ^ 2 / 2| ≤ 3 * C₀ * R := by
      rw [← abs_of_pos hcR, ← abs_mul, abs_le]
      constructor <;>
        linarith only [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2, hnrmT]
    have hdiv : |az - aR + ‖pz - pR‖ ^ 2 / 2| ≤ 12 * C₀ * (1 + 6 * C₀) := by
      rw [← hcinv, le_div_iff₀ hc0]
      have h4 : R * (|az - aR + ‖pz - pR‖ ^ 2 / 2| * c) ≤ R * (3 * C₀) := by
        calc R * (|az - aR + ‖pz - pR‖ ^ 2 / 2| * c)
            = c * R * |az - aR + ‖pz - pR‖ ^ 2 / 2| := by ring
          _ ≤ 3 * C₀ * R := hcomb
          _ = R * (3 * C₀) := by ring
      exact le_of_mul_le_mul_left h4 hRpos
    have hd := abs_le.mp hdiv
    have hsq : ‖pz - pR‖ ^ 2 ≤ 36 * C₀ ^ 2 := by
      nlinarith only [hsl, norm_nonneg (pz - pR), hC₀0.le]
    rw [abs_le]
    constructor <;> linarith only [hd.1, hd.2, sq_nonneg ‖pz - pR‖, hsq]
  -- Step 4: arbitrary radii at a center in the box
  obtain ⟨pz, az, hfz⟩ := hfitsat z R hRpos
  have hpzb : ‖pz‖ + |az| ≤ C₅ * L := by
    have h1 := hslopes pz az hfz
    have h2 := htimes pz az hfz
    have t1 : ‖pz‖ ≤ ‖pR‖ + ‖pz - pR‖ := by
      calc ‖pz‖ = ‖pR + (pz - pR)‖ := by rw [show pR + (pz - pR) = pz from by abel]
        _ ≤ ‖pR‖ + ‖pz - pR‖ := norm_add_le _ _
    have t2 : |az| ≤ |aR| + |az - aR| := by
      calc |az| = |aR + (az - aR)| := by rw [show aR + (az - aR) = az from by ring]
        _ ≤ |aR| + |az - aR| := habs3 _ _
    have hbr : (0:ℝ) ≤ 6 * C₀ + 12 * C₀ * (1 + 6 * C₀) + 18 * C₀ ^ 2 := by positivity
    have hbrL : (0:ℝ) ≤ (6 * C₀ + 12 * C₀ * (1 + 6 * C₀) + 18 * C₀ ^ 2) * (L - 1) :=
      mul_nonneg hbr (by linarith only [hL1])
    rw [hC₅def]
    linarith only [hpR, h1, h2, t1, t2, hbrL]
  have hcmp := hcomp v z (hfitsat z) r R p pz a az hr hRpos hfit hfz
  have hlogRr : |Real.log (R / r)| ≤ Real.log A + 2 * L + |Real.log r| := by
    rw [Real.log_div (ne_of_gt hRpos) (ne_of_gt hr)]
    calc |Real.log R - Real.log r| ≤ |Real.log R| + |Real.log r| := habs2 _ _
      _ = Real.log R + |Real.log r| := by rw [abs_of_nonneg hRlog0]
      _ ≤ Real.log A + 2 * L + |Real.log r| := by linarith only [hRlog]
  have t3 : ‖p‖ ≤ ‖pz‖ + ‖p - pz‖ := by
    calc ‖p‖ = ‖pz + (p - pz)‖ := by rw [show pz + (p - pz) = p from by abel]
      _ ≤ ‖pz‖ + ‖p - pz‖ := norm_add_le _ _
  have t4 : |a| ≤ |az| + |a - az| := by
    calc |a| = |az + (a - az)| := by rw [show az + (a - az) = a from by ring]
      _ ≤ |az| + |a - az| := habs3 _ _
  have hlr0 : (0:ℝ) ≤ |Real.log r| := abs_nonneg _
  have hLge0 : (0:ℝ) ≤ L := by linarith only [hL1]
  linarith only [t3, t4, hpzb, hcmp,
    mul_le_mul_of_nonneg_left hlogRr hC₁.le,
    mul_nonneg hC₁.le (by linarith only [hL1] : (0:ℝ) ≤ L - 1),
    mul_nonneg (mul_nonneg hC₁.le hAlog0) (by linarith only [hL1] : (0:ℝ) ≤ L - 1),
    mul_nonneg hC₁.le hLge0,
    mul_nonneg (mul_nonneg hC₁.le (by linarith only [hAlog0] : (0:ℝ) ≤ 3 + Real.log A)) hlr0,
    mul_nonneg (by linarith only [hC₅1] : (0:ℝ) ≤ C₅) hlr0]
