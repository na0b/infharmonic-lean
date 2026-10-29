import InfHarmonic.IsInfHarmonicOn
import InfHarmonic.ConeSlopeUpper
import InfHarmonic.ConeSlopeLower
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma 2.3, cone comparison and radial monotonicity: an infinity-harmonic
function is dominated on `closedBall z r` by the cone of slope
`ConeSlopeUpper w z r`, dominated below by the cone of slope
`ConeSlopeLower w z r`, and both slopes are nondecreasing in the radius. -/
theorem ConeComparison (D : Set E) (w : E → ℝ) (hw : IsInfHarmonicOn D w)
    (z : E) (r : ℝ) (hr : 0 < r) (hball : closedBall z r ⊆ D) :
    (∀ Z ∈ closedBall z r, w Z - w z ≤ ConeSlopeUpper w z r * ‖Z - z‖) ∧
    (∀ Z ∈ closedBall z r, -(w Z - w z) ≤ ConeSlopeLower w z r * ‖Z - z‖) ∧
    (∀ r' : ℝ, r ≤ r' → closedBall z r' ⊆ D →
      ConeSlopeUpper w z r ≤ ConeSlopeUpper w z r' ∧
      ConeSlopeLower w z r ≤ ConeSlopeLower w z r') := by
  -- The ambient inner product as an honestly `ℝ`-bilinear form, and the squared-distance
  -- polynomial `q Z = ‖Z - z‖²`.  Everything radial is expressed through `q`, so the only
  -- non-polynomial ingredient anywhere is the one-dimensional `Real.sqrt`.
  set B : E →L[ℝ] E →L[ℝ] ℝ :=
    (InnerProductSpace.toDualMap ℝ E).toContinuousLinearMap with hBdef
  have hB : ∀ v u : E, B v u = inner ℝ v u := fun v u => rfl
  have hgradB : ∀ v : E, (InnerProductSpace.toDual ℝ E).symm (B v) = v := by
    intro v
    have h : (InnerProductSpace.toDual ℝ E) v = B v := ContinuousLinearMap.ext fun u => rfl
    rw [h.symm]; simp
  set W : E →L[ℝ] E →L[ℝ] ℝ := B + ContinuousLinearMap.flip B with hWdef
  have hWvv : ∀ v u : E, W v u = 2 * inner ℝ v u := by
    intro v u
    simp only [hWdef, add_apply, ContinuousLinearMap.flip_apply, hB]
    rw [real_inner_comm u v]; ring
  have hWB : ∀ v : E, W v = B ((2:ℝ) • v) := by
    intro v; apply ContinuousLinearMap.ext; intro u
    simp only [hWdef, add_apply, ContinuousLinearMap.flip_apply, hB, map_smul,
      FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
    rw [real_inner_comm u v]; ring
  set q : E → ℝ := fun Z => B (Z - z) (Z - z) with hqdef
  have hqn : ∀ Z : E, q Z = ‖Z - z‖ ^ 2 := by
    intro Z; simp only [hqdef]; rw [hB]; exact real_inner_self_eq_norm_sq _
  have hqne : ∀ Z : E, Z ≠ z → q Z ≠ 0 := by
    intro Z hZ; rw [hqn]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero_of_ne hZ))
  have hsubd : ∀ Z : E, HasFDerivAt (fun Y : E => Y - z) (ContinuousLinearMap.id ℝ E) Z :=
    fun Z => (hasFDerivAt_id Z).sub_const z
  have hqC : ContDiff ℝ 2 q :=
    (B.contDiff.comp (contDiff_id.sub contDiff_const)).clm_apply
      (contDiff_id.sub contDiff_const)
  have hqd : ∀ Z : E, HasFDerivAt q (W (Z - z)) Z := by
    intro Z
    refine ((B.hasFDerivAt.comp Z (hsubd Z)).clm_apply (hsubd Z)).congr_fderiv ?_
    apply ContinuousLinearMap.ext; intro h; simp [hWdef]
  -- THE BARRIER of `paper.tex:274-280`, in the form `c₀ + L√(q Z) - γ q Z`: it is `C²` off
  -- the centre and its infinity Laplacian is `-2γ(L - 2γρ)²`, the computation of
  -- Step 2's closing display.
  have hbarrier : ∀ (c₀ L γ : ℝ) (Z₀ : E), Z₀ ≠ z →
      ContDiffAt ℝ 2 (fun Z : E => c₀ + (L * Real.sqrt (q Z) - γ * q Z)) Z₀ ∧
      InfLap (fun Z : E => c₀ + (L * Real.sqrt (q Z) - γ * q Z)) Z₀
        = -2 * γ * (L - 2 * γ * ‖Z₀ - z‖) ^ 2 := by
    intro c₀ L γ Z₀ hZ₀
    set ρ : ℝ := ‖Z₀ - z‖ with hρdef
    have hρ : 0 < ρ := by simp only [hρdef, norm_pos_iff]; exact sub_ne_zero_of_ne hZ₀
    have hr : Real.sqrt (q Z₀) = ρ := by rw [hqn]; exact Real.sqrt_sq hρ.le
    set Θ : E → ℝ := fun Z => c₀ + (L * Real.sqrt (q Z) - γ * q Z) with hΘdef
    set cp : ℝ → ℝ := fun s => L * (1 / (2 * Real.sqrt s)) - γ * 1 with hcpdef
    refine ⟨?_, ?_⟩
    · exact contDiffAt_const.add ((contDiffAt_const.mul
        (hqC.contDiffAt.sqrt (hqne Z₀ hZ₀))).sub (contDiffAt_const.mul hqC.contDiffAt))
    · have hΘd : ∀ Z : E, Z ≠ z → HasFDerivAt Θ (cp (q Z) • W (Z - z)) Z := by
        intro Z hZ
        have hGd : HasDerivAt (fun t : ℝ => L * Real.sqrt t - γ * t)
            (L * (1 / (2 * Real.sqrt (q Z))) - γ * 1) (q Z) :=
          ((Real.hasDerivAt_sqrt (hqne Z hZ)).const_mul L).sub
            ((hasDerivAt_id (q Z)).const_mul γ)
        exact (hGd.comp_hasFDerivAt Z (hqd Z)).const_add c₀
      have hcpd : HasDerivAt cp (-(L / (4 * ρ ^ 3))) (q Z₀) := by
        have hsq : q Z₀ ≠ 0 := hqne Z₀ hZ₀
        have hd2 : (2 : ℝ) * Real.sqrt (q Z₀) ≠ 0 := by rw [hr]; positivity
        have h1 : HasDerivAt (fun t : ℝ => (2:ℝ) * t) 2 (Real.sqrt (q Z₀)) := by
          simpa using (hasDerivAt_id (Real.sqrt (q Z₀))).const_mul (2:ℝ)
        have h2 : HasDerivAt (fun t : ℝ => (1:ℝ) / (2 * t))
            ((0 * (2 * Real.sqrt (q Z₀)) - 1 * 2) / (2 * Real.sqrt (q Z₀)) ^ 2)
            (Real.sqrt (q Z₀)) := (hasDerivAt_const _ (1:ℝ)).div h1 hd2
        have h4 := ((h2.const_mul L).sub_const (γ * 1)).comp (q Z₀)
          (Real.hasDerivAt_sqrt hsq)
        have h5 : HasDerivAt cp
            (L * ((0 * (2 * Real.sqrt (q Z₀)) - 1 * 2) / (2 * Real.sqrt (q Z₀)) ^ 2)
              * (1 / (2 * Real.sqrt (q Z₀)))) (q Z₀) := by
          simpa [hcpdef, Function.comp_def] using h4
        refine h5.congr_deriv ?_
        rw [hr]; field_simp; ring
      have hcd : HasFDerivAt (fun Z : E => cp (q Z))
          ((-(L / (4 * ρ ^ 3))) • W (Z₀ - z)) Z₀ := hcpd.comp_hasFDerivAt Z₀ (hqd Z₀)
      have hWd : HasFDerivAt (fun Z : E => W (Z - z)) W Z₀ := by
        refine (W.hasFDerivAt.comp Z₀ (hsubd Z₀)).congr_fderiv ?_
        apply ContinuousLinearMap.ext; intro h; simp
      have hD2 : fderiv ℝ (fderiv ℝ Θ) Z₀
          = cp (q Z₀) • W + ((-(L / (4 * ρ ^ 3))) • W (Z₀ - z)).smulRight (W (Z₀ - z)) := by
        have hg : HasFDerivAt (fun Z : E => cp (q Z) • W (Z - z))
            (cp (q Z₀) • W + ((-(L / (4 * ρ ^ 3))) • W (Z₀ - z)).smulRight (W (Z₀ - z))) Z₀ :=
          hcd.smul hWd
        have heq : fderiv ℝ Θ =ᶠ[nhds Z₀] fun Z => cp (q Z) • W (Z - z) := by
          filter_upwards [isOpen_compl_singleton.mem_nhds
            (by simpa using hZ₀ : Z₀ ∈ ({z} : Set E)ᶜ)] with Z hZ
          exact (hΘd Z (by simpa using hZ)).fderiv
        rw [heq.fderiv_eq, hg.fderiv]
      have hgrad : gradient Θ Z₀ = (2 * cp (q Z₀)) • (Z₀ - z) := by
        unfold gradient
        rw [(hΘd Z₀ hZ₀).fderiv, hWB]
        have he : cp (q Z₀) • B ((2:ℝ) • (Z₀ - z)) = B ((2 * cp (q Z₀)) • (Z₀ - z)) := by
          apply ContinuousLinearMap.ext; intro u
          simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul, map_smul]
          ring
        rw [he, hgradB]
      unfold InfLap
      rw [iteratedFDeriv_two_apply, hD2, hgrad]
      set k : ℝ := 2 * cp (q Z₀) with hkdef
      have hvv : inner ℝ (k • (Z₀ - z)) (k • (Z₀ - z)) = k ^ 2 * ρ ^ 2 := by
        rw [real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq, ← hρdef]
        ring
      have hzv : inner ℝ (Z₀ - z) (k • (Z₀ - z)) = k * ρ ^ 2 := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, ← hρdef]
      simp only [add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
        ContinuousLinearMap.smulRight_apply, hWvv, hvv, hzv]
      have hcpv : cp (q Z₀) = L * (1 / (2 * ρ)) - γ * 1 := by simp only [hcpdef, hr]
      rw [hkdef, hcpv]
      field_simp
      ring
  -- Step 0: the slope sets are nonempty and bounded above, so the suprema are genuine
  -- (pm-0004: the paper writes `max` over a compact ball, which is what supplies this).
  have hset : ∀ (v : E → ℝ) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ D → ContinuousOn v D →
      (((fun h => (v (z + h) - v z) / ρ) '' closedBall (0:E) ρ).Nonempty ∧
       BddAbove ((fun h => (v (z + h) - v z) / ρ) '' closedBall (0:E) ρ)) := by
    intro v ρ hρ hball hvc
    have hmemD : ∀ h : E, h ∈ closedBall (0:E) ρ → z + h ∈ D := by
      intro h hh
      refine hball ?_
      rw [mem_closedBall_iff_norm]
      simpa using mem_closedBall_zero_iff.mp hh
    have hcont : ContinuousOn (fun h : E => (v (z + h) - v z) / ρ) (closedBall (0:E) ρ) := by
      refine ContinuousOn.div_const (ContinuousOn.sub ?_ continuousOn_const) ρ
      exact hvc.comp (by fun_prop) hmemD
    exact ⟨⟨(v (z + 0) - v z) / ρ, ⟨0, mem_closedBall_self hρ.le, rfl⟩⟩,
      (isCompact_closedBall (0:E) ρ).bddAbove_image hcont⟩
  have hle : ∀ (v : E → ℝ) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ D → ContinuousOn v D →
      ∀ h : E, ‖h‖ ≤ ρ → (v (z + h) - v z) / ρ ≤ ConeSlopeUpper v z ρ := by
    intro v ρ hρ hball hvc h hh
    exact le_csSup (hset v ρ hρ hball hvc).2 ⟨h, mem_closedBall_zero_iff.mpr hh, rfl⟩
  have hnn : ∀ (v : E → ℝ) (ρ : ℝ), 0 < ρ → closedBall z ρ ⊆ D → ContinuousOn v D →
      0 ≤ ConeSlopeUpper v z ρ := by
    intro v ρ hρ hball hvc
    simpa using hle v ρ hρ hball hvc 0 (by simpa using hρ.le)
  -- Step 2: the perturbed cone barrier, for every slope strictly above the cone slope.
  have core : ∀ v : E → ℝ, IsInfSubsolutionOn D v → ∀ ρ : ℝ, 0 < ρ → closedBall z ρ ⊆ D →
      ∀ L : ℝ, ConeSlopeUpper v z ρ < L → ∀ Z ∈ closedBall z ρ,
        v Z - v z ≤ L * ‖Z - z‖ := by
    intro v hv ρ hρ hball L hL Z hZ
    have hvc : ContinuousOn v D := hv.2.1
    set S : ℝ := ConeSlopeUpper v z ρ with hSdef
    have hS0 : 0 ≤ S := hnn v ρ hρ hball hvc
    have hLpos : 0 < L := lt_of_le_of_lt hS0 hL
    -- the perturbation parameter of `paper.tex:276`
    set γ : ℝ := min ((L - S) / (2 * ρ)) (L / (4 * ρ)) with hγdef
    have hγ : 0 < γ := lt_min (div_pos (by linarith) (by positivity)) (by positivity)
    have hγ1 : γ * ρ < L - S := by
      have hle1 : γ ≤ (L - S) / (2 * ρ) := min_le_left _ _
      have h1 : γ * ρ ≤ (L - S) / (2 * ρ) * ρ := mul_le_mul_of_nonneg_right hle1 hρ.le
      have heq : (L - S) / (2 * ρ) * ρ = (L - S) / 2 := by field_simp
      rw [heq] at h1; linarith
    have hγ2 : 2 * γ * ρ < L := by
      have hle2 : γ ≤ L / (4 * ρ) := min_le_right _ _
      have h1 : γ * ρ ≤ L / (4 * ρ) * ρ := mul_le_mul_of_nonneg_right hle2 hρ.le
      have heq : L / (4 * ρ) * ρ = L / 4 := by field_simp
      rw [heq] at h1; linarith
    set Θ : E → ℝ := fun Y => v z + (L * Real.sqrt (q Y) - γ * q Y) with hΘdef
    have hΘval : ∀ Y : E, Θ Y = v z + (L * ‖Y - z‖ - γ * ‖Y - z‖ ^ 2) := by
      intro Y
      simp only [hΘdef, hqn]
      rw [Real.sqrt_sq (norm_nonneg _)]
    have hΘz : Θ z = v z := by rw [hΘval]; simp
    have hΘcont : Continuous Θ := by
      simp only [hΘdef]
      exact continuous_const.add ((continuous_const.mul
        (Real.continuous_sqrt.comp hqC.continuous)).sub (continuous_const.mul hqC.continuous))
    -- the barrier dominates `v` on the ball
    have hdom : ∀ Y ∈ closedBall z ρ, v Y ≤ Θ Y := by
      by_contra hcon
      push Not at hcon
      obtain ⟨Y₀, hY₀mem, hY₀⟩ := hcon
      obtain ⟨Z₁, hZ₁mem, hZ₁max⟩ := (isCompact_closedBall z ρ).exists_isMaxOn
        ⟨z, mem_closedBall_self hρ.le⟩
        (((hvc.mono hball).sub hΘcont.continuousOn) :
          ContinuousOn (fun Y => v Y - Θ Y) (closedBall z ρ))
      have hpos : 0 < v Z₁ - Θ Z₁ :=
        lt_of_lt_of_le (by linarith : (0:ℝ) < v Y₀ - Θ Y₀) (hZ₁max hY₀mem)
      have hZ₁z : Z₁ ≠ z := by
        intro h; rw [h, hΘz] at hpos; simp at hpos
      -- on the sphere the barrier is strictly above `v`, by Step 0
      have hsphere : ∀ Y : E, ‖Y - z‖ = ρ → v Y - Θ Y < 0 := by
        intro Y hY
        have h1 : v Y - v z ≤ ρ * S := by
          have h2 := hle v ρ hρ hball hvc (Y - z) (by rw [hY])
          have hz : z + (Y - z) = Y := by abel
          rw [hz, div_le_iff₀ hρ] at h2
          linarith
        have h3 : Θ Y = v z + (L * ρ - γ * ρ ^ 2) := by rw [hΘval, hY]
        rw [h3]
        nlinarith [hγ1, hρ]
      have hlt : ‖Z₁ - z‖ < ρ := by
        rcases lt_or_eq_of_le (mem_closedBall_iff_norm.mp hZ₁mem) with h | h
        · exact h
        · exact absurd (hsphere Z₁ h) (by linarith)
      have hlocmax : IsLocalMaxOn (fun Y => v Y - Θ Y) D Z₁ := by
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [Metric.ball_mem_nhds Z₁ (by linarith : 0 < ρ - ‖Z₁ - z‖)] with Y hY
        refine hZ₁max ?_
        rw [mem_closedBall_iff_norm]
        have h1 := mem_ball.mp hY
        rw [dist_eq_norm] at h1
        have h2 : ‖Y - z‖ ≤ ‖Y - Z₁‖ + ‖Z₁ - z‖ := by
          have h3 := norm_add_le (Y - Z₁) (Z₁ - z)
          have h4 : Y - Z₁ + (Z₁ - z) = Y - z := by abel
          rwa [h4] at h3
        linarith
      obtain ⟨hΘC, hΘInf⟩ := hbarrier (v z) L γ Z₁ hZ₁z
      rw [← hΘdef] at hΘC hΘInf
      have h0 := hv.2.2 Z₁ (hball hZ₁mem) Θ hΘC hlocmax
      rw [hΘInf] at h0
      have hpos2 : 0 < L - 2 * γ * ‖Z₁ - z‖ := by nlinarith [hγ, hlt, norm_nonneg (Z₁ - z)]
      have hsqpos : 0 < (L - 2 * γ * ‖Z₁ - z‖) ^ 2 := pow_pos hpos2 2
      nlinarith [hγ, hsqpos]
    have h1 := hdom Z hZ
    rw [hΘval] at h1
    nlinarith [hγ, sq_nonneg ‖Z - z‖]
  -- Step 2's conclusion, letting `L` decrease to the cone slope.
  have step2 : ∀ v : E → ℝ, IsInfSubsolutionOn D v → ∀ ρ : ℝ, 0 < ρ → closedBall z ρ ⊆ D →
      ∀ Z ∈ closedBall z ρ, v Z - v z ≤ ConeSlopeUpper v z ρ * ‖Z - z‖ := by
    intro v hv ρ hρ hball Z hZ
    by_contra hcon
    push Not at hcon
    set S : ℝ := ConeSlopeUpper v z ρ with hSdef
    have hnorm : 0 < ‖Z - z‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (Z - z)) with h | h
      · exfalso
        have hZz : Z = z := by
          have h1 : Z - z = 0 := norm_eq_zero.mp h.symm
          have := sub_eq_zero.mp h1
          exact this
        rw [hZz] at hcon; simp at hcon
      · exact h
    set δ : ℝ := (v Z - v z - S * ‖Z - z‖) / (2 * ‖Z - z‖) with hδdef
    have hδ : 0 < δ := div_pos (by linarith) (by positivity)
    have h := core v hv ρ hρ hball (S + δ) (by linarith) Z hZ
    have hδn : δ * ‖Z - z‖ = (v Z - v z - S * ‖Z - z‖) / 2 := by
      rw [hδdef]; field_simp
    rw [add_mul, hδn] at h
    linarith
  -- Step 1: `-w` is an infinity subsolution, because `InfLap (-φ) = -InfLap φ`.
  have hInfneg : ∀ (φ : E → ℝ) (Y : E), InfLap (-φ) Y = -InfLap φ Y := by
    intro φ Y
    unfold InfLap
    have hg : gradient (-φ) Y = -gradient φ Y := by
      unfold gradient; rw [fderiv_neg]; simp
    rw [hg, iteratedFDeriv_neg_apply]
    have hflip : ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ,
        (M fun _ => -gradient φ Y) = M (fun _ => gradient φ Y) := by
      intro M
      have h1 : (fun _ : Fin 2 => -gradient φ Y)
          = fun i : Fin 2 => (fun _ : Fin 2 => (-1 : ℝ)) i •
              (fun _ : Fin 2 => gradient φ Y) i := by
        funext i; simp
      rw [h1, M.map_smul_univ]; simp
    simp [hflip]
  have hneg : IsInfSubsolutionOn D (-w) := by
    refine ⟨hw.2.1, hw.2.2.1.neg, ?_⟩
    intro Y hY φ hφ hmax
    have hmin : IsLocalMinOn (fun x => w x - (-φ) x) D Y := by
      filter_upwards [hmax] with x hx
      simp only [Pi.neg_apply] at hx ⊢
      linarith
    have h := hw.2.2.2 Y hY (-φ) hφ.neg hmin
    rw [hInfneg] at h
    linarith
  have hslopeneg : ∀ ρ : ℝ, ConeSlopeUpper (-w) z ρ = ConeSlopeLower w z ρ := by
    intro ρ
    show sSup ((fun h => ((-w) (z + h) - (-w) z) / ρ) '' closedBall (0:E) ρ)
        = sSup ((fun h => (-(w (z + h) - w z)) / ρ) '' closedBall (0:E) ρ)
    have hfun : (fun h : E => ((-w) (z + h) - (-w) z) / ρ)
        = fun h : E => (-(w (z + h) - w z)) / ρ := by
      funext h; simp only [Pi.neg_apply]; ring
    rw [hfun]
  -- Step 4: monotonicity in the radius.
  have mono : ∀ v : E → ℝ, IsInfSubsolutionOn D v → ∀ ρ' : ℝ, 0 < ρ' →
      closedBall z ρ' ⊆ D → r ≤ ρ' → ConeSlopeUpper v z r ≤ ConeSlopeUpper v z ρ' := by
    intro v hv ρ' hρ' hball' hrr'
    have hvc : ContinuousOn v D := hv.2.1
    have hS' : 0 ≤ ConeSlopeUpper v z ρ' := hnn v ρ' hρ' hball' hvc
    have hb := step2 v hv ρ' hρ' hball'
    have hrw : ConeSlopeUpper v z r
        = sSup ((fun h => (v (z + h) - v z) / r) '' closedBall (0:E) r) := rfl
    rw [hrw]
    refine csSup_le (hset v r hr hball hvc).1 ?_
    rintro a ⟨h, hh, rfl⟩
    have hhr : ‖h‖ ≤ r := mem_closedBall_zero_iff.mp hh
    have hmem : z + h ∈ closedBall z ρ' := by
      rw [mem_closedBall_iff_norm]
      simpa using le_trans hhr hrr'
    have h1 := hb (z + h) hmem
    simp only [add_sub_cancel_left] at h1
    rw [div_le_iff₀ hr]
    nlinarith [hS', hhr, norm_nonneg h]
  -- assemble the three conclusions
  refine ⟨step2 w hw.1 r hr hball, ?_, ?_⟩
  · intro Z hZ
    have h := step2 (-w) hneg r hr hball Z hZ
    rw [hslopeneg] at h
    have he : (-w) Z - (-w) z = -(w Z - w z) := by simp only [Pi.neg_apply]; ring
    rwa [he] at h
  · intro r' hrr' hball'
    have hr' : 0 < r' := lt_of_lt_of_le hr hrr'
    refine ⟨mono w hw.1 r' hr' hball' hrr', ?_⟩
    have h := mono (-w) hneg r' hr' hball' hrr'
    rw [hslopeneg, hslopeneg] at h
    exact h
