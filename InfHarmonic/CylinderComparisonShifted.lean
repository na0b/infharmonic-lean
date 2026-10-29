import InfHarmonic.IsCylinderFit
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma 3.5, displaced-center case: two cylinder fits of parameter `θ²` of
equal radius `H`, whose centers differ by at most a quarter of the axial and
transverse radii of the first cylinder, have slopes agreeing to `O(θ)` and
norms agreeing to `O(θ²)`. -/
theorem CylinderComparisonShifted (c₁ C₁ : ℝ) (hc : 0 < c₁) (hcC : c₁ ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : E → ℝ) (z z' : E) (θ H : ℝ) (P P' : E),
      0 < θ → θ < 1 → 0 < H →
      c₁ ≤ ‖P‖ → ‖P‖ ≤ C₁ → c₁ ≤ ‖P'‖ → ‖P'‖ ≤ C₁ →
      |(inner ℝ (‖P‖⁻¹ • P) (z' - z) : ℝ)| ≤ H / 4 →
      ‖(z' - z) - (inner ℝ (‖P‖⁻¹ • P) (z' - z) : ℝ) • (‖P‖⁻¹ • P)‖ ≤ θ * H / 4 →
      IsCylinderFit u z H (θ ^ 2) P → IsCylinderFit u z' H (θ ^ 2) P' →
      ‖P - P'‖ + ‖‖P‖⁻¹ • P - ‖P'‖⁻¹ • P'‖ ≤ C * θ ∧
      |‖P‖ - ‖P'‖| ≤ C * θ ^ 2 := by
  -- The argument is pure affine geometry and dimension-free: `[FiniteDimensional ℝ E]` is
  -- carried by the statement because the paper's lemma lives in `ℝ^m`, but nothing below
  -- uses it. Recorded here so the node closes without a fresh `unusedSectionVars` warning.
  have _unused_fd : FiniteDimensional ℝ E := inferInstance
  -- `γ = min {1/4, c₁/48}`, used only through these three facts.
  obtain ⟨γ, hγ4, hγ48, hγ0⟩ : ∃ γ : ℝ, γ ≤ 1 / 4 ∧ γ ≤ c₁ / 48 ∧ 0 < γ :=
    ⟨min (1 / 4) (c₁ / 48), min_le_left _ _, min_le_right _ _,
      lt_min (by norm_num) (by linarith)⟩
  have hc' : c₁ ≠ 0 := hc.ne'
  have hproj : ∀ m h : E, ‖m‖ = 1 → ‖h - (inner ℝ m h : ℝ) • m‖ ≤ ‖h‖ := by
    intro m h hm
    have hsq : ‖h - (inner ℝ m h : ℝ) • m‖ ^ 2 ≤ ‖h‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hm, mul_one,
        real_inner_comm h m]
      nlinarith [sq_abs (inner ℝ h m : ℝ), sq_nonneg (inner ℝ h m : ℝ)]
    have h' := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'
  have hprojid : ∀ a b : E, ‖b‖ = 1 →
      a - (inner ℝ b a : ℝ) • b = (a - b) - (inner ℝ b (a - b) : ℝ) • b := by
    intro a b hb
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hb]
    simp only [one_pow, sub_smul, one_smul]
    abel
  have hscalar : ∀ a b d : ℝ, 0 < a → 0 < b → |b - a| ≤ d → |a⁻¹ - b⁻¹| * b ≤ a⁻¹ * d := by
    intro a b d ha hb hd
    have ha' : a ≠ 0 := ha.ne'
    have hb' : b ≠ 0 := hb.ne'
    have e : a⁻¹ - b⁻¹ = (b - a) / (a * b) := by field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0:ℝ) < a * b),
      div_mul_eq_mul_div, div_le_iff₀ (by positivity : (0:ℝ) < a * b)]
    have e2 : a⁻¹ * d * (a * b) = d * b := by field_simp
    rw [e2]
    exact mul_le_mul_of_nonneg_right hd hb.le
  have hsplitproj : ∀ m a b : E, (a + b) - (inner ℝ m (a + b) : ℝ) • m
      = (a - (inner ℝ m a : ℝ) • m) + (b - (inner ℝ m b : ℝ) • m) := by
    intro m a b
    rw [inner_add_right, add_smul]
    abel
  have haxle : ∀ m h : E, ‖m‖ = 1 → |(inner ℝ m h : ℝ)| ≤ ‖h‖ := by
    intro m h hm
    calc |(inner ℝ m h : ℝ)| ≤ ‖m‖ * ‖h‖ := abs_real_inner_le_norm _ _
      _ = ‖h‖ := by rw [hm, one_mul]
  refine ⟨max (6 + 12 / c₁) (3 / γ + 72 * C₁ / c₁ ^ 2), ?_, ?_⟩
  · have h1 : (0:ℝ) < 12 / c₁ := div_pos (by norm_num) hc
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  intro u z z' θ H P P' hθ0 hθ1 hH hcP hPC hcP' hP'C hoffa hofft hfit hfit'
  have hPpos : (0:ℝ) < ‖P‖ := lt_of_lt_of_le hc hcP
  have hP'pos : (0:ℝ) < ‖P'‖ := lt_of_lt_of_le hc hcP'
  have hnnorm : ‖(‖P‖⁻¹ • P : E)‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hPpos)
  have hn'norm : ‖(‖P'‖⁻¹ • P' : E)‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hP'pos)
  have hsqrt : Real.sqrt (θ ^ 2) = θ := Real.sqrt_sq hθ0.le
  have hθH : (0:ℝ) < θ * H := mul_pos hθ0 hH
  have hθHH : θ * H ≤ H := by nlinarith
  have hmem : ∀ (Q : E) (r : ℝ) (cc h : E),
      |(inner ℝ (‖Q‖⁻¹ • Q) h : ℝ)| ≤ r →
      ‖h - (inner ℝ (‖Q‖⁻¹ • Q) h : ℝ) • (‖Q‖⁻¹ • Q)‖ ≤ θ * r →
      cc + h ∈ FitCylinder cc r (θ ^ 2) Q := by
    intro Q r cc h hax htr
    exact ⟨by rw [add_sub_cancel_left]; exact hax,
      by rw [add_sub_cancel_left, hsqrt]; exact htr⟩
  have hshift : ∀ h : E, z' + h = z + ((z' - z) + h) := by intro h; abel
  -- Step 1: the ball of radius θH/2 around z' sits in both cylinders.
  have hinC : ∀ h : E, ‖h‖ ≤ θ * H / 2 → z' + h ∈ FitCylinder z H (θ ^ 2) P := by
    intro h hh
    rw [hshift h]
    refine hmem P H z ((z' - z) + h) ?_ ?_
    · have h1 := haxle (‖P‖⁻¹ • P : E) h hnnorm
      have h2 : |(inner ℝ (‖P‖⁻¹ • P) ((z' - z) + h) : ℝ)|
          ≤ |(inner ℝ (‖P‖⁻¹ • P) (z' - z) : ℝ)| + |(inner ℝ (‖P‖⁻¹ • P) h : ℝ)| := by
        rw [inner_add_right]; exact abs_add_le _ _
      linarith
    · rw [hsplitproj]
      have h1 : ‖(h - (inner ℝ (‖P‖⁻¹ • P) h : ℝ) • (‖P‖⁻¹ • P) : E)‖ ≤ ‖h‖ :=
        hproj _ h hnnorm
      have h2 := norm_add_le
        ((z' - z) - (inner ℝ (‖P‖⁻¹ • P) (z' - z) : ℝ) • (‖P‖⁻¹ • P))
        (h - (inner ℝ (‖P‖⁻¹ • P) h : ℝ) • (‖P‖⁻¹ • P))
      linarith [hθH.le]
  have hinC' : ∀ h : E, ‖h‖ ≤ θ * H / 2 → z' + h ∈ FitCylinder z' H (θ ^ 2) P' := by
    intro h hh
    refine hmem P' H z' h ?_ ?_
    · have h1 := haxle (‖P'‖⁻¹ • P' : E) h hn'norm
      linarith
    · have h1 := hproj (‖P'‖⁻¹ • P' : E) h hn'norm
      linarith [hθH.le]
  have hz'C : z' ∈ FitCylinder z H (θ ^ 2) P := by
    simpa using hinC 0 (by rw [norm_zero]; positivity)
  have hfz' := hfit.2 z' hz'C
  -- Step 2: the two fits differ by at most 3θ²H on increments from z'.
  have hdiff : ∀ h : E, z' + h ∈ FitCylinder z H (θ ^ 2) P →
      z' + h ∈ FitCylinder z' H (θ ^ 2) P' →
      |(inner ℝ (P - P') h : ℝ)| ≤ 3 * (θ ^ 2 * H) := by
    intro h hC hC'
    have e1 := hfit.2 (z' + h) hC
    have e2 := hfit'.2 (z' + h) hC'
    rw [add_sub_cancel_left] at e2
    have ed : z' + h - z = (z' - z) + h := by abel
    rw [ed, inner_add_right] at e1
    rw [inner_sub_left, abs_le]
    rw [abs_le] at e1 e2 hfz'
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2, hfz'.1, hfz'.2]
  have hvec : ‖P - P'‖ ≤ 6 * θ := by
    rcases eq_or_ne P P' with h | h
    · rw [h, sub_self, norm_zero]; linarith
    · have hne : P - P' ≠ 0 := sub_ne_zero.mpr h
      have hnpos : (0:ℝ) < ‖P - P'‖ := norm_pos_iff.mpr hne
      have hc0 : (0:ℝ) < θ * H / 2 * ‖P - P'‖⁻¹ := by positivity
      have hwn : ‖((θ * H / 2 * ‖P - P'‖⁻¹) • (P - P') : E)‖ = θ * H / 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
        field_simp
      have hinner : (inner ℝ (P - P') ((θ * H / 2 * ‖P - P'‖⁻¹) • (P - P')) : ℝ)
          = θ * H / 2 * ‖P - P'‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hd := hdiff ((θ * H / 2 * ‖P - P'‖⁻¹) • (P - P'))
        (hinC _ (le_of_eq hwn)) (hinC' _ (le_of_eq hwn))
      rw [hinner, abs_of_pos (by positivity : (0:ℝ) < θ * H / 2 * ‖P - P'‖)] at hd
      nlinarith [hd, hθH]
  -- Step 2b: the direction bound.
  have hinvle : ‖P‖⁻¹ ≤ c₁⁻¹ := by
    have hP0 : ‖P‖ ≠ 0 := hPpos.ne'
    have e : c₁⁻¹ - ‖P‖⁻¹ = (‖P‖ - c₁) / (c₁ * ‖P‖) := by field_simp
    have h0 : 0 ≤ (‖P‖ - c₁) / (c₁ * ‖P‖) :=
      div_nonneg (by linarith) (mul_pos hc hPpos).le
    rw [← e] at h0
    linarith
  have hdir : ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ≤ 12 * θ / c₁ := by
    have hsplit : (‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'
        = ‖P‖⁻¹ • (P - P') + (‖P‖⁻¹ - ‖P'‖⁻¹) • P' := by
      rw [smul_sub, sub_smul]; abel
    have h1 : ‖(‖P‖⁻¹ • (P - P') : E)‖ = ‖P‖⁻¹ * ‖P - P'‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hPpos)]
    have h2 : ‖((‖P‖⁻¹ - ‖P'‖⁻¹) • P' : E)‖ = |‖P‖⁻¹ - ‖P'‖⁻¹| * ‖P'‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    have h3 : |‖P‖⁻¹ - ‖P'‖⁻¹| * ‖P'‖ ≤ ‖P‖⁻¹ * ‖P - P'‖ :=
      hscalar ‖P‖ ‖P'‖ ‖P - P'‖ hPpos hP'pos
        (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le P P')
    have htri : ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖
        ≤ ‖P‖⁻¹ * ‖P - P'‖ + ‖P‖⁻¹ * ‖P - P'‖ := by
      rw [hsplit]
      calc ‖(‖P‖⁻¹ • (P - P') : E) + (‖P‖⁻¹ - ‖P'‖⁻¹) • P'‖
          ≤ ‖(‖P‖⁻¹ • (P - P') : E)‖ + ‖((‖P‖⁻¹ - ‖P'‖⁻¹) • P' : E)‖ := norm_add_le _ _
        _ ≤ ‖P‖⁻¹ * ‖P - P'‖ + ‖P‖⁻¹ * ‖P - P'‖ := by rw [h1, h2]; linarith
    have s1 : ‖P‖⁻¹ * ‖P - P'‖ ≤ c₁⁻¹ * ‖P - P'‖ :=
      mul_le_mul_of_nonneg_right hinvle (norm_nonneg _)
    have s2 : c₁⁻¹ * ‖P - P'‖ ≤ c₁⁻¹ * (6 * θ) :=
      mul_le_mul_of_nonneg_left hvec (inv_pos.mpr hc).le
    have s3 : (12:ℝ) * θ / c₁ = 2 * (c₁⁻¹ * (6 * θ)) := by field_simp; ring
    linarith
  -- Step 3: the point z' + γH n' lies in both cylinders.
  have hwn2 : ‖((γ * H) • (‖P'‖⁻¹ • P') : E)‖ = γ * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hγ0 hH), hn'norm, mul_one]
  have hγH4 : γ * H ≤ H / 4 := by nlinarith
  have hseg' : z' + (γ * H) • (‖P'‖⁻¹ • P') ∈ FitCylinder z' H (θ ^ 2) P' := by
    refine hmem P' H z' _ ?_ ?_
    · have h1 := haxle (‖P'‖⁻¹ • P' : E) ((γ * H) • (‖P'‖⁻¹ • P')) hn'norm
      rw [hwn2] at h1
      linarith
    · have e : ((γ * H) • (‖P'‖⁻¹ • P') : E)
          - (inner ℝ (‖P'‖⁻¹ • P') ((γ * H) • (‖P'‖⁻¹ • P')) : ℝ) • (‖P'‖⁻¹ • P') = 0 := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hn'norm]
        simp
      rw [e, norm_zero]
      positivity
  have hseg : z' + (γ * H) • (‖P'‖⁻¹ • P') ∈ FitCylinder z H (θ ^ 2) P := by
    rw [hshift]
    refine hmem P H z ((z' - z) + (γ * H) • (‖P'‖⁻¹ • P')) ?_ ?_
    · have h2 : |(inner ℝ (‖P‖⁻¹ • P) ((z' - z) + (γ * H) • (‖P'‖⁻¹ • P')) : ℝ)|
          ≤ |(inner ℝ (‖P‖⁻¹ • P) (z' - z) : ℝ)|
            + |(inner ℝ (‖P‖⁻¹ • P) ((γ * H) • (‖P'‖⁻¹ • P')) : ℝ)| := by
        rw [inner_add_right]; exact abs_add_le _ _
      have h1 := haxle (‖P‖⁻¹ • P : E) ((γ * H) • (‖P'‖⁻¹ • P')) hnnorm
      rw [hwn2] at h1
      linarith
    · rw [hsplitproj]
      have e : ((γ * H) • (‖P'‖⁻¹ • P') : E)
          - (inner ℝ (‖P‖⁻¹ • P) ((γ * H) • (‖P'‖⁻¹ • P')) : ℝ) • (‖P‖⁻¹ • P)
          = (γ * H) • ((‖P'‖⁻¹ • P' : E)
              - (inner ℝ (‖P‖⁻¹ • P) (‖P'‖⁻¹ • P') : ℝ) • (‖P‖⁻¹ • P)) := by
        simp only [real_inner_smul_right, smul_sub, smul_smul, mul_assoc]
      have hb := hproj (‖P‖⁻¹ • P : E) ((‖P'‖⁻¹ • P' : E) - ‖P‖⁻¹ • P) hnnorm
      have hbnd : ‖(‖P'‖⁻¹ • P' : E)
          - (inner ℝ (‖P‖⁻¹ • P) (‖P'‖⁻¹ • P') : ℝ) • (‖P‖⁻¹ • P)‖
          ≤ ‖(‖P'‖⁻¹ • P' : E) - ‖P‖⁻¹ • P‖ := by
        rw [hprojid _ _ hnnorm]; exact hb
      have hdir' : ‖(‖P'‖⁻¹ • P' : E) - ‖P‖⁻¹ • P‖ ≤ 12 * θ / c₁ := by
        rw [norm_sub_rev]; exact hdir
      have hB : ‖(((γ * H) • (‖P'‖⁻¹ • P') : E)
          - (inner ℝ (‖P‖⁻¹ • P) ((γ * H) • (‖P'‖⁻¹ • P')) : ℝ) • (‖P‖⁻¹ • P))‖
          ≤ θ * H / 4 := by
        rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hγ0 hH)]
        have k1 : γ * (12 / c₁) ≤ 1 / 4 := by
          have ee : γ * (12 / c₁) = 12 * γ / c₁ := by ring
          rw [ee, div_le_iff₀ hc]
          linarith
        have k2 : γ * H * (12 * θ / c₁) = γ * (12 / c₁) * (θ * H) := by field_simp
        have k3 : γ * H * ‖(‖P'‖⁻¹ • P' : E)
            - (inner ℝ (‖P‖⁻¹ • P) (‖P'‖⁻¹ • P') : ℝ) • (‖P‖⁻¹ • P)‖
            ≤ γ * H * (12 * θ / c₁) :=
          mul_le_mul_of_nonneg_left (le_trans hbnd hdir') (mul_pos hγ0 hH).le
        have k4 : γ * (12 / c₁) * (θ * H) ≤ 1 / 4 * (θ * H) :=
          mul_le_mul_of_nonneg_right k1 hθH.le
        rw [k2] at k3
        linarith
      have h2 := norm_add_le
        ((z' - z) - (inner ℝ (‖P‖⁻¹ • P) (z' - z) : ℝ) • (‖P‖⁻¹ • P))
        (((γ * H) • (‖P'‖⁻¹ • P') : E)
          - (inner ℝ (‖P‖⁻¹ • P) ((γ * H) • (‖P'‖⁻¹ • P')) : ℝ) • (‖P‖⁻¹ • P))
      linarith [hθH.le]
  -- Step 4: the axial component of the slope difference, measured against n'.
  have haxial : |(inner ℝ (P - P') (‖P'‖⁻¹ • P') : ℝ)| ≤ 3 * θ ^ 2 / γ := by
    have hd := hdiff ((γ * H) • (‖P'‖⁻¹ • P')) hseg hseg'
    rw [real_inner_smul_right, abs_mul, abs_of_pos (mul_pos hγ0 hH)] at hd
    rw [le_div_iff₀ hγ0]
    nlinarith [hd, hH, abs_nonneg (inner ℝ (P - P') (‖P'‖⁻¹ • P') : ℝ)]
  -- Step 5: the norm bound, and assembling both conclusions.
  have hP'n : (inner ℝ P' (‖P'‖⁻¹ • P') : ℝ) = ‖P'‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hPn' : (inner ℝ P (‖P'‖⁻¹ • P') : ℝ)
      = ‖P‖ * (inner ℝ (‖P‖⁻¹ • P) (‖P'‖⁻¹ • P') : ℝ) := by
    rw [real_inner_smul_left]
    field_simp
  have hcos : (inner ℝ (‖P‖⁻¹ • P) (‖P'‖⁻¹ • P') : ℝ)
      = 1 - ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2 := by
    have h := norm_sub_sq_real (‖P‖⁻¹ • P : E) (‖P'‖⁻¹ • P')
    rw [hnnorm, hn'norm] at h
    norm_num at h
    linarith
  have hsqdir : ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 ≤ (12 * θ / c₁) ^ 2 := by
    nlinarith [hdir, norm_nonneg ((‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P')]
  have hnorm : |‖P‖ - ‖P'‖| ≤ (3 / γ + 72 * C₁ / c₁ ^ 2) * θ ^ 2 := by
    have hid : ‖P‖ - ‖P'‖ = (inner ℝ (P - P') (‖P'‖⁻¹ • P') : ℝ)
        + ‖P‖ * (‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2) := by
      rw [inner_sub_left, hP'n, hPn', hcos]
      ring
    have hnn : (0:ℝ) ≤ ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2 := by positivity
    have hsq12 : (12 * θ / c₁) ^ 2 = 144 * θ ^ 2 / c₁ ^ 2 := by field_simp; ring
    have hterm : ‖P‖ * (‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2)
        ≤ C₁ * (144 * θ ^ 2 / c₁ ^ 2 / 2) := by
      refine mul_le_mul hPC ?_ hnn (le_trans hc.le (le_trans hcP hPC))
      rw [← hsq12]
      linarith
    have hSnn : (0:ℝ) ≤ ‖P‖ * (‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2) :=
      mul_nonneg hPpos.le hnn
    have hBnn : (0:ℝ) ≤ C₁ * (144 * θ ^ 2 / c₁ ^ 2 / 2) :=
      mul_nonneg (by linarith)
        (div_nonneg (div_nonneg (by positivity) (sq_nonneg c₁)) (by norm_num))
    have hRHS : (3 / γ + 72 * C₁ / c₁ ^ 2) * θ ^ 2
        = 3 * θ ^ 2 / γ + C₁ * (144 * θ ^ 2 / c₁ ^ 2 / 2) := by
      field_simp
      ring
    rw [abs_le] at haxial
    rw [abs_le, hRHS]
    constructor <;> linarith [haxial.1, haxial.2, hterm, hid, hSnn, hBnn]
  refine ⟨?_, ?_⟩
  · have hsum : ‖P - P'‖ + ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ≤ (6 + 12 / c₁) * θ := by
      have e : (6 + 12 / c₁) * θ = 6 * θ + 12 * θ / c₁ := by field_simp
      rw [e]
      linarith
    exact le_trans hsum (mul_le_mul_of_nonneg_right (le_max_left _ _) hθ0.le)
  · exact le_trans hnorm (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg θ))
