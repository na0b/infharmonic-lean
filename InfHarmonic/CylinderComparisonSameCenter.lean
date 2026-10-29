import InfHarmonic.IsCylinderFit
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma 3.5, common-center case: two cylinder fits of parameter `θ²` at the
same center, with comparable radii and slopes of comparable norms, have slopes
agreeing to `O(θ)` and norms agreeing to `O(θ²)`. -/
theorem CylinderComparisonSameCenter (c₁ C₁ : ℝ) (hc : 0 < c₁) (hcC : c₁ ≤ C₁) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : E → ℝ) (z : E) (θ H H' : ℝ) (P P' : E),
      0 < θ → θ < 1 → 0 < H → H ≤ H' → H' ≤ 2 * H →
      c₁ ≤ ‖P‖ → ‖P‖ ≤ C₁ → c₁ ≤ ‖P'‖ → ‖P'‖ ≤ C₁ →
      IsCylinderFit u z H (θ ^ 2) P → IsCylinderFit u z H' (θ ^ 2) P' →
      ‖P - P'‖ + ‖‖P‖⁻¹ • P - ‖P'‖⁻¹ • P'‖ ≤ C * θ ∧
      |‖P‖ - ‖P'‖| ≤ C * θ ^ 2 := by
  -- The argument is dimension-free: `[FiniteDimensional ℝ E]` is carried by the statement
  -- because the paper's lemma lives in `ℝ^m`, but nothing below uses it. Recorded here
  -- so the node closes without a fresh `unusedSectionVars` warning.
  have _unused_fd : FiniteDimensional ℝ E := inferInstance
  -- `γ = min {1/2, c₁/12}`, used only through these three facts.
  obtain ⟨γ, hγ2, hγ12, hγ0⟩ : ∃ γ : ℝ, γ ≤ 1 / 2 ∧ γ ≤ c₁ / 12 ∧ 0 < γ :=
    ⟨min (1 / 2) (c₁ / 12), min_le_left _ _, min_le_right _ _,
      lt_min (by norm_num) (by linarith)⟩
  have hc' : c₁ ≠ 0 := hc.ne'
  -- Step 0a: the orthogonal-projection bound for a unit axis.
  have hproj : ∀ m h : E, ‖m‖ = 1 → ‖h - (inner ℝ m h : ℝ) • m‖ ≤ ‖h‖ := by
    intro m h hm
    have hsq : ‖h - (inner ℝ m h : ℝ) • m‖ ^ 2 ≤ ‖h‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, hm, mul_one,
        real_inner_comm h m]
      nlinarith [sq_abs (inner ℝ h m : ℝ), sq_nonneg (inner ℝ h m : ℝ)]
    have h' := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h'
  -- Step 0b: projecting off a unit axis only sees the difference from that axis.
  have hprojid : ∀ a b : E, ‖b‖ = 1 →
      a - (inner ℝ b a : ℝ) • b = (a - b) - (inner ℝ b (a - b) : ℝ) • b := by
    intro a b hb
    rw [inner_sub_right, real_inner_self_eq_norm_sq, hb]
    simp only [one_pow, sub_smul, one_smul]
    abel
  -- Step 0c: the scalar bound behind the normalization step.
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
  refine ⟨max (3 + 6 / c₁) (3 / γ + 18 * C₁ / c₁ ^ 2), ?_, ?_⟩
  · have h1 : (0:ℝ) < 6 / c₁ := div_pos (by norm_num) hc
    exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
  intro u z θ H H' P P' hθ0 hθ1 hH hHH' hH'2H hcP hPC hcP' hP'C hfit hfit'
  have hPpos : (0:ℝ) < ‖P‖ := lt_of_lt_of_le hc hcP
  have hP'pos : (0:ℝ) < ‖P'‖ := lt_of_lt_of_le hc hcP'
  have hH'0 : (0:ℝ) < H' := lt_of_lt_of_le hH hHH'
  have hnnorm : ‖(‖P‖⁻¹ • P : E)‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hPpos)
  have hn'norm : ‖(‖P'‖⁻¹ • P' : E)‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hP'pos)
  have hsqrt : Real.sqrt (θ ^ 2) = θ := Real.sqrt_sq hθ0.le
  have hθH : (0:ℝ) < θ * H := mul_pos hθ0 hH
  -- Step 0d: a point of the ambient space lies in a cylinder once its length and
  -- its transverse part are controlled.
  have hmem : ∀ (Q : E) (r : ℝ) (h : E), ‖(‖Q‖⁻¹ • Q : E)‖ = 1 → ‖h‖ ≤ r →
      ‖h - (inner ℝ (‖Q‖⁻¹ • Q) h : ℝ) • (‖Q‖⁻¹ • Q)‖ ≤ θ * r →
      z + h ∈ FitCylinder z r (θ ^ 2) Q := by
    intro Q r h hQ hr htr
    refine ⟨?_, ?_⟩
    · rw [add_sub_cancel_left]
      calc |(inner ℝ (‖Q‖⁻¹ • Q) h : ℝ)| ≤ ‖(‖Q‖⁻¹ • Q : E)‖ * ‖h‖ :=
            abs_real_inner_le_norm _ _
        _ = ‖h‖ := by rw [hQ, one_mul]
        _ ≤ r := hr
    · rw [add_sub_cancel_left, hsqrt]
      exact htr
  -- Step 1 and Step 2: the two fits differ by at most `3θ²H` on `B̄_{θH}(z)`.
  have hdiff : ∀ h : E, ‖h‖ ≤ θ * H → |(inner ℝ (P - P') h : ℝ)| ≤ 3 * (θ ^ 2 * H) := by
    intro h hh
    have hhH : ‖h‖ ≤ H := le_trans hh (by nlinarith)
    have h1 : z + h ∈ FitCylinder z H (θ ^ 2) P :=
      hmem P H h hnnorm hhH (le_trans (hproj _ h hnnorm) hh)
    have h2 : z + h ∈ FitCylinder z H' (θ ^ 2) P' :=
      hmem P' H' h hn'norm (le_trans hhH hHH')
        (le_trans (hproj _ h hn'norm)
          (le_trans hh (mul_le_mul_of_nonneg_left hHH' hθ0.le)))
    have e1 := hfit.2 (z + h) h1
    have e2 := hfit'.2 (z + h) h2
    rw [add_sub_cancel_left] at e1 e2
    have hbd : θ ^ 2 * H' ≤ 2 * (θ ^ 2 * H) := by nlinarith [sq_nonneg θ]
    rw [inner_sub_left, abs_le]
    rw [abs_le] at e1 e2
    constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
  have hvec : ‖P - P'‖ ≤ 3 * θ := by
    rcases eq_or_ne P P' with h | h
    · rw [h, sub_self, norm_zero]; linarith
    · have hne : P - P' ≠ 0 := sub_ne_zero.mpr h
      have hnpos : (0:ℝ) < ‖P - P'‖ := norm_pos_iff.mpr hne
      have hc0 : (0:ℝ) < θ * H * ‖P - P'‖⁻¹ := mul_pos hθH (inv_pos.mpr hnpos)
      have hwn : ‖((θ * H * ‖P - P'‖⁻¹) • (P - P') : E)‖ = θ * H := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
        field_simp
      have hinner : (inner ℝ (P - P') ((θ * H * ‖P - P'‖⁻¹) • (P - P')) : ℝ)
          = θ * H * ‖P - P'‖ := by
        rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hd := hdiff _ (le_of_eq hwn)
      rw [hinner, abs_of_pos (mul_pos hθH hnpos)] at hd
      nlinarith [hd, hθH]
  -- Step 3: the direction bound.
  have hinvle : ‖P‖⁻¹ ≤ c₁⁻¹ := by
    have hP0 : ‖P‖ ≠ 0 := hPpos.ne'
    have e : c₁⁻¹ - ‖P‖⁻¹ = (‖P‖ - c₁) / (c₁ * ‖P‖) := by field_simp
    have h0 : 0 ≤ (‖P‖ - c₁) / (c₁ * ‖P‖) :=
      div_nonneg (by linarith) (mul_pos hc hPpos).le
    rw [← e] at h0
    linarith
  have hdir : ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ≤ 6 * θ / c₁ := by
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
    have s2 : c₁⁻¹ * ‖P - P'‖ ≤ c₁⁻¹ * (3 * θ) :=
      mul_le_mul_of_nonneg_left hvec (inv_pos.mpr hc).le
    have s3 : (6:ℝ) * θ / c₁ = 2 * (c₁⁻¹ * (3 * θ)) := by field_simp; ring
    linarith
  -- Step 4: the axis point `z + γH n` lies in both cylinders.
  have hwn2 : ‖((γ * H) • (‖P‖⁻¹ • P) : E)‖ = γ * H := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hγ0 hH), hnnorm, mul_one]
  have hγH : γ * H ≤ H := by nlinarith
  have hax1 : z + (γ * H) • (‖P‖⁻¹ • P) ∈ FitCylinder z H (θ ^ 2) P := by
    refine hmem P H _ hnnorm (by rw [hwn2]; exact hγH) ?_
    have e : ((γ * H) • (‖P‖⁻¹ • P) : E)
        - (inner ℝ (‖P‖⁻¹ • P) ((γ * H) • (‖P‖⁻¹ • P)) : ℝ) • (‖P‖⁻¹ • P) = 0 := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hnnorm]
      simp
    rw [e, norm_zero]
    positivity
  have hax2 : z + (γ * H) • (‖P‖⁻¹ • P) ∈ FitCylinder z H' (θ ^ 2) P' := by
    refine hmem P' H' _ hn'norm (by rw [hwn2]; linarith) ?_
    have e : ((γ * H) • (‖P‖⁻¹ • P) : E)
        - (inner ℝ (‖P'‖⁻¹ • P') ((γ * H) • (‖P‖⁻¹ • P)) : ℝ) • (‖P'‖⁻¹ • P')
        = (γ * H) • ((‖P‖⁻¹ • P : E)
            - (inner ℝ (‖P'‖⁻¹ • P') (‖P‖⁻¹ • P) : ℝ) • (‖P'‖⁻¹ • P')) := by
      simp only [real_inner_smul_right, smul_sub, smul_smul, mul_assoc]
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hγ0 hH),
      hprojid _ _ hn'norm]
    have hb := hproj (‖P'‖⁻¹ • P' : E) ((‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P') hn'norm
    have hstep : γ * H * ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ≤ γ * H * (6 * θ / c₁) :=
      mul_le_mul_of_nonneg_left hdir (mul_pos hγ0 hH).le
    have hgoal : γ * H * (6 * θ / c₁) ≤ θ * H' := by
      have h1 : γ * (6 / c₁) ≤ 1 / 2 := by
        have e : γ * (6 / c₁) = 6 * γ / c₁ := by ring
        rw [e, div_le_iff₀ hc]
        linarith
      have h2 : γ * H * (6 * θ / c₁) = γ * (6 / c₁) * (θ * H) := by field_simp
      have h3 : γ * (6 / c₁) * (θ * H) ≤ 1 / 2 * (θ * H) :=
        mul_le_mul_of_nonneg_right h1 hθH.le
      have h4 : θ * H ≤ θ * H' := mul_le_mul_of_nonneg_left hHH' hθ0.le
      rw [h2]
      linarith
    calc γ * H * ‖((‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P')
          - (inner ℝ (‖P'‖⁻¹ • P') ((‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P') : ℝ) • (‖P'‖⁻¹ • P')‖
        ≤ γ * H * ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ :=
          mul_le_mul_of_nonneg_left hb (mul_pos hγ0 hH).le
      _ ≤ θ * H' := le_trans hstep hgoal
  -- Step 5: the axial component of the slope difference.
  have haxial : |(inner ℝ (P - P') (‖P‖⁻¹ • P) : ℝ)| ≤ 3 * θ ^ 2 / γ := by
    have e1 := hfit.2 _ hax1
    have e2 := hfit'.2 _ hax2
    rw [add_sub_cancel_left, real_inner_smul_right] at e1 e2
    have hbd : θ ^ 2 * H' ≤ 2 * (θ ^ 2 * H) := by nlinarith [sq_nonneg θ]
    have hsub : |γ * H * ((inner ℝ P (‖P‖⁻¹ • P) : ℝ) - (inner ℝ P' (‖P‖⁻¹ • P) : ℝ))|
        ≤ 3 * (θ ^ 2 * H) := by
      rw [abs_le] at e1 e2 ⊢
      constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]
    rw [abs_mul, abs_of_pos (mul_pos hγ0 hH)] at hsub
    rw [inner_sub_left, le_div_iff₀ hγ0]
    nlinarith [hsub, hH,
      abs_nonneg ((inner ℝ P (‖P‖⁻¹ • P) : ℝ) - (inner ℝ P' (‖P‖⁻¹ • P) : ℝ))]
  -- Step 6: the norm bound, and assembling both conclusions.
  have hPn : (inner ℝ P (‖P‖⁻¹ • P) : ℝ) = ‖P‖ := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have hP'n : (inner ℝ P' (‖P‖⁻¹ • P) : ℝ)
      = ‖P'‖ * (inner ℝ (‖P'‖⁻¹ • P') (‖P‖⁻¹ • P) : ℝ) := by
    rw [real_inner_smul_left]
    field_simp
  have hcos : (inner ℝ (‖P'‖⁻¹ • P') (‖P‖⁻¹ • P) : ℝ)
      = 1 - ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2 := by
    have h := norm_sub_sq_real (‖P‖⁻¹ • P : E) (‖P'‖⁻¹ • P')
    rw [hnnorm, hn'norm] at h
    norm_num at h
    rw [real_inner_comm]
    linarith
  have hsqdir : ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 ≤ (6 * θ / c₁) ^ 2 := by
    nlinarith [hdir, norm_nonneg ((‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P')]
  have hnorm : |‖P‖ - ‖P'‖| ≤ (3 / γ + 18 * C₁ / c₁ ^ 2) * θ ^ 2 := by
    have hid : ‖P‖ - ‖P'‖ = (inner ℝ (P - P') (‖P‖⁻¹ • P) : ℝ)
        - ‖P'‖ * (‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2) := by
      rw [inner_sub_left, hPn, hP'n, hcos]
      ring
    have hnn : (0:ℝ) ≤ ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2 := by positivity
    have hsq6 : (6 * θ / c₁) ^ 2 = 36 * θ ^ 2 / c₁ ^ 2 := by
      field_simp; ring
    have hterm : ‖P'‖ * (‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2)
        ≤ C₁ * (36 * θ ^ 2 / c₁ ^ 2 / 2) := by
      refine mul_le_mul hP'C ?_ hnn (le_trans hc.le (le_trans hcP hPC))
      rw [← hsq6]
      linarith
    have hSnn : (0:ℝ) ≤ ‖P'‖ * (‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ^ 2 / 2) :=
      mul_nonneg hP'pos.le hnn
    have hBnn : (0:ℝ) ≤ C₁ * (36 * θ ^ 2 / c₁ ^ 2 / 2) :=
      mul_nonneg (by linarith)
        (div_nonneg (div_nonneg (by positivity) (sq_nonneg c₁)) (by norm_num))
    have hRHS : (3 / γ + 18 * C₁ / c₁ ^ 2) * θ ^ 2
        = 3 * θ ^ 2 / γ + C₁ * (36 * θ ^ 2 / c₁ ^ 2 / 2) := by
      field_simp
      ring
    rw [abs_le] at haxial
    rw [abs_le, hRHS]
    constructor <;> linarith [haxial.1, haxial.2, hterm, hid, hSnn, hBnn]
  refine ⟨?_, ?_⟩
  · have hsum : ‖P - P'‖ + ‖(‖P‖⁻¹ • P : E) - ‖P'‖⁻¹ • P'‖ ≤ (3 + 6 / c₁) * θ := by
      have e : (3 + 6 / c₁) * θ = 3 * θ + 6 * θ / c₁ := by field_simp
      rw [e]
      linarith
    exact le_trans hsum (mul_le_mul_of_nonneg_right (le_max_left _ _) hθ0.le)
  · exact le_trans hnorm (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg θ))
