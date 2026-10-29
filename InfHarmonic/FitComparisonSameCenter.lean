import InfHarmonic.IsFit
open WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.2): for a function admitting a fit at `z` of every positive
radius, any two fits at `z` have parameters differing by
`C (1 + |log (R'/R)|)`. -/
theorem FitComparisonSameCenter (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)),
      (∀ ρ : ℝ, 0 < ρ → ∃ (q : F) (b : ℝ), IsFit C₀ v z ρ q b) →
      ∀ (R R' : ℝ) (p p' : F) (a a' : ℝ), 0 < R → 0 < R' →
        IsFit C₀ v z R p a → IsFit C₀ v z R' p' a' →
        ‖p - p'‖ + |a - a'| ≤ C * (1 + |Real.log (R' / R)|) := by
  -- the argument is dimension-free; `pm-0003` keeps the ambient hypothesis in the
  -- statement, so the unused-section-variable warning is silenced here.
  have _unused_fd : FiniteDimensional ℝ F := inferInstance
  have hC₀0 : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have habs2 : ∀ x y : ℝ, |x - y| ≤ |x| + |y| := fun x y => abs_sub x y
  set C₁ : ℝ := 4 * C₀ + 3 * C₀ * (2 + 8 * C₀) + 8 * C₀ ^ 2 with hC₁def
  have hC₁ : (0:ℝ) < C₁ := by rw [hC₁def]; positivity
  have hfac : (0:ℝ) < 2 + 1 / Real.log 2 := by positivity
  refine ⟨C₁ * (2 + 1 / Real.log 2), mul_pos hC₁ hfac, ?_⟩
  intro v z hfits
  -- Step 1: comparable radii.
  have hadj : ∀ (R R' : ℝ) (p p' : F) (a a' : ℝ), 0 < R → R ≤ R' → R' ≤ 2 * R →
      IsFit C₀ v z R p a → IsFit C₀ v z R' p' a' →
      ‖p - p'‖ + |a - a'| ≤ C₁ := by
    intro R R' p p' a a' hR hRR' hR'2 hf hf'
    have hR'0 : 0 < R' := lt_of_lt_of_le hR hRR'
    -- 1a: the horizontal slice `l = 0` bounds `‖p - p'‖`
    have hslice : ∀ h : F, ‖h‖ ≤ R → |(inner ℝ (p - p') h : ℝ)| ≤ 3 * C₀ * R := by
      intro h hh
      have h1 := hf h 0 (by simpa using hR.le) (by simpa using hh)
      have h2 := hf' h 0 (by simpa using hR'0.le) (by simpa using hh.trans hRR')
      simp only [mul_zero, sub_zero] at h1 h2
      have ha1 := abs_le.mp h1
      have ha2 := abs_le.mp h2
      have hCR : C₀ * R' ≤ 2 * (C₀ * R) := by nlinarith [hC₀0.le, hR'2]
      rw [inner_sub_left, abs_le]
      constructor <;> linarith [ha1.1, ha1.2, ha2.1, ha2.2]
    have hp : ‖p - p'‖ ≤ 3 * C₀ := by
      rcases eq_or_ne p p' with rfl | hne
      · rw [sub_self, norm_zero]; positivity
      · have hpos : 0 < ‖p - p'‖ := by
          rw [norm_pos_iff]; exact sub_ne_zero_of_ne hne
        have hnm : ‖(R / ‖p - p'‖) • (p - p')‖ = R := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
          field_simp
        have hin : (inner ℝ (p - p') ((R / ‖p - p'‖) • (p - p')) : ℝ) = R * ‖p - p'‖ := by
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        have := hslice _ hnm.le
        rw [hin, abs_of_nonneg (by positivity)] at this
        have : R * ‖p - p'‖ ≤ R * (3 * C₀) := by linarith
        exact le_of_mul_le_mul_left this hR
    -- 1b: the sheared increment `(c R p, c R)` bounds `|a - a'|`
    obtain ⟨c, hc0, hc1, hc3, hcinv⟩ : ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ 3 * C₀ * c ≤ 1
        ∧ 3 * C₀ / c = 3 * C₀ * (2 + 8 * C₀) := by
      refine ⟨(2 + 8 * C₀)⁻¹, by positivity, ?_, ?_, ?_⟩
      · rw [inv_le_one_iff₀]; right; nlinarith [hC₀0.le]
      · rw [mul_inv_le_iff₀ (by positivity : (0:ℝ) < 2 + 8 * C₀)]; nlinarith [hC₀0.le]
      · field_simp
    have ht : (0:ℝ) < c * R := by positivity
    have htR : c * R ≤ R := by nlinarith [hR.le]
    have hbox2 : ‖(c * R) • p - (c * R) • p'‖ ≤ R' := by
      rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have h1 : c * R * ‖p - p'‖ ≤ c * R * (3 * C₀) :=
        mul_le_mul_of_nonneg_left hp ht.le
      refine h1.trans (le_trans ?_ hRR')
      nlinarith [hR.le, hc3]
    have hA := hf ((c * R) • p) (c * R) (by rw [abs_of_pos ht]; exact htR)
      (by simpa using hR.le)
    have hB := hf' ((c * R) • p) (c * R) (by rw [abs_of_pos ht]; exact htR.trans hRR') hbox2
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq] at hA
    rw [real_inner_smul_right] at hB
    have hnrm : ‖p - p'‖ ^ 2 = ‖p‖ ^ 2 - 2 * (inner ℝ p' p : ℝ) + ‖p'‖ ^ 2 := by
      rw [norm_sub_sq_real, real_inner_comm p p']
    have hid : (v (z + toLp 2 ((c * R) • p, c * R)) - v z - c * R * ‖p‖ ^ 2
          - (a - ‖p‖ ^ 2 / 2) * (c * R))
        - (v (z + toLp 2 ((c * R) • p, c * R)) - v z - c * R * (inner ℝ p' p : ℝ)
          - (a' - ‖p'‖ ^ 2 / 2) * (c * R))
        = -(c * R * (a - a' + ‖p - p'‖ ^ 2 / 2)) := by
      rw [hnrm]; ring
    have hdiff : |c * R * (a - a' + ‖p - p'‖ ^ 2 / 2)| ≤ C₀ * R + C₀ * R' := by
      have h := habs2
        (v (z + toLp 2 ((c * R) • p, c * R)) - v z - c * R * ‖p‖ ^ 2
          - (a - ‖p‖ ^ 2 / 2) * (c * R))
        (v (z + toLp 2 ((c * R) • p, c * R)) - v z - c * R * (inner ℝ p' p : ℝ)
          - (a' - ‖p'‖ ^ 2 / 2) * (c * R))
      rw [hid, abs_neg] at h
      exact h.trans (add_le_add hA hB)
    have hdiv : |a - a' + ‖p - p'‖ ^ 2 / 2| ≤ 3 * C₀ * (2 + 8 * C₀) := by
      rw [abs_mul, abs_of_pos ht] at hdiff
      have hCR : C₀ * R' ≤ 2 * (C₀ * R) := by nlinarith [hC₀0.le, hR'2]
      have h2 : c * R * |a - a' + ‖p - p'‖ ^ 2 / 2| ≤ 3 * C₀ * R := by linarith
      rw [← hcinv, le_div_iff₀ hc0]
      have h4 : (R * c) * |a - a' + ‖p - p'‖ ^ 2 / 2| ≤ R * (3 * C₀) := by
        calc (R * c) * |a - a' + ‖p - p'‖ ^ 2 / 2|
            = c * R * |a - a' + ‖p - p'‖ ^ 2 / 2| := by ring
          _ ≤ 3 * C₀ * R := h2
          _ = R * (3 * C₀) := by ring
      have h5 : R * (|a - a' + ‖p - p'‖ ^ 2 / 2| * c) ≤ R * (3 * C₀) := by
        calc R * (|a - a' + ‖p - p'‖ ^ 2 / 2| * c)
            = (R * c) * |a - a' + ‖p - p'‖ ^ 2 / 2| := by ring
          _ ≤ R * (3 * C₀) := h4
      exact le_of_mul_le_mul_left h5 hR
    have ha : |a - a'| ≤ 3 * C₀ * (2 + 8 * C₀) + 8 * C₀ ^ 2 := by
      have h1 := abs_le.mp hdiv
      have hpn : (0:ℝ) ≤ ‖p - p'‖ := norm_nonneg _
      have hsq : ‖p - p'‖ ^ 2 ≤ 16 * C₀ ^ 2 := by nlinarith [hp, hpn, hC₀0.le]
      rw [abs_le]
      constructor <;> linarith [h1.1, h1.2, sq_nonneg ‖p - p'‖]
    rw [hC₁def]
    linarith [hp, ha, hC₀0.le]
  -- Step 2: a dyadic chain between two arbitrary radii.
  have hchain : ∀ (k : ℕ) (R R' : ℝ) (p p' : F) (a a' : ℝ), 0 < R → R ≤ R' →
      R' ≤ 2 ^ k * R → IsFit C₀ v z R p a → IsFit C₀ v z R' p' a' →
      ‖p - p'‖ + |a - a'| ≤ ((k : ℝ) + 1) * C₁ := by
    intro k
    induction k with
    | zero =>
      intro R R' p p' a a' hR hRR' hle hf hf'
      rw [pow_zero, one_mul] at hle
      have h := hadj R R' p p' a a' hR hRR' (by linarith) hf hf'
      push_cast
      linarith
    | succ n ih =>
      intro R R' p p' a a' hR hRR' hle hf hf'
      have hn0 : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hexp : ((n : ℝ) + 1 + 1) * C₁ = C₁ + ((n : ℝ) + 1) * C₁ := by ring
      have hprod : (0:ℝ) ≤ ((n : ℝ) + 1) * C₁ := by positivity
      push_cast
      rcases le_or_gt R' (2 * R) with hsmall | hbig
      · have h := hadj R R' p p' a a' hR hRR' hsmall hf hf'
        rw [hexp]
        linarith
      · obtain ⟨q, b, hq⟩ := hfits (2 * R) (by linarith)
        have h1 := hadj R (2 * R) p q a b hR (by linarith) (le_refl _) hf hq
        have hle2 : R' ≤ 2 ^ n * (2 * R) := by
          calc R' ≤ 2 ^ (n + 1) * R := hle
            _ = 2 ^ n * (2 * R) := by rw [pow_succ]; ring
        have h2 := ih (2 * R) R' q p' b a' (by linarith) (by linarith) hle2 hq hf'
        have ht1 : ‖p - p'‖ ≤ ‖p - q‖ + ‖q - p'‖ := by
          calc ‖p - p'‖ = ‖(p - q) + (q - p')‖ := by rw [sub_add_sub_cancel]
            _ ≤ ‖p - q‖ + ‖q - p'‖ := norm_add_le _ _
        have ht2 : |a - a'| ≤ |a - b| + |b - a'| := abs_sub_le a b a'
        rw [hexp]
        linarith
  -- Step 3: bounding the number of doublings, in the ordered case.
  have hord : ∀ (R R' : ℝ) (p p' : F) (a a' : ℝ), 0 < R → R ≤ R' →
      IsFit C₀ v z R p a → IsFit C₀ v z R' p' a' →
      ‖p - p'‖ + |a - a'| ≤ C₁ * (2 + 1 / Real.log 2) * (1 + |Real.log (R' / R)|) := by
    intro R R' p p' a a' hR hRR' hf hf'
    have hR'0 : 0 < R' := lt_of_lt_of_le hR hRR'
    have hratio : 1 ≤ R' / R := (one_le_div hR).mpr hRR'
    have hlogr : 0 ≤ Real.log (R' / R) := Real.log_nonneg hratio
    set k : ℕ := ⌈Real.log (R' / R) / Real.log 2⌉₊ with hkdef
    have hxnn : 0 ≤ Real.log (R' / R) / Real.log 2 := by positivity
    have hkge : Real.log (R' / R) / Real.log 2 ≤ (k : ℝ) := Nat.le_ceil _
    have hklt : (k : ℝ) < Real.log (R' / R) / Real.log 2 + 1 := by
      rw [hkdef]; exact Nat.ceil_lt_add_one hxnn
    -- `R' ≤ 2 ^ k * R`
    have hpow : R' ≤ 2 ^ k * R := by
      have h1 : Real.log (R' / R) ≤ (k : ℝ) * Real.log 2 := by
        rw [div_le_iff₀ hlog2] at hkge; linarith
      have h2 : Real.log (R' / R) ≤ Real.log (2 ^ k) := by
        rw [Real.log_pow]; exact h1
      have h3 : R' / R ≤ 2 ^ k := by
        have := Real.exp_le_exp.mpr h2
        rwa [Real.exp_log (by positivity), Real.exp_log (by positivity)] at this
      rw [div_le_iff₀ hR] at h3
      linarith [h3]
    have h := hchain k R R' p p' a a' hR hRR' hpow hf hf'
    refine h.trans ?_
    have hkb : (k : ℝ) + 1 ≤ 2 + Real.log (R' / R) / Real.log 2 := by linarith
    have hstep : ((k : ℝ) + 1) * C₁ ≤ (2 + Real.log (R' / R) / Real.log 2) * C₁ :=
      mul_le_mul_of_nonneg_right hkb hC₁.le
    refine hstep.trans ?_
    rw [abs_of_nonneg hlogr]
    have hfin : (2 + Real.log (R' / R) / Real.log 2)
        ≤ (2 + 1 / Real.log 2) * (1 + Real.log (R' / R)) := by
      have hdd : Real.log (R' / R) / Real.log 2 = (1 / Real.log 2) * Real.log (R' / R) := by
        ring
      rw [hdd]
      have hinv : (0:ℝ) < 1 / Real.log 2 := by positivity
      nlinarith [hlogr, hinv.le]
    calc (2 + Real.log (R' / R) / Real.log 2) * C₁
        ≤ ((2 + 1 / Real.log 2) * (1 + Real.log (R' / R))) * C₁ :=
          mul_le_mul_of_nonneg_right hfin hC₁.le
      _ = C₁ * (2 + 1 / Real.log 2) * (1 + Real.log (R' / R)) := by ring
  -- conclude, symmetrising in the two radii
  intro R R' p p' a a' hR hR' hf hf'
  rcases le_total R R' with hle | hle
  · exact hord R R' p p' a a' hR hle hf hf'
  · have h := hord R' R p' p a' a hR' hle hf' hf
    rw [show ‖p' - p‖ = ‖p - p'‖ from by rw [← norm_neg, neg_sub],
      show |a' - a| = |a - a'| from abs_sub_comm a' a,
      show |Real.log (R / R')| = |Real.log (R' / R)| from by
        rw [show R / R' = (R' / R)⁻¹ from by rw [inv_div], Real.log_inv, abs_neg]] at h
    exact h
