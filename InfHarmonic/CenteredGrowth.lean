module

public import InfHarmonic.FitComparisonSameCenter
public import InfHarmonic.FrameInvariance
public import InfHarmonic.IsFitClass
public import InfHarmonic.IsCenteredAt

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.3): a centered member of `A_{m,C₀}` grows at most like
`C K L(K)²` on the box of size `K`, where `L(K) = 1 + log K`. -/
theorem CenteredGrowth (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      (IsCenteredAt C₀ v 0 ∨ IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ)))) →
      ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
        ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
        |v z| ≤ C * K * (1 + Real.log K) ^ 2 := by
  have hC₀0 : (0:ℝ) < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- the `WithLp` round trip, used to read a point as an increment from the origin
  have hrt : ∀ z : WithLp 2 (F × ℝ),
      (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := fun z => rfl
  -- The comparison constant of `FitComparisonSameCenter`, raised to be at least 1:
  -- its conclusion is an upper bound, so it survives the enlargement.  It is fixed
  -- first because Step 1's choice of `A` depends on it.
  obtain ⟨C₁, hC₁, hcmp⟩ : ∃ C₁ : ℝ, 1 ≤ C₁ ∧
      ∀ (v : WithLp 2 (F × ℝ) → ℝ) (z : WithLp 2 (F × ℝ)),
      (∀ ρ : ℝ, 0 < ρ → ∃ (q : F) (b : ℝ), IsFit C₀ v z ρ q b) →
      ∀ (R R' : ℝ) (p p' : F) (a a' : ℝ), 0 < R → 0 < R' →
        IsFit C₀ v z R p a → IsFit C₀ v z R' p' a' →
        ‖p - p'‖ + |a - a'| ≤ C₁ * (1 + |Real.log (R' / R)|) := by
    obtain ⟨C₁₀, hC₁₀, hcmp0⟩ := FitComparisonSameCenter (F := F) C₀ hC₀
    refine ⟨max C₁₀ 1, le_max_right _ _, ?_⟩
    intro v z hfits R R' p p' a a' hR hR' hf hf'
    refine (hcmp0 v z hfits R R' p p' a a' hR hR' hf hf').trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hC₁0 : (0:ℝ) < C₁ := lt_of_lt_of_le zero_lt_one hC₁
  -- STEP 1 : the choice of `A`, the node's one analytic extraction.
  -- `(3 + log A) / A → 0`, so `A` can be pushed past a fixed multiple of `1 + log A`.
  obtain ⟨A, hA4, hAbig⟩ : ∃ A : ℝ, 4 ≤ A ∧ 8 * C₁ * (3 + Real.log A) ≤ A := by
    have hc : (0:ℝ) < 1 / (16 * C₁) := by positivity
    have h := Real.isLittleO_log_id_atTop.def hc
    obtain ⟨A, ⟨hlog, hA4⟩, hAbig⟩ :=
      ((h.and (Filter.eventually_ge_atTop (4:ℝ))).and
        (Filter.eventually_ge_atTop (48 * C₁))).exists
    have hApos : (0:ℝ) < A := by linarith
    have hnormA : ‖(id A : ℝ)‖ = A := by simpa using abs_of_pos hApos
    have hlog' : Real.log A ≤ 1 / (16 * C₁) * A := by
      calc Real.log A ≤ ‖Real.log A‖ := le_abs_self _
        _ ≤ 1 / (16 * C₁) * ‖(id A : ℝ)‖ := hlog
        _ = 1 / (16 * C₁) * A := by rw [hnormA]
    refine ⟨A, hA4, ?_⟩
    have h3 : (3:ℝ) ≤ 1 / (16 * C₁) * A := by
      rw [one_div, inv_mul_eq_div, le_div_iff₀ (by positivity : (0:ℝ) < 16 * C₁)]
      linarith
    have key : 3 + Real.log A ≤ 2 * (1 / (16 * C₁)) * A := by linarith
    calc 8 * C₁ * (3 + Real.log A)
        ≤ 8 * C₁ * (2 * (1 / (16 * C₁)) * A) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = A := by field_simp; norm_num
  have hA0 : (0:ℝ) < A := by linarith
  have hlogA : 0 ≤ Real.log A := Real.log_nonneg (by linarith)
  -- `C₂ = C₁ (3 + log A)`, carried as an OPAQUE constant with exactly the three
  -- properties the proof uses; `A ≥ 8 C₂` is eq:cg-Achoice.
  obtain ⟨C₂, hC₂, hA8, hC₂key⟩ : ∃ C₂ : ℝ, 1 ≤ C₂ ∧ 8 * C₂ ≤ A ∧
      ∀ L : ℝ, 1 ≤ L → C₁ * (1 + Real.log A + 2 * L) ≤ C₂ * L := by
    refine ⟨C₁ * (3 + Real.log A), by nlinarith, by linarith, ?_⟩
    intro L hL
    have hkey : 1 + Real.log A + 2 * L ≤ (3 + Real.log A) * L := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hL) hlogA]
    calc C₁ * (1 + Real.log A + 2 * L)
        ≤ C₁ * ((3 + Real.log A) * L) := mul_le_mul_of_nonneg_left hkey hC₁0.le
      _ = C₁ * (3 + Real.log A) * L := by ring
  have hC₂0 : (0:ℝ) < C₂ := lt_of_lt_of_le zero_lt_one hC₂
  -- `C₃ = C₀ A + 2 C₂ + C₂² / 2`, again opaque, carrying the scalar endgame of Step 2
  obtain ⟨C₃, hC₃0, hC₃key⟩ : ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ K L : ℝ, 0 < K → 1 ≤ L →
      C₀ * (A * K * L) + C₂ * L * K + (C₂ * L + (C₂ * L) ^ 2 / 2) * K
        ≤ C₃ * K * L ^ 2 := by
    refine ⟨C₀ * A + 2 * C₂ + C₂ ^ 2 / 2, by positivity, ?_⟩
    intro K L hK hL
    have hd1 : (0:ℝ) ≤ C₀ * A * K * (L ^ 2 - L) :=
      mul_nonneg (by positivity) (by nlinarith)
    have hd2 : (0:ℝ) ≤ 2 * C₂ * K * (L ^ 2 - L) :=
      mul_nonneg (by positivity) (by nlinarith)
    nlinarith [hd1, hd2]
  -- eq:cg-ofb : the parameter bound at a center where `(0,0)` is a fit of radius 1
  have hofb : ∀ w : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ w → IsCenteredAt C₀ w 0 →
      ∀ (r : ℝ) (p : F) (a : ℝ), 0 < r → IsFit C₀ w 0 r p a →
        ‖p‖ + |a| ≤ C₁ * (1 + |Real.log r|) := by
    intro w hw hc r p a hr hf
    have hfits : ∀ ρ : ℝ, 0 < ρ → ∃ (q : F) (b : ℝ), IsFit C₀ w 0 ρ q b :=
      fun ρ hρ => hw.2 0 ρ hρ
    have h := hcmp w 0 hfits r 1 p 0 a 0 hr one_pos hf hc.2
    rwa [sub_zero, sub_zero, one_div, Real.log_inv, abs_neg] at h
  -- STEP 2 : eq:cg-origin, centering at the origin.  A SINGLE fit at radius
  -- `R = A K L(K)`; the `L(K) ^ 2` comes from the `‖p‖ ^ 2 / 2` term, not from iterating.
  have horigin : ∀ w : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ w → IsCenteredAt C₀ w 0 →
      ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
        ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
        |w z| ≤ C₃ * K * (1 + Real.log K) ^ 2 := by
    intro w hw hc K hK z hzx hzt
    have hK0 : (0:ℝ) < K := by linarith
    have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
    obtain ⟨L, hLdef⟩ : ∃ L : ℝ, L = 1 + Real.log K := ⟨_, rfl⟩
    have hL1 : (1:ℝ) ≤ L := by rw [hLdef]; linarith
    have hL0 : (0:ℝ) < L := by linarith
    rw [← hLdef]
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = A * K * L := ⟨_, rfl⟩
    have hR0 : (0:ℝ) < R := by rw [hRdef]; positivity
    have hAK : (8:ℝ) ≤ A * K := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hA4) (sub_nonneg.mpr hK)]
    have hR1 : (1:ℝ) ≤ R := by
      rw [hRdef]
      linarith [mul_le_mul_of_nonneg_left hL1 (by linarith : (0:ℝ) ≤ A * K)]
    obtain ⟨p, a, hf⟩ := hw.2 0 R hR0
    -- eq:cg-param, through `log R = log A + log K + log L(K) ≤ log A + 2 L(K)`
    have hlogR : Real.log R ≤ Real.log A + 2 * L := by
      rw [hRdef, Real.log_mul (by positivity : A * K ≠ 0) (ne_of_gt hL0),
        Real.log_mul (ne_of_gt hA0) (ne_of_gt hK0)]
      have hls : Real.log L ≤ L := by
        have := Real.log_le_sub_one_of_pos hL0; linarith
      linarith
    have hpa : ‖p‖ + |a| ≤ C₂ * L := by
      have h := hofb w hw hc R p a hR0 hf
      rw [abs_of_nonneg (Real.log_nonneg hR1)] at h
      have h2 : C₁ * (1 + Real.log R) ≤ C₁ * (1 + Real.log A + 2 * L) :=
        mul_le_mul_of_nonneg_left (by linarith) hC₁0.le
      exact h.trans (h2.trans (hC₂key L hL1))
    have hp : ‖p‖ ≤ C₂ * L := by linarith [abs_nonneg a]
    have ha : |a| ≤ C₂ * L := by linarith [norm_nonneg p]
    -- both box conditions of the fit of radius `R`
    have hAL4 : (4:ℝ) ≤ A * L := by
      linarith [mul_le_mul_of_nonneg_left hL1 (by linarith : (0:ℝ) ≤ A)]
    have hbox1 : |(ofLp z).2| ≤ R := by
      rw [hRdef]
      linarith [mul_le_mul_of_nonneg_left hAL4 hK0.le, hzt, hK0.le]
    have hbox2 : ‖(ofLp z).1 - (ofLp z).2 • p‖ ≤ R := by
      have h1 : ‖(ofLp z).1 - (ofLp z).2 • p‖ ≤ ‖(ofLp z).1‖ + |(ofLp z).2| * ‖p‖ := by
        have h := norm_sub_le (ofLp z).1 ((ofLp z).2 • p)
        rwa [norm_smul, Real.norm_eq_abs] at h
      have h2 : |(ofLp z).2| * ‖p‖ ≤ K * (C₂ * L) :=
        mul_le_mul hzt hp (norm_nonneg p) hK0.le
      have h4 : (0:ℝ) ≤ (A - 8 * C₂) * (K * L) :=
        mul_nonneg (by linarith) (by positivity)
      have h5 : (0:ℝ) ≤ (C₂ * L - 1) * K := by
        refine mul_nonneg ?_ hK0.le
        linarith [mul_le_mul_of_nonneg_left hL1 hC₂0.le]
      have h6 : (0:ℝ) ≤ A * K * L := by positivity
      rw [hRdef]
      linarith [h1, h2, h4, h5, h6, hzx]
    -- the fit, read at the increment `z` from the origin
    have hfit := hf (ofLp z).1 (ofLp z).2 hbox1 hbox2
    rw [zero_add, hrt z, hc.1] at hfit
    -- Cauchy-Schwarz and the two scalar bounds
    have hcs : |(inner ℝ p (ofLp z).1 : ℝ)| ≤ C₂ * L * K :=
      (abs_real_inner_le_norm p (ofLp z).1).trans
        (mul_le_mul hp hzx (norm_nonneg _) (by positivity))
    have hat : |(a - ‖p‖ ^ 2 / 2) * (ofLp z).2| ≤ (C₂ * L + (C₂ * L) ^ 2 / 2) * K := by
      rw [abs_mul]
      have h1 : |a - ‖p‖ ^ 2 / 2| ≤ C₂ * L + (C₂ * L) ^ 2 / 2 := by
        have h2 := abs_sub a (‖p‖ ^ 2 / 2)
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖p‖ ^ 2 / 2)] at h2
        linarith [mul_self_le_mul_self (norm_nonneg p) hp]
      exact mul_le_mul h1 hzt (abs_nonneg _) (by positivity)
    -- name the deviation, so that rewriting `w z` cannot touch the bound itself
    obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = w z - 0 - (inner ℝ p (ofLp z).1 : ℝ)
        - (a - ‖p‖ ^ 2 / 2) * (ofLp z).2 := ⟨_, rfl⟩
    rw [← hXdef] at hfit
    have hdecomp : w z
        = X + (inner ℝ p (ofLp z).1 : ℝ) + (a - ‖p‖ ^ 2 / 2) * (ofLp z).2 := by
      rw [hXdef]; ring
    have habs : |w z| ≤ C₀ * (A * K * L) + C₂ * L * K
        + (C₂ * L + (C₂ * L) ^ 2 / 2) * K := by
      rw [← hRdef, hdecomp]
      calc |X + (inner ℝ p (ofLp z).1 : ℝ) + (a - ‖p‖ ^ 2 / 2) * (ofLp z).2|
          ≤ |X| + |(inner ℝ p (ofLp z).1 : ℝ)| + |(a - ‖p‖ ^ 2 / 2) * (ofLp z).2| :=
            abs_add_three _ _ _
        _ ≤ C₀ * R + C₂ * L * K + (C₂ * L + (C₂ * L) ^ 2 / 2) * K :=
            add_le_add (add_le_add hfit hcs) hat
    exact habs.trans (hC₃key K L hK0 hL1)
  -- the uniform constant
  refine ⟨2 * (1 + Real.log 2) ^ 2 * C₃ + 1, by positivity, ?_⟩
  intro v hv hcen K hK z hzx hzt
  have hK0 : (0:ℝ) < K := by linarith
  have hlogK : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hgrow : ∀ D : ℝ, D ≤ 2 * (1 + Real.log 2) ^ 2 * C₃ + 1 →
      D * K * (1 + Real.log K) ^ 2
        ≤ (2 * (1 + Real.log 2) ^ 2 * C₃ + 1) * K * (1 + Real.log K) ^ 2 := by
    intro D hD
    calc D * K * (1 + Real.log K) ^ 2 = D * (K * (1 + Real.log K) ^ 2) := by ring
      _ ≤ (2 * (1 + Real.log 2) ^ 2 * C₃ + 1) * (K * (1 + Real.log K) ^ 2) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ = (2 * (1 + Real.log 2) ^ 2 * C₃ + 1) * K * (1 + Real.log K) ^ 2 := by ring
  have hCfin : C₃ ≤ 2 * (1 + Real.log 2) ^ 2 * C₃ + 1 := by
    have h1 : (1:ℝ) ≤ (1 + Real.log 2) ^ 2 := by nlinarith [sq_nonneg (Real.log 2)]
    have h2 : (0:ℝ) ≤ C₃ * (2 * (1 + Real.log 2) ^ 2 - 1) :=
      mul_nonneg hC₃0.le (by linarith)
    nlinarith [h2]
  rcases hcen with hc0 | hc1
  · exact (horigin v hv hc0 K hK z hzx hzt).trans (hgrow C₃ hCfin)
  · -- STEP 3 : centering at `(0,1)`.  This is the DEGENERATE instance of
    -- `FrameInvariance`: the shear is the identity and the frame change is a pure
    -- time translation, and BOTH clauses of the centering come from that theorem.
    obtain ⟨z₀, hz₀def⟩ : ∃ z₀ : WithLp 2 (F × ℝ), z₀ = toLp 2 ((0:F), (1:ℝ)) := ⟨_, rfl⟩
    rw [← hz₀def] at hc1
    obtain ⟨hwclass, hwfit⟩ := FrameInvariance C₀ v hv z₀ 1 one_pos (0 : F) (0 : ℝ)
    obtain ⟨w, hwdef⟩ : ∃ w : WithLp 2 (F × ℝ) → ℝ, w = FrameChange v z₀ 1 0 0 :=
      ⟨_, rfl⟩
    rw [← hwdef] at hwclass hwfit
    have hbar : ∀ ζ : WithLp 2 (F × ℝ), w ζ = v (z₀ + ζ) - v z₀ := by
      intro ζ
      rw [hwdef]
      simp only [FrameChange, smul_zero, add_zero, one_smul, one_mul, div_one,
        inner_zero_left, norm_zero]
      rw [hrt ζ]
      ring
    -- `w` is centered at the origin, both clauses coming from `FrameInvariance`
    have hcw : IsCenteredAt C₀ w 0 := by
      refine ⟨by rw [hbar 0, add_zero]; exact sub_self _, ?_⟩
      have hz00 : (toLp 2 ((0:F), (0:ℝ)) : WithLp 2 (F × ℝ)) = 0 := rfl
      have h := hwfit 0 1 0 0 (by simpa [hz00] using hc1.2)
      simpa using h
    -- transfer the point and the box to the translated function
    have hzz : v z = w (z - z₀) := by
      rw [hbar (z - z₀), add_sub_cancel, hc1.1, sub_zero]
    have hb1 : ‖(ofLp (z - z₀)).1‖ ≤ 2 * K := by
      have h : (ofLp (z - z₀)).1 = (ofLp z).1 := by rw [hz₀def]; simp
      rw [h]; linarith
    have hb2 : |(ofLp (z - z₀)).2| ≤ 2 * K := by
      have h : (ofLp (z - z₀)).2 = (ofLp z).2 - 1 := by rw [hz₀def]; simp
      rw [h]
      have h2 := abs_sub (ofLp z).2 (1:ℝ)
      rw [abs_one] at h2
      linarith
    have horig := horigin w hwclass hcw (2 * K) (by linarith) (z - z₀) hb1 hb2
    -- `L(2K) ≤ (1 + log 2) L(K)`
    have hL2K : 1 + Real.log (2 * K) ≤ (1 + Real.log 2) * (1 + Real.log K) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hK0)]
      nlinarith [mul_nonneg hlog2.le hlogK]
    have hL2K0 : (0:ℝ) ≤ 1 + Real.log (2 * K) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hK0)]; linarith
    have hsq : (1 + Real.log (2 * K)) ^ 2
        ≤ ((1 + Real.log 2) * (1 + Real.log K)) ^ 2 := by
      refine sq_le_sq' ?_ hL2K
      have hprod : (0:ℝ) ≤ (1 + Real.log 2) * (1 + Real.log K) :=
        mul_nonneg (by linarith) (by linarith)
      linarith
    rw [hzz]
    refine horig.trans ?_
    calc C₃ * (2 * K) * (1 + Real.log (2 * K)) ^ 2
        ≤ C₃ * (2 * K) * ((1 + Real.log 2) * (1 + Real.log K)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = 2 * (1 + Real.log 2) ^ 2 * C₃ * K * (1 + Real.log K) ^ 2 := by ring
      _ ≤ (2 * (1 + Real.log 2) ^ 2 * C₃ + 1) * K * (1 + Real.log K) ^ 2 :=
          hgrow _ (by linarith)
