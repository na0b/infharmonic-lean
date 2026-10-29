module

public import InfHarmonic.NonaffineSliceExists
public import InfHarmonic.HasJensenBound
public import InfHarmonic.FrameInvariance
public import InfHarmonic.TimeReversal
public import InfHarmonic.CenteredGrowth
public import InfHarmonic.IsSpaceTimeAffine

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (5.7): the supremum of the horizontal Jensen quotients of a
nonaffine centered member of `A_{m,C₀}` is positive and finite; after a time
reversal if necessary, there is a least admissible constant `κ > 0`. -/
theorem JensenSupremumFinite (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (v₀ : WithLp 2 (F × ℝ) → ℝ)
    (hv₀ : IsFitClass C₀ v₀) (hcent : IsCenteredAt C₀ v₀ 0)
    (hna : ¬ IsSpaceTimeAffine v₀) :
    ∃ (v : WithLp 2 (F × ℝ) → ℝ) (κ : ℝ),
      IsFitClass C₀ v ∧ IsCenteredAt C₀ v 0 ∧ ¬ IsSpaceTimeAffine v ∧
      0 < κ ∧ HasJensenBound Set.univ v κ ∧
      (∀ κ' : ℝ, HasJensenBound Set.univ v κ' → κ ≤ κ') := by
  classical
  -- ===== Step 0: the uniform quadratic growth bound for centered members =====
  have hnormsmul : ∀ (cs : ℝ) (w : F), ‖cs • w‖ ^ 2 = cs ^ 2 * ‖w‖ ^ 2 := by
    intro cs w; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hzz : (toLp 2 ((0 : F), (0 : ℝ)) : WithLp 2 (F × ℝ)) = 0 := rfl
  obtain ⟨Cg, hCg0, hCgb⟩ := CenteredGrowth (F := F) C₀ hC₀
  -- the log bootstrap: `(1 + log K)² ≤ 4K` for `K ≥ 2`, by passing to `√K`
  have hlogsq : ∀ K : ℝ, 2 ≤ K → (1 + Real.log K) ^ 2 ≤ 4 * K := by
    intro K hK
    have hK0 : (0 : ℝ) < K := by linarith
    have hsq : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK0.le
    have hsq0 : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr hK0
    have hlog2 : Real.log K = 2 * Real.log (Real.sqrt K) := by
      have h := Real.log_pow (Real.sqrt K) 2
      rw [hsq] at h
      push_cast at h
      linarith
    have hls : Real.log (Real.sqrt K) ≤ Real.sqrt K - 1 :=
      Real.log_le_sub_one_of_pos hsq0
    have hnn : (0 : ℝ) ≤ 1 + Real.log K := by
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ K); linarith
    have hub : 1 + Real.log K ≤ 2 * Real.sqrt K := by rw [hlog2]; linarith
    have hsqle := mul_self_le_mul_self hnn hub
    nlinarith [hsqle, hsq]
  have hquad : ∀ w : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ w → IsCenteredAt C₀ w 0 →
      ∀ u : F, |w (toLp 2 (u, (0 : ℝ)))| ≤ 16 * Cg * (1 + ‖u‖ ^ 2) := by
    intro w hw hwc u
    have hp1 : ‖(ofLp (toLp 2 (u, (0 : ℝ)) : WithLp 2 (F × ℝ))).1‖ = ‖u‖ := rfl
    have hp2 : (ofLp (toLp 2 (u, (0 : ℝ)) : WithLp 2 (F × ℝ))).2 = (0 : ℝ) := rfl
    rcases le_total ‖u‖ 2 with hu | hu
    · have hb := hCgb w hw (Or.inl hwc) 2 le_rfl (toLp 2 (u, (0 : ℝ)))
        (by rw [hp1]; exact hu) (by rw [hp2, abs_zero]; norm_num)
      have h2 := hlogsq 2 le_rfl
      nlinarith [hb, h2, hCg0, sq_nonneg ‖u‖, mul_nonneg hCg0.le (sq_nonneg ‖u‖)]
    · have hb := hCgb w hw (Or.inl hwc) ‖u‖ hu (toLp 2 (u, (0 : ℝ)))
        (by rw [hp1]) (by rw [hp2, abs_zero]; linarith)
      have h2 := hlogsq ‖u‖ hu
      have hm : Cg * ‖u‖ * (1 + Real.log ‖u‖) ^ 2 ≤ Cg * ‖u‖ * (4 * ‖u‖) :=
        mul_le_mul_of_nonneg_left h2 (mul_nonneg hCg0.le (norm_nonneg u))
      nlinarith [hb, hm, hCg0, mul_nonneg hCg0.le (sq_nonneg ‖u‖)]
  -- ===== Step 1: a two-point configuration with nonzero defect for `v₀` =====
  obtain ⟨t₁, w₁, w₂, hmid⟩ := NonaffineSliceExists C₀ hC₀ v₀ hv₀ hcent hna
  have hwne : w₁ ≠ w₂ := by
    intro h
    rw [h] at hmid
    apply hmid
    rw [show (2 : ℝ)⁻¹ • (w₂ + w₂) = w₂ from by module]
    ring
  obtain ⟨θv, hθv⟩ : ∃ f : Fin 2 → ℝ, f = fun _ => (1 / 2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨yv, hyv⟩ : ∃ f : Fin 2 → F, f = fun i => if i = 0 then w₁ else w₂ := ⟨_, rfl⟩
  obtain ⟨xv, hxv⟩ : ∃ u : F, u = (2 : ℝ)⁻¹ • (w₁ + w₂) := ⟨_, rfl⟩
  have hθv0 : θv 0 = (1 / 2 : ℝ) := by rw [hθv]
  have hθv1 : θv 1 = (1 / 2 : ℝ) := by rw [hθv]
  have hyv0 : yv 0 = w₁ := by rw [hyv]; simp
  have hyv1 : yv 1 = w₂ := by rw [hyv]; simp
  have hcfg₁ : IsBaryConfig 2 θv yv xv := by
    refine ⟨fun i => by rw [hθv]; norm_num, ?_, ?_⟩
    · rw [Fin.sum_univ_two, hθv0, hθv1]; norm_num
    · rw [Fin.sum_univ_two, hθv0, hθv1, hyv0, hyv1, hxv]; module
  have hsumsq : ∑ i, θv i * ‖yv i - xv‖ ^ 2
      = (1 / 2 : ℝ) * ‖w₁ - xv‖ ^ 2 + (1 / 2 : ℝ) * ‖w₂ - xv‖ ^ 2 := by
    rw [Fin.sum_univ_two, hθv0, hθv1, hyv0, hyv1]
  have hr₁ : 0 < BaryRadius 2 θv yv xv := by
    rw [BaryRadius, Real.sqrt_pos, hsumsq]
    have h1 : w₁ - xv = (2 : ℝ)⁻¹ • (w₁ - w₂) := by rw [hxv]; module
    have h2 : w₁ - xv ≠ 0 := by
      rw [h1]
      intro h
      exact hwne (sub_eq_zero.mp ((smul_eq_zero.mp h).resolve_left (by norm_num)))
    have h3 : (0 : ℝ) < ‖w₁ - xv‖ := norm_pos_iff.mpr h2
    nlinarith [sq_nonneg ‖w₂ - xv‖]
  have hD₁ : (∑ i, θv i * v₀ (toLp 2 (yv i, t₁))) - v₀ (toLp 2 (xv, t₁)) ≠ 0 := by
    rw [Fin.sum_univ_two, hθv0, hθv1, hyv0, hyv1, hxv]
    intro h
    exact hmid (by linarith)
  -- ===== Step 2: normalizing the sign of the defect =====
  obtain ⟨v, hvclass, hvcent, hvna, τ₁, nn, θθ, yy, xx, hcfg, hrad, hDpos⟩ :
      ∃ v : WithLp 2 (F × ℝ) → ℝ,
        IsFitClass C₀ v ∧ IsCenteredAt C₀ v 0 ∧ ¬ IsSpaceTimeAffine v ∧
        ∃ (τ : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
          IsBaryConfig n θ y x ∧ 0 < BaryRadius n θ y x ∧
          0 < (∑ i, θ i * v (toLp 2 (y i, τ))) - v (toLp 2 (x, τ)) := by
    rcases lt_or_gt_of_ne hD₁ with hneg | hpos
    · -- the defect is negative: pass to the time reversal
      have hflipval : ∀ (u : F) (σ : ℝ),
          TimeFlip v₀ (toLp 2 (u, σ)) = -v₀ (toLp 2 (u, -σ)) := by
        intro u σ; simp only [TimeFlip]
      obtain ⟨-, -, -, -, hTRfit, hTRclass, -⟩ := TimeReversal C₀ v₀
      have hzero : TimeFlip v₀ (0 : WithLp 2 (F × ℝ)) = 0 := by
        rw [← hzz, hflipval, neg_zero, hzz, hcent.1, neg_zero]
      have hpt : (toLp 2 ((ofLp (0 : WithLp 2 (F × ℝ))).1,
          -(ofLp (0 : WithLp 2 (F × ℝ))).2) : WithLp 2 (F × ℝ)) = 0 := by
        rw [show (ofLp (0 : WithLp 2 (F × ℝ))).1 = (0 : F) from rfl,
          show (ofLp (0 : WithLp 2 (F × ℝ))).2 = (0 : ℝ) from rfl, neg_zero]
        exact hzz
      have hfit := hTRfit (0 : WithLp 2 (F × ℝ)) 1 0 0 hcent.2
      rw [hpt, neg_zero] at hfit
      refine ⟨TimeFlip v₀, hTRclass hv₀, ⟨hzero, hfit⟩, ?_, -t₁, 2, θv, yv, xv,
        hcfg₁, hr₁, ?_⟩
      · rintro ⟨q, β, γ, hq⟩
        refine hna ⟨-q, β, -γ, ?_⟩
        intro z
        have h1 := hq (toLp 2 ((ofLp z).1, -(ofLp z).2))
        rw [show TimeFlip v₀ (toLp 2 ((ofLp z).1, -(ofLp z).2)) = -v₀ z from by
            rw [hflipval, neg_neg],
          show (ofLp (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ))).1
            = (ofLp z).1 from rfl,
          show (ofLp (toLp 2 ((ofLp z).1, -(ofLp z).2) : WithLp 2 (F × ℝ))).2
            = -(ofLp z).2 from rfl] at h1
        rw [inner_neg_left]
        linarith [h1]
      · have hs : ∀ i, θv i * TimeFlip v₀ (toLp 2 (yv i, -t₁))
            = -(θv i * v₀ (toLp 2 (yv i, t₁))) := by
          intro i; rw [hflipval, neg_neg]; ring
        rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_neg_distrib, hflipval, neg_neg]
        have h := hD₁
        linarith [hneg]
    · exact ⟨v₀, hv₀, hcent, hna, t₁, 2, θv, yv, xv, hcfg₁, hr₁, hpos⟩
  -- ===== Steps 3 and 4: the set of defect quotients, nonempty and bounded above =====
  obtain ⟨Q, hQdef⟩ : ∃ S : Set ℝ, S = {q : ℝ | ∃ (τ : ℝ) (n : ℕ) (θ : Fin n → ℝ)
      (y : Fin n → F) (x : F), IsBaryConfig n θ y x ∧ 0 < BaryRadius n θ y x ∧
      q = ((∑ i, θ i * v (toLp 2 (y i, τ))) - v (toLp 2 (x, τ)))
            / BaryRadius n θ y x} := ⟨_, rfl⟩
  have hQmem : ∀ q : ℝ, q ∈ Q ↔ ∃ (τ : ℝ) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
      IsBaryConfig n θ y x ∧ 0 < BaryRadius n θ y x ∧
      q = ((∑ i, θ i * v (toLp 2 (y i, τ))) - v (toLp 2 (x, τ)))
            / BaryRadius n θ y x := by
    intro q; rw [hQdef]; exact Iff.rfl
  have hQbdd : ∀ q ∈ Q, q ≤ 32 * Cg := by
    intro q hq
    obtain ⟨τ, n, θ, y, x, hcfg', hpos, rfl⟩ := (hQmem q).mp hq
    obtain ⟨hθpos, hθ1, hθmean⟩ := hcfg'
    obtain ⟨r, hrdef⟩ : ∃ s : ℝ, s = BaryRadius n θ y x := ⟨_, rfl⟩
    rw [← hrdef] at hpos ⊢
    have hrne : r ≠ 0 := ne_of_gt hpos
    -- the fit at the configuration's mean, and the frame change it generates
    obtain ⟨p, a, hfit⟩ := hvclass.2 (toLp 2 (x, τ)) r hpos
    obtain ⟨vb, hvbdef⟩ : ∃ w : WithLp 2 (F × ℝ) → ℝ,
        w = FrameChange v (toLp 2 (x, τ)) r p a := ⟨_, rfl⟩
    obtain ⟨hFIclass, hFIfit⟩ := FrameInvariance C₀ v hvclass (toLp 2 (x, τ)) r hpos p a
    have hvbclass : IsFitClass C₀ vb := by rw [hvbdef]; exact hFIclass
    have hvbval : ∀ u : F, vb (toLp 2 (u, (0 : ℝ)))
        = (v (toLp 2 (x + r • u, τ)) - v (toLp 2 (x, τ))) / r - inner ℝ p u := by
      intro u
      have hpt : (toLp 2 (x, τ) : WithLp 2 (F × ℝ))
          + toLp 2 (r • (u + (0 : ℝ) • p), r * (0 : ℝ)) = toLp 2 (x + r • u, τ) := by
        have h1 : (toLp 2 (x, τ) : WithLp 2 (F × ℝ))
            + toLp 2 (r • (u + (0 : ℝ) • p), r * (0 : ℝ))
            = toLp 2 (x + r • (u + (0 : ℝ) • p), τ + r * (0 : ℝ)) := rfl
        rw [h1, show x + r • (u + (0 : ℝ) • p) = x + r • u from by module,
          show τ + r * (0 : ℝ) = τ from by ring]
      rw [hvbdef]
      simp only [FrameChange]
      rw [hpt]
      ring
    have hvb0 : vb (0 : WithLp 2 (F × ℝ)) = 0 := by
      rw [← hzz, hvbval, show x + r • (0 : F) = x from by rw [smul_zero, add_zero]]
      simp
    have hvbfit : IsFit C₀ vb 0 1 0 0 := by
      have hbase : (toLp 2 (x, τ) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((ofLp (0 : WithLp 2 (F × ℝ))).1
              + (ofLp (0 : WithLp 2 (F × ℝ))).2 • p),
            r * (ofLp (0 : WithLp 2 (F × ℝ))).2) = toLp 2 (x, τ) := by
        rw [show (ofLp (0 : WithLp 2 (F × ℝ))).1 = (0 : F) from rfl,
          show (ofLp (0 : WithLp 2 (F × ℝ))).2 = (0 : ℝ) from rfl]
        have h1 : (toLp 2 (x, τ) : WithLp 2 (F × ℝ))
            + toLp 2 (r • ((0 : F) + (0 : ℝ) • p), r * (0 : ℝ))
            = toLp 2 (x + r • ((0 : F) + (0 : ℝ) • p), τ + r * (0 : ℝ)) := rfl
        rw [h1, show x + r • ((0 : F) + (0 : ℝ) • p) = x from by module,
          show τ + r * (0 : ℝ) = τ from by ring]
      have hin : IsFit C₀ v ((toLp 2 (x, τ) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((ofLp (0 : WithLp 2 (F × ℝ))).1
              + (ofLp (0 : WithLp 2 (F × ℝ))).2 • p),
            r * (ofLp (0 : WithLp 2 (F × ℝ))).2)) (r * 1) p a := by
        rw [hbase, mul_one]; exact hfit
      have hout := hFIfit (0 : WithLp 2 (F × ℝ)) 1 p a hin
      rw [sub_self, sub_self] at hout
      rw [hvbdef]
      exact hout
    -- the normalized positions: mean zero and second moment one
    obtain ⟨u, hudef⟩ : ∃ f : Fin n → F, f = fun i => r⁻¹ • (y i - x) := ⟨_, rfl⟩
    have huval : ∀ i, u i = r⁻¹ • (y i - x) := by intro i; rw [hudef]
    have hback : ∀ i, x + r • u i = y i := by
      intro i
      rw [huval, smul_smul, mul_inv_cancel₀ hrne, one_smul]
      abel
    have hmean0 : ∑ i, θ i • u i = (0 : F) := by
      have hs : ∀ i, θ i • u i = θ i • (-(r⁻¹ • x)) + r⁻¹ • (θ i • y i) := by
        intro i; rw [huval]; module
      rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_add_distrib,
        ← Finset.sum_smul, hθ1, one_smul, ← Finset.smul_sum, hθmean]
      abel
    have hsum2 : ∑ i, θ i * ‖y i - x‖ ^ 2 = r ^ 2 := by
      have hnn : (0 : ℝ) ≤ ∑ i, θ i * ‖y i - x‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hθpos i).le (sq_nonneg _)
      rw [hrdef, BaryRadius, Real.sq_sqrt hnn]
    have hsecond : ∑ i, θ i * ‖u i‖ ^ 2 = 1 := by
      have hs : ∀ i, θ i * ‖u i‖ ^ 2 = (r⁻¹) ^ 2 * (θ i * ‖y i - x‖ ^ 2) := by
        intro i; rw [huval, hnormsmul]; ring
      rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.mul_sum, hsum2]
      field_simp
    have hinnersum : (inner ℝ p (∑ i, θ i • u i) : ℝ) = ∑ i, θ i * inner ℝ p (u i) := by
      rw [inner_sum]
      exact Finset.sum_congr rfl fun i _ => real_inner_smul_right _ _ _
    have hinner0 : (∑ i, θ i * (inner ℝ p (u i) : ℝ)) = 0 := by
      rw [← hinnersum, hmean0, inner_zero_right]
    -- eq:jsf-transfer : the defect quotient is the framed average
    have htransfer : (∑ i, θ i * vb (toLp 2 (u i, (0 : ℝ))))
        = ((∑ i, θ i * v (toLp 2 (y i, τ))) - v (toLp 2 (x, τ))) / r := by
      have hs : ∀ i, θ i * vb (toLp 2 (u i, (0 : ℝ)))
          = r⁻¹ * (θ i * v (toLp 2 (y i, τ)))
            - θ i * (r⁻¹ * v (toLp 2 (x, τ))) - θ i * inner ℝ p (u i) := by
        intro i
        rw [hvbval, hback i]
        field_simp
      rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hθ1, one_mul, hinner0]
      field_simp
      ring
    -- summing the quadratic bound against a configuration of second moment one
    have hbd : (∑ i, θ i * vb (toLp 2 (u i, (0 : ℝ)))) ≤ 32 * Cg := by
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          θ i * vb (toLp 2 (u i, (0 : ℝ))) ≤ θ i * (16 * Cg * (1 + ‖u i‖ ^ 2)) := by
        intro i _
        refine mul_le_mul_of_nonneg_left ?_ (hθpos i).le
        have h := hquad vb hvbclass ⟨hvb0, hvbfit⟩ (u i)
        linarith [le_abs_self (vb (toLp 2 (u i, (0 : ℝ)))), h]
      have hsum := Finset.sum_le_sum hterm
      have hval : (∑ i, θ i * (16 * Cg * (1 + ‖u i‖ ^ 2))) = 32 * Cg := by
        have hs : ∀ i, θ i * (16 * Cg * (1 + ‖u i‖ ^ 2))
            = 16 * Cg * θ i + 16 * Cg * (θ i * ‖u i‖ ^ 2) := by intro i; ring
        rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_add_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, hθ1, hsecond]
        ring
      linarith [hsum, hval]
    rw [← htransfer]
    exact hbd
  -- ===== Step 5: the extremal constant =====
  have hDr : ((∑ i, θθ i * v (toLp 2 (yy i, τ₁))) - v (toLp 2 (xx, τ₁)))
      / BaryRadius nn θθ yy xx ∈ Q :=
    (hQmem _).mpr ⟨τ₁, nn, θθ, yy, xx, hcfg, hrad, rfl⟩
  have hQne : Q.Nonempty := ⟨_, hDr⟩
  have hQbddAbove : BddAbove Q := ⟨32 * Cg, fun q hq => hQbdd q hq⟩
  obtain ⟨κ, hκdef⟩ : ∃ k : ℝ, k = sSup Q := ⟨_, rfl⟩
  have hκpos : 0 < κ := by
    have h1 : (0 : ℝ) < ((∑ i, θθ i * v (toLp 2 (yy i, τ₁))) - v (toLp 2 (xx, τ₁)))
        / BaryRadius nn θθ yy xx := div_pos hDpos hrad
    have h2 := le_csSup hQbddAbove hDr
    rw [hκdef]
    linarith
  refine ⟨v, κ, hvclass, hvcent, hvna, hκpos, ?_, ?_⟩
  · intro τ _ n θ y x hcfg'
    have hrnn : (0 : ℝ) ≤ BaryRadius n θ y x := by
      rw [BaryRadius]; exact Real.sqrt_nonneg _
    rcases eq_or_lt_of_le hrnn with h0 | hpos
    · obtain ⟨hθpos, hθ1, -⟩ := hcfg'
      have hnn : (0 : ℝ) ≤ ∑ i, θ i * ‖y i - x‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hθpos i).le (sq_nonneg _)
      have hS : ∑ i, θ i * ‖y i - x‖ ^ 2 = 0 := by
        have hb : BaryRadius n θ y x = 0 := h0.symm
        rw [BaryRadius] at hb
        exact (Real.sqrt_eq_zero hnn).mp hb
      have hyi : ∀ i, y i = x := by
        intro i
        have hz : ∀ j ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ θ j * ‖y j - x‖ ^ 2 :=
          fun j _ => mul_nonneg (hθpos j).le (sq_nonneg _)
        have hi := (Finset.sum_eq_zero_iff_of_nonneg hz).mp hS i (Finset.mem_univ i)
        have hn : ‖y i - x‖ ^ 2 = 0 := by
          rcases mul_eq_zero.mp hi with h | h
          · exact absurd h (ne_of_gt (hθpos i))
          · exact h
        have hn0 : ‖y i - x‖ = 0 := by nlinarith [norm_nonneg (y i - x)]
        exact sub_eq_zero.mp (norm_eq_zero.mp hn0)
      have hsum : (∑ i, θ i * v (toLp 2 (y i, τ))) = v (toLp 2 (x, τ)) := by
        have hs : ∀ i, θ i * v (toLp 2 (y i, τ)) = θ i * v (toLp 2 (x, τ)) := by
          intro i; rw [hyi i]
        rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.sum_mul, hθ1, one_mul]
      rw [hsum, ← h0]
      simp
    · have hmem : ((∑ i, θ i * v (toLp 2 (y i, τ))) - v (toLp 2 (x, τ)))
          / BaryRadius n θ y x ∈ Q := (hQmem _).mpr ⟨τ, n, θ, y, x, hcfg', hpos, rfl⟩
      have hle := le_csSup hQbddAbove hmem
      rw [div_le_iff₀ hpos] at hle
      rw [hκdef]
      linarith
  · intro κ' hκ'
    rw [hκdef]
    refine csSup_le hQne ?_
    intro q hq
    obtain ⟨τ, n, θ, y, x, hcfg', hpos, rfl⟩ := (hQmem q).mp hq
    have h := hκ' τ (Set.mem_univ _) n θ y x hcfg'
    rw [div_le_iff₀ hpos]
    linarith
