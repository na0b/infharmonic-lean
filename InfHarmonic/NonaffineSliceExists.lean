import InfHarmonic.IsFitClass
import InfHarmonic.IsCenteredAt
import InfHarmonic.IsSpaceTimeAffine
import InfHarmonic.QuadEnvPathConvex
import InfHarmonic.CenteredGrowth
import InfHarmonic.UniformSubquadratic
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A nonaffine centered member of `A_{m,C₀}` has a horizontal slice with
nonzero midpoint Jensen defect. -/
theorem NonaffineSliceExists (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : IsFitClass C₀ v) (hcent : IsCenteredAt C₀ v 0)
    (hna : ¬ IsSpaceTimeAffine v) :
    ∃ (t : ℝ) (y₁ y₂ : F),
      v (toLp 2 ((2 : ℝ)⁻¹ • (y₁ + y₂), t))
        ≠ (v (toLp 2 (y₁, t)) + v (toLp 2 (y₂, t))) / 2 := by
  classical
  -- ===== the contrapositive: assume the midpoint identity on every slice =====
  by_contra hcon
  push Not at hcon
  refine hna ?_
  -- ===== Step 0: standing facts about `v` =====
  have hvc : Continuous v := continuousOn_univ.mp hv.1.1.2.1
  have hIuniv : ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvcont : ContinuousOn v
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc η hη
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ 0 (Or.inl rfl) J hJc η hη
    exact ⟨M, hM0, fun ξ hξ hξJ => hMb v hv hcent ξ hξ hξJ⟩
  have hvsub : IsLimitSubOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ)) v := by
    rw [hIuniv]; exact hv.1.1
  have hvsuper : IsLimitSuperOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ)) v := by
    rw [hIuniv]; exact hv.1.2
  have hnormsmul : ∀ (cs : ℝ) (u : F), ‖cs • u‖ ^ 2 = cs ^ 2 * ‖u‖ ^ 2 := by
    intro cs u; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hP0 : ∀ z : WithLp 2 (F × ℝ), QuadEnvP v 0 z = v z := by intro z; simp [QuadEnvP]
  have hM0 : ∀ z : WithLp 2 (F × ℝ), QuadEnvM v 0 z = v z := by intro z; simp [QuadEnvM]
  -- the convexity in the length, at `d = 0`, and its backward twin
  have hconvP : ∀ (x : F) (t T : ℝ), 0 < T →
      ConvexOn ℝ (Set.Icc (0 : ℝ) T) (fun l : ℝ => QuadEnvP v l (toLp 2 (x, t))) := by
    intro x t T hT
    obtain ⟨h1, -⟩ :=
      QuadEnvPathConvex (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow T hT
    have h2 := h1 hvsub x (0 : F) t (fun l _ => Set.mem_univ _)
    have hfun : (fun l : ℝ => QuadEnvP v l (toLp 2 (x + l • (0 : F), t))
          + ‖(0 : F)‖ ^ 2 * (l * Real.log l))
        = (fun l : ℝ => QuadEnvP v l (toLp 2 (x, t))) := by
      funext l
      rw [smul_zero, add_zero, norm_zero]
      ring
    rw [hfun] at h2
    exact h2
  have hconcM : ∀ (x : F) (t T : ℝ), 0 < T →
      ConcaveOn ℝ (Set.Icc (0 : ℝ) T) (fun l : ℝ => QuadEnvM v l (toLp 2 (x, t))) := by
    intro x t T hT
    obtain ⟨-, h1⟩ :=
      QuadEnvPathConvex (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow T hT
    exact h1 hvsuper x t (fun l _ => Set.mem_univ _)
  -- a linear functional bounded above on all of `F` is zero
  have hvanish : ∀ (Δ : F) (R : ℝ), (∀ x : F, (inner ℝ Δ x : ℝ) ≤ R) → Δ = 0 := by
    intro Δ R hR
    by_contra hne
    have hpos : (0 : ℝ) < ‖Δ‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
    have h1 := hR (((|R| + 1) / ‖Δ‖ ^ 2) • Δ)
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq,
      div_mul_cancel₀ _ (ne_of_gt hpos)] at h1
    have h2 := le_abs_self R
    linarith
  -- ===== Step 1: each horizontal slice is affine =====
  have hslice : ∀ t : ℝ, ∃ q : F, ∀ y : F,
      v (toLp 2 (y, t)) = inner ℝ q y + v (toLp 2 ((0 : F), t)) := by
    intro t
    have hhalf : ∀ y : F, v (toLp 2 ((2 : ℝ)⁻¹ • y, t))
        = (v (toLp 2 (y, t)) + v (toLp 2 ((0 : F), t))) / 2 := by
      intro y
      have h := hcon t y 0
      rwa [add_zero] at h
    have hadd : ∀ y₁ y₂ : F,
        v (toLp 2 (y₁ + y₂, t)) - v (toLp 2 ((0 : F), t))
          = (v (toLp 2 (y₁, t)) - v (toLp 2 ((0 : F), t)))
            + (v (toLp 2 (y₂, t)) - v (toLp 2 ((0 : F), t))) := by
      intro y₁ y₂
      have h1 := hcon t y₁ y₂
      rw [hhalf (y₁ + y₂)] at h1
      linarith
    have hctsslice : Continuous
        (fun y : F => v (toLp 2 (y, t)) - v (toLp 2 ((0 : F), t))) := by
      have hm : Continuous fun y : F => (toLp 2 (y, t) : WithLp 2 (F × ℝ)) := by fun_prop
      exact (hvc.comp hm).sub continuous_const
    obtain ⟨L, hL⟩ : ∃ L : F →L[ℝ] ℝ, ∀ y : F,
        L y = v (toLp 2 (y, t)) - v (toLp 2 ((0 : F), t)) := by
      refine ⟨AddMonoidHom.toRealLinearMap
        (AddMonoidHom.mk' (fun y : F => v (toLp 2 (y, t)) - v (toLp 2 ((0 : F), t))) hadd)
        hctsslice, ?_⟩
      intro y; rfl
    refine ⟨(InnerProductSpace.toDual ℝ F).symm L, ?_⟩
    intro y
    have hr : (inner ℝ ((InnerProductSpace.toDual ℝ F).symm L) y : ℝ) = L y := by
      have h0 : (InnerProductSpace.toDual ℝ F) ((InnerProductSpace.toDual ℝ F).symm L) = L :=
        LinearIsometryEquiv.apply_symm_apply _ _
      calc (inner ℝ ((InnerProductSpace.toDual ℝ F).symm L) y : ℝ)
          = (InnerProductSpace.toDual ℝ F) ((InnerProductSpace.toDual ℝ F).symm L) y := rfl
        _ = L y := by rw [h0]
    rw [hr, hL y]
    ring
  choose p hp using hslice
  obtain ⟨c, hcdef⟩ : ∃ f : ℝ → ℝ, f = fun t => v (toLp 2 ((0 : F), t)) := ⟨_, rfl⟩
  have hcval : ∀ t : ℝ, c t = v (toLp 2 ((0 : F), t)) := by intro t; rw [hcdef]
  -- ===== Step 3: the forward envelope of an affine slice =====
  have hPform : ∀ l : ℝ, 0 ≤ l → ∀ (x : F) (t : ℝ),
      QuadEnvP v l (toLp 2 (x, t))
        = inner ℝ (p (t + l)) x + c (t + l) + (l / 2) * ‖p (t + l)‖ ^ 2 := by
    intro l hl x t
    rcases eq_or_lt_of_le hl with h0 | hlpos
    · rw [← h0, hP0, add_zero, hcval, hp t x]
      ring
    · have hlne : l ≠ 0 := ne_of_gt hlpos
      have hid : ∀ y : F, v (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l)
          = (inner ℝ (p (t + l)) x + c (t + l) + (l / 2) * ‖p (t + l)‖ ^ 2)
            - ‖y - (x + l • p (t + l))‖ ^ 2 / (2 * l) := by
        intro y
        have hn1 : ‖y - x‖ ^ 2
            = ‖y - (x + l • p (t + l))‖ ^ 2
              + 2 * (l * (inner ℝ (p (t + l)) (y - (x + l • p (t + l))) : ℝ))
              + l ^ 2 * ‖p (t + l)‖ ^ 2 := by
          rw [show y - x = (y - (x + l • p (t + l))) + l • p (t + l) from by abel,
            norm_add_sq_real, real_inner_smul_right, real_inner_comm, hnormsmul]
        have hn2 : (inner ℝ (p (t + l)) y : ℝ)
            = inner ℝ (p (t + l)) x + l * ‖p (t + l)‖ ^ 2
              + inner ℝ (p (t + l)) (y - (x + l • p (t + l))) := by
          rw [inner_sub_right, inner_add_right, real_inner_smul_right,
            real_inner_self_eq_norm_sq]
          ring
        rw [hp (t + l) y, ← hcval, hn1, hn2]
        field_simp
        ring
      have hub : ∀ y : F, v (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l)
          ≤ inner ℝ (p (t + l)) x + c (t + l) + (l / 2) * ‖p (t + l)‖ ^ 2 := by
        intro y
        rw [hid y]
        have h2 : (0 : ℝ) ≤ ‖y - (x + l • p (t + l))‖ ^ 2 / (2 * l) :=
          div_nonneg (sq_nonneg _) (by linarith)
        linarith
      have hat : v (toLp 2 (x + l • p (t + l), t + l))
            - ‖(x + l • p (t + l)) - x‖ ^ 2 / (2 * l)
          = inner ℝ (p (t + l)) x + c (t + l) + (l / 2) * ‖p (t + l)‖ ^ 2 := by
        rw [hid (x + l • p (t + l)),
          show (x + l • p (t + l)) - (x + l • p (t + l)) = (0 : F) from by abel, norm_zero]
        norm_num
      rw [QuadEnvP, if_neg hlne]
      show sSup {w : ℝ | ∃ y : F, w = v (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l)}
        = inner ℝ (p (t + l)) x + c (t + l) + (l / 2) * ‖p (t + l)‖ ^ 2
      refine le_antisymm (csSup_le ⟨_, ⟨x, rfl⟩⟩ ?_) ?_
      · rintro w ⟨y, rfl⟩; exact hub y
      · rw [← hat]
        exact le_csSup ⟨_, by rintro w ⟨y, rfl⟩; exact hub y⟩ ⟨x + l • p (t + l), rfl⟩
  -- ===== Step 6 (first half of the data): the backward envelope =====
  have hMform : ∀ l : ℝ, 0 ≤ l → ∀ (x : F) (t : ℝ),
      QuadEnvM v l (toLp 2 (x, t))
        = inner ℝ (p (t - l)) x + c (t - l) - (l / 2) * ‖p (t - l)‖ ^ 2 := by
    intro l hl x t
    rcases eq_or_lt_of_le hl with h0 | hlpos
    · rw [← h0, hM0, sub_zero, hcval, hp t x]
      ring
    · have hlne : l ≠ 0 := ne_of_gt hlpos
      have hid : ∀ y : F, v (toLp 2 (y, t - l)) + ‖y - x‖ ^ 2 / (2 * l)
          = (inner ℝ (p (t - l)) x + c (t - l) - (l / 2) * ‖p (t - l)‖ ^ 2)
            + ‖y - (x - l • p (t - l))‖ ^ 2 / (2 * l) := by
        intro y
        have hn1 : ‖y - x‖ ^ 2
            = ‖y - (x - l • p (t - l))‖ ^ 2
              - 2 * (l * (inner ℝ (p (t - l)) (y - (x - l • p (t - l))) : ℝ))
              + l ^ 2 * ‖p (t - l)‖ ^ 2 := by
          rw [show y - x = (y - (x - l • p (t - l))) - l • p (t - l) from by abel,
            norm_sub_sq_real, real_inner_smul_right, real_inner_comm, hnormsmul]
        have hn2 : (inner ℝ (p (t - l)) y : ℝ)
            = inner ℝ (p (t - l)) x - l * ‖p (t - l)‖ ^ 2
              + inner ℝ (p (t - l)) (y - (x - l • p (t - l))) := by
          rw [inner_sub_right, inner_sub_right, real_inner_smul_right,
            real_inner_self_eq_norm_sq]
          ring
        rw [hp (t - l) y, ← hcval, hn1, hn2]
        field_simp
        ring
      have hlb : ∀ y : F,
          inner ℝ (p (t - l)) x + c (t - l) - (l / 2) * ‖p (t - l)‖ ^ 2
            ≤ v (toLp 2 (y, t - l)) + ‖y - x‖ ^ 2 / (2 * l) := by
        intro y
        rw [hid y]
        have h2 : (0 : ℝ) ≤ ‖y - (x - l • p (t - l))‖ ^ 2 / (2 * l) :=
          div_nonneg (sq_nonneg _) (by linarith)
        linarith
      have hat : v (toLp 2 (x - l • p (t - l), t - l))
            + ‖(x - l • p (t - l)) - x‖ ^ 2 / (2 * l)
          = inner ℝ (p (t - l)) x + c (t - l) - (l / 2) * ‖p (t - l)‖ ^ 2 := by
        rw [hid (x - l • p (t - l)),
          show (x - l • p (t - l)) - (x - l • p (t - l)) = (0 : F) from by abel, norm_zero]
        norm_num
      rw [QuadEnvM, if_neg hlne]
      show sInf {w : ℝ | ∃ y : F, w = v (toLp 2 (y, t - l)) + ‖y - x‖ ^ 2 / (2 * l)}
        = inner ℝ (p (t - l)) x + c (t - l) - (l / 2) * ‖p (t - l)‖ ^ 2
      refine le_antisymm ?_ (le_csInf ⟨_, ⟨x, rfl⟩⟩ ?_)
      · rw [← hat]
        exact csInf_le ⟨_, by rintro w ⟨y, rfl⟩; exact hlb y⟩ ⟨x - l • p (t - l), rfl⟩
      · rintro w ⟨y, rfl⟩; exact hlb y
  -- ===== Step 4: `p` satisfies the affine interpolation identity on `[0, T]` =====
  have hpinterp : ∀ (t T : ℝ), 0 < T → ∀ l₀ ∈ Set.Icc (0 : ℝ) T, ∀ l₁ ∈ Set.Icc (0 : ℝ) T,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      p (t + (a * l₀ + b * l₁)) = a • p (t + l₀) + b • p (t + l₁) := by
    intro t T hT l₀ h0 l₁ h1 a b ha hb hab
    have hlθ : (0 : ℝ) ≤ a * l₀ + b * l₁ :=
      add_nonneg (mul_nonneg ha h0.1) (mul_nonneg hb h1.1)
    have key : ∀ x : F,
        (inner ℝ (p (t + (a * l₀ + b * l₁)) - a • p (t + l₀) - b • p (t + l₁)) x : ℝ)
          ≤ (a * (c (t + l₀) + (l₀ / 2) * ‖p (t + l₀)‖ ^ 2)
              + b * (c (t + l₁) + (l₁ / 2) * ‖p (t + l₁)‖ ^ 2))
            - (c (t + (a * l₀ + b * l₁))
              + ((a * l₀ + b * l₁) / 2) * ‖p (t + (a * l₀ + b * l₁))‖ ^ 2) := by
      intro x
      have hcv := (hconvP x t T hT).2 h0 h1 ha hb hab
      simp only [smul_eq_mul] at hcv
      rw [hPform _ hlθ x t, hPform _ h0.1 x t, hPform _ h1.1 x t] at hcv
      rw [inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left]
      linarith [hcv]
    have hΔ := hvanish _ _ key
    have hΔ' : p (t + (a * l₀ + b * l₁)) - (a • p (t + l₀) + b • p (t + l₁)) = 0 := by
      rw [← hΔ]; abel
    exact sub_eq_zero.mp hΔ'
  have hpstep : ∀ (t l : ℝ), 0 ≤ l → p (t + l) = p t + l • (p (t + 1) - p t) := by
    intro t l hl
    rcases le_total l 1 with h1 | h1
    · have h2 := hpinterp t 1 one_pos 0 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
        1 (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) (1 - l) l (by linarith) hl (by ring)
      rw [show (1 - l) * 0 + l * 1 = l from by ring, add_zero] at h2
      rw [h2]; module
    · have hlne : l ≠ 0 := by intro h; rw [h] at h1; linarith
      have h2 := hpinterp t l (by linarith) 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩)
        l (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) (1 - 1 / l) (1 / l)
        (by rw [sub_nonneg, div_le_one (by linarith)]; linarith)
        (by positivity) (by ring)
      rw [show (1 - 1 / l) * 0 + 1 / l * l = (1 : ℝ) from by
          rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ hlne], add_zero] at h2
      have h5 : (1 / l) • p (t + l) = p (t + 1) - (1 - 1 / l) • p t := by rw [h2]; abel
      have h6 : (l : ℝ) • ((1 / l) • p (t + l)) = p (t + l) := by
        rw [smul_smul, mul_one_div, div_self hlne, one_smul]
      have h4 : p (t + l) = l • p (t + 1) - (l - 1) • p t := by
        rw [← h6, h5, smul_sub, smul_smul,
          show (l : ℝ) * (1 - 1 / l) = l - 1 from by field_simp]
      rw [h4]; module
  -- the base-point lemma, in `F` and in `ℝ`
  have hbaseF : ∀ q : ℝ → F,
      (∀ (t l : ℝ), 0 ≤ l → q (t + l) = q t + l • (q (t + 1) - q t)) →
      ∀ τ : ℝ, q τ = q 0 + τ • (q 1 - q 0) := by
    intro q hq τ
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min τ 0 - 1 := ⟨_, rfl⟩
    have hsτ : s ≤ τ - 1 := by rw [hs]; have := min_le_left τ (0 : ℝ); linarith
    have hs0 : s ≤ -1 := by rw [hs]; have := min_le_right τ (0 : ℝ); linarith
    have h1 := hq s (τ - s) (by linarith)
    have h2 := hq s (0 - s) (by linarith)
    have h3 := hq s (1 - s) (by linarith)
    rw [show s + (τ - s) = τ from by ring] at h1
    rw [show s + (0 - s) = (0 : ℝ) from by ring] at h2
    rw [show s + (1 - s) = (1 : ℝ) from by ring] at h3
    rw [h1, h2, h3]
    module
  have hbaseR : ∀ q : ℝ → ℝ,
      (∀ (t l : ℝ), 0 ≤ l → q (t + l) = q t + l * (q (t + 1) - q t)) →
      ∀ τ : ℝ, q τ = q 0 + τ * (q 1 - q 0) := by
    intro q hq τ
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = min τ 0 - 1 := ⟨_, rfl⟩
    have hsτ : s ≤ τ - 1 := by rw [hs]; have := min_le_left τ (0 : ℝ); linarith
    have hs0 : s ≤ -1 := by rw [hs]; have := min_le_right τ (0 : ℝ); linarith
    have h1 := hq s (τ - s) (by linarith)
    have h2 := hq s (0 - s) (by linarith)
    have h3 := hq s (1 - s) (by linarith)
    rw [show s + (τ - s) = τ from by ring] at h1
    rw [show s + (0 - s) = (0 : ℝ) from by ring] at h2
    rw [show s + (1 - s) = (1 : ℝ) from by ring] at h3
    rw [h1, h2, h3]
    ring
  have hpaff : ∀ τ : ℝ, p τ = p 0 + τ • (p 1 - p 0) := hbaseF p hpstep
  -- ===== Step 5: `p` is constant =====
  obtain ⟨Cg, hCg0, hCgb⟩ := CenteredGrowth (F := F) C₀ hC₀
  have hpbound : ∀ (K : ℝ), 2 ≤ K → ∀ τ : ℝ, |τ| ≤ K → ‖p τ‖ ≤ Cg * (1 + Real.log K) ^ 2 := by
    intro K hK τ hτ
    have hK0 : (0 : ℝ) < K := by linarith
    have hLnn : (0 : ℝ) ≤ (1 + Real.log K) ^ 2 := sq_nonneg _
    rcases eq_or_ne (p τ) 0 with h0 | h0
    · rw [h0, norm_zero]; positivity
    · have hn0 : (0 : ℝ) < ‖p τ‖ := norm_pos_iff.mpr h0
      obtain ⟨x, hxd⟩ : ∃ u : F, u = (K / ‖p τ‖) • p τ := ⟨_, rfl⟩
      have hxn : ‖x‖ = K := by
        rw [hxd, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ K / ‖p τ‖)]
        field_simp
      have hxin : (inner ℝ (p τ) x : ℝ) = K * ‖p τ‖ := by
        rw [hxd, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hb1 := hCgb v hv (Or.inl hcent) K hK (toLp 2 (x, τ))
        (by rw [show (ofLp (toLp 2 (x, τ) : WithLp 2 (F × ℝ))).1 = x from rfl, hxn])
        (by rw [show (ofLp (toLp 2 (x, τ) : WithLp 2 (F × ℝ))).2 = τ from rfl]; exact hτ)
      have hb2 := hCgb v hv (Or.inl hcent) K hK (toLp 2 (-x, τ))
        (by rw [show (ofLp (toLp 2 (-x, τ) : WithLp 2 (F × ℝ))).1 = -x from rfl, norm_neg, hxn])
        (by rw [show (ofLp (toLp 2 (-x, τ) : WithLp 2 (F × ℝ))).2 = τ from rfl]; exact hτ)
      have hv1 : v (toLp 2 (x, τ)) = inner ℝ (p τ) x + c τ := by rw [hp τ x, hcval]
      have hv2 : v (toLp 2 (-x, τ)) = -(inner ℝ (p τ) x : ℝ) + c τ := by
        rw [hp τ (-x), hcval, inner_neg_right]
      rw [hv1, hxin] at hb1
      rw [hv2, hxin] at hb2
      have hb1' := abs_le.mp hb1
      have hb2' := abs_le.mp hb2
      -- `2 K ‖p τ‖ ≤ 2 Cg K (1 + log K)^2`, divide by `2K > 0`
      have hcomb : 2 * (K * ‖p τ‖) ≤ 2 * (Cg * K * (1 + Real.log K) ^ 2) := by
        have := hb1'.2
        have := hb2'.1
        linarith
      have hfin : K * ‖p τ‖ ≤ K * (Cg * (1 + Real.log K) ^ 2) := by nlinarith [hcomb]
      exact le_of_mul_le_mul_left hfin hK0
  have hpconst : ∀ τ : ℝ, p τ = p 0 := by
    have hd : p 1 - p 0 = 0 := by
      by_contra hne
      have hdn : (0 : ℝ) < ‖p 1 - p 0‖ := norm_pos_iff.mpr hne
      obtain ⟨S, hS2, hSd⟩ : ∃ S : ℝ, 2 ≤ S
          ∧ (25 * Cg + ‖p 0‖ + 1) / ‖p 1 - p 0‖ ≤ S :=
        ⟨max 2 ((25 * Cg + ‖p 0‖ + 1) / ‖p 1 - p 0‖), le_max_left _ _, le_max_right _ _⟩
      have hS0 : (0 : ℝ) < S := by linarith
      have hS2' : (4 : ℝ) ≤ S ^ 2 := by nlinarith
      have hK : (2 : ℝ) ≤ S ^ 4 := by nlinarith
      have hlogS : Real.log S ≤ S - 1 := Real.log_le_sub_one_of_pos hS0
      have hlogSnn : (0 : ℝ) ≤ Real.log S := Real.log_nonneg (by linarith)
      have hlog4 : Real.log (S ^ 4) = 4 * Real.log S := by
        rw [Real.log_pow]; push_cast; ring
      have hgb := hpbound (S ^ 4) hK (S ^ 4) (by rw [abs_of_nonneg (by positivity)])
      rw [hlog4] at hgb
      -- `‖p (S^4)‖ ≥ S^4 ‖p 1 - p 0‖ - ‖p 0‖`
      have hsplit := hpaff (S ^ 4)
      have hnsm : ‖(S ^ 4 : ℝ) • (p 1 - p 0)‖ = S ^ 4 * ‖p 1 - p 0‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ S ^ 4)]
      have hlow : ‖(S ^ 4 : ℝ) • (p 1 - p 0)‖ ≤ ‖p (S ^ 4)‖ + ‖p 0‖ := by
        have h0 := norm_sub_le (p (S ^ 4)) (p 0)
        rw [hsplit, show p 0 + (S ^ 4 : ℝ) • (p 1 - p 0) - p 0
          = (S ^ 4 : ℝ) • (p 1 - p 0) from by abel] at h0
        rw [hsplit]
        linarith [h0]
      rw [hnsm] at hlow
      -- the explicit log bootstrap: `(1 + 4 log S)^2 ≤ 16 S^2`
      have e3 : (1 + 4 * Real.log S) ^ 2 ≤ 16 * S ^ 2 := by nlinarith
      have e4 : ‖p (S ^ 4)‖ ≤ 16 * Cg * S ^ 2 := by nlinarith
      have e5 : 25 * Cg + ‖p 0‖ + 1 ≤ S * ‖p 1 - p 0‖ := by
        rw [div_le_iff₀ hdn] at hSd; linarith
      have e6 : S ^ 4 * ‖p 1 - p 0‖ - ‖p 0‖ ≤ 16 * Cg * S ^ 2 := by linarith
      have e7 : S ^ 2 * (25 * Cg + ‖p 0‖ + 1) ≤ S ^ 2 * (S * ‖p 1 - p 0‖) :=
        mul_le_mul_of_nonneg_left e5 (sq_nonneg S)
      have e8 : S ^ 3 * ‖p 1 - p 0‖ ≤ S ^ 4 * ‖p 1 - p 0‖ := by
        have h3 : (0 : ℝ) ≤ S ^ 3 * ‖p 1 - p 0‖ :=
          mul_nonneg (pow_nonneg hS0.le 3) hdn.le
        nlinarith [mul_nonneg h3 (by linarith : (0 : ℝ) ≤ S - 1)]
      have e9 : S ^ 2 * (S * ‖p 1 - p 0‖) = S ^ 3 * ‖p 1 - p 0‖ := by ring
      rw [e9] at e7
      nlinarith [norm_nonneg (p 0), hCg0, hS2']
    intro τ
    rw [hpaff τ, hd, smul_zero, add_zero]
  -- ===== Step 6: `c` is convex and concave, hence affine =====
  have hcconv : ∀ (t T : ℝ), 0 < T → ∀ l₀ ∈ Set.Icc (0 : ℝ) T, ∀ l₁ ∈ Set.Icc (0 : ℝ) T,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      c (t + (a * l₀ + b * l₁)) ≤ a * c (t + l₀) + b * c (t + l₁) := by
    intro t T hT l₀ h0 l₁ h1 a b ha hb hab
    have hlθ : (0 : ℝ) ≤ a * l₀ + b * l₁ :=
      add_nonneg (mul_nonneg ha h0.1) (mul_nonneg hb h1.1)
    have hcv := (hconvP (0 : F) t T hT).2 h0 h1 ha hb hab
    simp only [smul_eq_mul] at hcv
    rw [hPform _ hlθ 0 t, hPform _ h0.1 0 t, hPform _ h1.1 0 t,
      hpconst (t + (a * l₀ + b * l₁)), hpconst (t + l₀), hpconst (t + l₁)] at hcv
    simp only [inner_zero_right] at hcv
    nlinarith [hcv, hab]
  have hcconc : ∀ (t T : ℝ), 0 < T → ∀ l₀ ∈ Set.Icc (0 : ℝ) T, ∀ l₁ ∈ Set.Icc (0 : ℝ) T,
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      a * c (t - l₀) + b * c (t - l₁) ≤ c (t - (a * l₀ + b * l₁)) := by
    intro t T hT l₀ h0 l₁ h1 a b ha hb hab
    have hlθ : (0 : ℝ) ≤ a * l₀ + b * l₁ :=
      add_nonneg (mul_nonneg ha h0.1) (mul_nonneg hb h1.1)
    have hcv := (hconcM (0 : F) t T hT).2 h0 h1 ha hb hab
    simp only [smul_eq_mul] at hcv
    rw [hMform _ hlθ 0 t, hMform _ h0.1 0 t, hMform _ h1.1 0 t,
      hpconst (t - (a * l₀ + b * l₁)), hpconst (t - l₀), hpconst (t - l₁)] at hcv
    simp only [inner_zero_right] at hcv
    nlinarith [hcv, hab]
  have hcstep : ∀ (t l : ℝ), 0 ≤ l → c (t + l) = c t + l * (c (t + 1) - c t) := by
    intro t l hl
    rcases le_total l 1 with h1 | h1
    · have hA := hcconv t 1 one_pos 0 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
        1 (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) (1 - l) l (by linarith) hl (by ring)
      have hB := hcconc (t + 1) 1 one_pos 1 (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩)
        0 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩) (1 - l) l (by linarith) hl (by ring)
      rw [show (1 - l) * 0 + l * 1 = l from by ring, add_zero] at hA
      rw [show (1 - l) * 1 + l * 0 = 1 - l from by ring,
        show t + 1 - (1 - l) = t + l from by ring, show t + 1 - 1 = t from by ring,
        show t + 1 - 0 = t + 1 from by ring] at hB
      linarith
    · have hlne : l ≠ 0 := by intro h; rw [h] at h1; linarith
      have hA := hcconv t l (by linarith) 0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩)
        l (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) (1 - 1 / l) (1 / l)
        (by rw [sub_nonneg, div_le_one (by linarith)]; linarith)
        (by positivity) (by ring)
      have hB := hcconc (t + l) l (by linarith) l (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩)
        0 (Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩) (1 - 1 / l) (1 / l)
        (by rw [sub_nonneg, div_le_one (by linarith)]; linarith)
        (by positivity) (by ring)
      rw [show (1 - 1 / l) * 0 + 1 / l * l = (1 : ℝ) from by
          rw [mul_zero, zero_add, one_div, inv_mul_cancel₀ hlne], add_zero] at hA
      rw [show (1 - 1 / l) * l + 1 / l * 0 = l - 1 from by field_simp; ring,
        show t + l - (l - 1) = t + 1 from by ring, show t + l - l = t from by ring,
        show t + l - 0 = t + l from by ring] at hB
      have heq : c (t + 1) = (1 - 1 / l) * c t + 1 / l * c (t + l) := le_antisymm hA hB
      have hmul : l * c (t + 1) = l * ((1 - 1 / l) * c t + 1 / l * c (t + l)) := by rw [heq]
      rw [show l * ((1 - 1 / l) * c t + 1 / l * c (t + l))
          = (l - 1) * c t + c (t + l) from by field_simp] at hmul
      linarith
  have hcaff : ∀ τ : ℝ, c τ = c 0 + τ * (c 1 - c 0) := hbaseR c hcstep
  -- ===== Conclusion: `v` is affine on space-time =====
  refine ⟨p 0, c 1 - c 0, c 0, ?_⟩
  intro z
  have hzz : (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := rfl
  have h1 := hp ((ofLp z).2) ((ofLp z).1)
  rw [hzz, ← hcval] at h1
  rw [h1, hpconst ((ofLp z).2), hcaff ((ofLp z).2)]
  ring
