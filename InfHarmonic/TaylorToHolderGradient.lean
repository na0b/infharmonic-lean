import InfHarmonic.Preamble
open Metric Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A uniform `|h|^{1+α}` Taylor estimate with a bounded slope field gives
pointwise differentiability and an `α`-Hölder gradient. The Hölder constant is
produced before the data `S`, `U`, `g`, so it depends only on `C`, `α`
and `ρ₀`. -/
theorem TaylorToHolderGradient (α C ρ₀ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hC : 0 < C) (hρ₀ : 0 < ρ₀) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (S : Set E) (U : E → ℝ) (g : E → E),
      (∀ z ∈ S, ∀ h : E, ‖h‖ ≤ ρ₀ →
        |U (z + h) - U z - inner ℝ (g z) h| ≤ C * ‖h‖ ^ (1 + α)) →
      (∀ z ∈ S, ‖g z‖ ≤ C) →
      (∀ z ∈ S, HasGradientAt U (g z) z) ∧
      ∀ z ∈ S, ∀ z' ∈ S, ‖g z - g z'‖ ≤ C' * ‖z - z'‖ ^ α := by
  -- `α ≤ 1` is carried by the statement because the paper's Hölder exponent `α_d` lies in
  -- `(0,1]`; the argument below needs only `α > 0`, so it is recorded here rather than used.
  have _unused_hα1 := hα1
  -- The constant is produced before the data `S`, `U`, `g`, as the statement requires.
  have h2a : (0:ℝ) < (2:ℝ) ^ (1 + α) := Real.rpow_pos_of_pos (by norm_num) _
  have h1le2a : (1:ℝ) ≤ (2:ℝ) ^ (1 + α) :=
    Real.one_le_rpow (by norm_num) (by linarith)
  have hρa : (0:ℝ) < (2 / ρ₀) ^ α := Real.rpow_pos_of_pos (by positivity) _
  refine ⟨max (3 * C * (2:ℝ) ^ (1 + α)) (2 * C * (2 / ρ₀) ^ α), ?_, ?_⟩
  · exact lt_of_lt_of_le (by positivity) (le_max_left _ _)
  intro S U g htaylor hgb
  refine ⟨?_, ?_⟩
  · -- Differentiability: the Taylor bound is `o(‖h‖)` because `α > 0`.
    intro z hz
    refine hasGradientAt_iff_hasFDerivAt.mpr ?_
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro c hc
    rw [Metric.eventually_nhds_iff]
    refine ⟨min ρ₀ ((c / C) ^ α⁻¹),
      lt_min hρ₀ (Real.rpow_pos_of_pos (by positivity) _), fun h hh => ?_⟩
    rw [dist_zero_right] at hh
    have hhρ : ‖h‖ ≤ ρ₀ := le_of_lt (lt_of_lt_of_le hh (min_le_left _ _))
    have hT := htaylor z hz h hhρ
    have hkey : C * ‖h‖ ^ (1 + α) ≤ c * ‖h‖ := by
      rcases eq_or_lt_of_le (norm_nonneg h) with h0 | h0
      · rw [← h0, Real.zero_rpow (by linarith)]
        simp
      · have hsplit : ‖h‖ ^ (1 + α) = ‖h‖ * ‖h‖ ^ α := by
          rw [Real.rpow_add h0, Real.rpow_one]
        have hle : ‖h‖ ^ α ≤ c / C :=
          le_trans (Real.rpow_le_rpow (norm_nonneg h)
              (le_of_lt (lt_of_lt_of_le hh (min_le_right _ _))) hα.le)
            (le_of_eq (Real.rpow_inv_rpow (by positivity) hα.ne'))
        rw [le_div_iff₀ hC] at hle
        rw [hsplit]
        nlinarith [h0, hle]
    have happ : (InnerProductSpace.toDual ℝ E (g z)) h = (inner ℝ (g z) h : ℝ) := by
      simp [InnerProductSpace.toDual_apply_apply]
    rw [happ, Real.norm_eq_abs]
    exact le_trans hT hkey
  · -- The Hölder estimate, in three regimes.
    intro z hz z' hz'
    rcases eq_or_lt_of_le (norm_nonneg (z - z')) with hl0 | hl0
    · -- `ℓ = 0`
      have hzz : z = z' := sub_eq_zero.mp (norm_eq_zero.mp hl0.symm)
      rw [hzz]
      simp [Real.zero_rpow hα.ne']
    rcases le_or_gt ‖z - z'‖ (ρ₀ / 2) with hnear | hfar
    · -- `0 < ℓ ≤ ρ₀/2`: the two-way Taylor comparison, direction by direction
      have hsplitT : ‖z - z'‖ ^ (1 + α) = ‖z - z'‖ * ‖z - z'‖ ^ α := by
        rw [Real.rpow_add hl0, Real.rpow_one]
      have hTnn : (0:ℝ) ≤ ‖z - z'‖ ^ (1 + α) := Real.rpow_nonneg (norm_nonneg _) _
      have hdir : ∀ e : E, ‖e‖ = 1 →
          |(inner ℝ (g z - g z') e : ℝ)| ≤ 3 * C * (2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ α := by
        intro e he
        have hsn : ‖(‖z - z'‖ • e : E)‖ = ‖z - z'‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), he, mul_one]
        have hnz : ‖z' - z‖ = ‖z - z'‖ := norm_sub_rev _ _
        -- the Taylor estimate at `z'` with increment `ℓ e`
        have h1 := htaylor z' hz' (‖z - z'‖ • e) (by rw [hsn]; linarith)
        rw [real_inner_smul_right, hsn] at h1
        -- the Taylor estimate at `z` with increment `z' - z`
        have h2 := htaylor z hz (z' - z) (by rw [hnz]; linarith)
        rw [show z + (z' - z) = z' from by abel, hnz] at h2
        -- the Taylor estimate at `z` with increment `z' + ℓ e - z`, of norm at most `2ℓ`
        have hn3 : ‖z' + ‖z - z'‖ • e - z‖ ≤ 2 * ‖z - z'‖ := by
          calc ‖z' + ‖z - z'‖ • e - z‖ = ‖(z' - z) + ‖z - z'‖ • e‖ := by
                rw [show z' + ‖z - z'‖ • e - z = (z' - z) + ‖z - z'‖ • e from by abel]
            _ ≤ ‖z' - z‖ + ‖(‖z - z'‖ • e : E)‖ := norm_add_le _ _
            _ = 2 * ‖z - z'‖ := by rw [hnz, hsn]; ring
        have h3 := htaylor z hz (z' + ‖z - z'‖ • e - z) (by linarith)
        rw [show z + (z' + ‖z - z'‖ • e - z) = z' + ‖z - z'‖ • e from by abel] at h3
        have hinn : (inner ℝ (g z) (z' + ‖z - z'‖ • e - z) : ℝ)
            = (inner ℝ (g z) (z' - z) : ℝ) + ‖z - z'‖ * (inner ℝ (g z) e : ℝ) := by
          rw [show z' + ‖z - z'‖ • e - z = (z' - z) + ‖z - z'‖ • e from by abel,
            inner_add_right, real_inner_smul_right]
        rw [hinn] at h3
        have hrhs : C * ‖z' + ‖z - z'‖ • e - z‖ ^ (1 + α)
            ≤ C * ((2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ (1 + α)) := by
          rw [← Real.mul_rpow (by norm_num) (norm_nonneg _)]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (norm_nonneg _) hn3 (by linarith)) hC.le
        have h3' : |U (z' + ‖z - z'‖ • e) - U z
              - ((inner ℝ (g z) (z' - z) : ℝ) + ‖z - z'‖ * (inner ℝ (g z) e : ℝ))|
            ≤ C * ((2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ (1 + α)) := le_trans h3 hrhs
        -- combine, then divide by `ℓ > 0`
        have habs : |‖z - z'‖ * ((inner ℝ (g z) e : ℝ) - (inner ℝ (g z') e : ℝ))|
            ≤ 3 * C * (2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ (1 + α) := by
          rw [abs_le] at h1 h2 h3' ⊢
          constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2, h3'.1, h3'.2, hTnn, hC.le, h1le2a]
        rw [abs_mul, abs_of_pos hl0] at habs
        have hgoal : ‖z - z'‖ * |(inner ℝ (g z - g z') e : ℝ)|
            ≤ ‖z - z'‖ * (3 * C * (2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ α) := by
          rw [inner_sub_left]
          calc ‖z - z'‖ * |(inner ℝ (g z) e : ℝ) - (inner ℝ (g z') e : ℝ)|
              ≤ 3 * C * (2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ (1 + α) := habs
            _ = ‖z - z'‖ * (3 * C * (2:ℝ) ^ (1 + α) * ‖z - z'‖ ^ α) := by
                rw [hsplitT]; ring
        exact le_of_mul_le_mul_left hgoal hl0
      -- taking the supremum over unit vectors computes the norm
      rcases eq_or_ne (g z - g z') 0 with hv | hv
      · rw [hv, norm_zero]
        positivity
      · have hvp : (0:ℝ) < ‖g z - g z'‖ := norm_pos_iff.mpr hv
        have hd := hdir (‖g z - g z'‖⁻¹ • (g z - g z')) (norm_smul_inv_norm hv)
        have hcomp : (inner ℝ (g z - g z') (‖g z - g z'‖⁻¹ • (g z - g z')) : ℝ)
            = ‖g z - g z'‖ := by
          rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp
        rw [hcomp, abs_of_pos hvp] at hd
        exact le_trans hd (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg (norm_nonneg _) _))
    · -- `ℓ > ρ₀/2`: the bound `|g| ≤ C` suffices after increasing the constant
      have hb : ‖g z - g z'‖ ≤ 2 * C := by
        calc ‖g z - g z'‖ ≤ ‖g z‖ + ‖g z'‖ := norm_sub_le _ _
          _ ≤ C + C := add_le_add (hgb z hz) (hgb z' hz')
          _ = 2 * C := by ring
      have hrr : (2 / ρ₀) ^ α * (ρ₀ / 2) ^ α = 1 := by
        rw [← Real.mul_rpow (by positivity) (by positivity),
          show (2 / ρ₀) * (ρ₀ / 2) = 1 from by field_simp]
        exact Real.one_rpow _
      have hmono : (ρ₀ / 2) ^ α ≤ ‖z - z'‖ ^ α :=
        Real.rpow_le_rpow (by positivity) hfar.le hα.le
      have hstep : (2:ℝ) * C ≤ 2 * C * (2 / ρ₀) ^ α * ‖z - z'‖ ^ α := by
        calc (2:ℝ) * C = 2 * C * (2 / ρ₀) ^ α * (ρ₀ / 2) ^ α := by
              rw [mul_assoc, hrr, mul_one]
          _ ≤ 2 * C * (2 / ρ₀) ^ α * ‖z - z'‖ ^ α :=
              mul_le_mul_of_nonneg_left hmono (by positivity)
      exact le_trans hb (le_trans hstep (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (norm_nonneg _) _)))
