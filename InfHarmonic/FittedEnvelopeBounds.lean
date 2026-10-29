module

public import InfHarmonic.CenteredGrowth
public import InfHarmonic.EnvSlopeP
public import InfHarmonic.EnvSlopeM
public import InfHarmonic.EnvHamiltonianSolution
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.EnvelopeCompetitorBounds

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.5: for a centered member of `A_{m,C₀}` both envelope slopes on the
box of size `K` are at most `C L(K)⁴`, and every optimizing displacement at
length `K` has length at most `C K L(K)²`. -/
theorem FittedEnvelopeBounds (C₀ : ℝ) (hC₀ : 1 ≤ C₀) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      (IsCenteredAt C₀ v 0 ∨ IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ)))) →
      ∀ K : ℝ, 2 ≤ K → ∀ z : WithLp 2 (F × ℝ),
        ‖(ofLp z).1‖ ≤ K → |(ofLp z).2| ≤ K →
        (∀ l : ℝ, 0 < l → l ≤ K →
            EnvSlopeP v l z ≤ C * (1 + Real.log K) ^ 4 ∧
            EnvSlopeM v l z ≤ C * (1 + Real.log K) ^ 4) ∧
        (∀ y : F,
          (QuadEnvP v K z = v (toLp 2 (y, (ofLp z).2 + K))
              - ‖y - (ofLp z).1‖ ^ 2 / (2 * K) →
            ‖y - (ofLp z).1‖ ≤ C * K * (1 + Real.log K) ^ 2) ∧
          (QuadEnvM v K z = v (toLp 2 (y, (ofLp z).2 - K))
              + ‖y - (ofLp z).1‖ ^ 2 / (2 * K) →
            ‖y - (ofLp z).1‖ ≤ C * K * (1 + Real.log K) ^ 2)) := by
  classical
  -- ===================== the constants, all fixed before `v`, `K`, `z` ==============
  obtain ⟨Cg, hCg0, hCgb⟩ := CenteredGrowth (F := F) C₀ hC₀
  obtain ⟨a, had⟩ : ∃ s : ℝ, s = 16 * Cg * (1 + Real.log 2) ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ s : ℝ, s = 16 * Cg := ⟨_, rfl⟩
  obtain ⟨B₀, hB₀d⟩ : ∃ s : ℝ, s = max 2 (1024 * b ^ 2) := ⟨_, rfl⟩
  obtain ⟨C6, hC6d⟩ : ∃ s : ℝ, s = max (max (2 * a) B₀) 2 := ⟨_, rfl⟩
  obtain ⟨C7, hC7d⟩ : ∃ s : ℝ, s = 3 + C6 := ⟨_, rfl⟩
  obtain ⟨C8, hC8d⟩ : ∃ s : ℝ, s = Cg * C7 * (3 + Real.log C7) ^ 2 := ⟨_, rfl⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha0 : 0 < a := by rw [had]; positivity
  have hb0 : 0 < b := by rw [hbd]; positivity
  have hB₀2 : (2 : ℝ) ≤ B₀ := by rw [hB₀d]; exact le_max_left _ _
  have hC6a : 2 * a ≤ C6 := by rw [hC6d]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hC6B₀ : B₀ ≤ C6 := by rw [hC6d]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hC62 : (2 : ℝ) ≤ C6 := by rw [hC6d]; exact le_max_right _ _
  have hC75 : (5 : ℝ) ≤ C7 := by rw [hC7d]; linarith
  have hC70 : (0 : ℝ) < C7 := by linarith
  have hlogC7 : 0 < Real.log C7 := Real.log_pos (by linarith)
  refine ⟨max (C8 + Cg) C6 + 1, by
    have h1 : C6 ≤ max (C8 + Cg) C6 := le_max_right _ _
    linarith, ?_⟩
  -- ===================== the logarithmic bootstrap threshold ========================
  -- `b (log B)² ≤ B/2` once `B ≥ B₀`, with `B₀` EXPLICIT in `b`: the fourth root beats
  -- the logarithm, `log B ≤ 4·B^{1/4}`, so `(log B)² ≤ 16√B`, and `1024 b² ≤ B` gives
  -- `32 b ≤ √B`, hence `b (log B)² ≤ 16 b √B ≤ B/2`.
  have hboot : ∀ B : ℝ, B₀ ≤ B → b * (Real.log B) ^ 2 ≤ B / 2 := by
    intro B hB
    have hB2 : (2 : ℝ) ≤ B := le_trans hB₀2 hB
    have hBpos : 0 < B := by linarith
    have hbsq : 1024 * b ^ 2 ≤ B := le_trans (by rw [hB₀d]; exact le_max_right _ _) hB
    have hsB0 : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
    obtain ⟨r, hrd⟩ : ∃ s : ℝ, s = Real.sqrt (Real.sqrt B) := ⟨_, rfl⟩
    have hr0 : 0 < r := by
      rw [hrd]; exact Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hBpos)
    have hrsq : r ^ 2 = Real.sqrt B := by rw [hrd]; exact Real.sq_sqrt hsB0
    have hlogr : Real.log r = Real.log B / 4 := by
      rw [hrd, Real.log_sqrt hsB0, Real.log_sqrt hBpos.le]; ring
    have hlogB0 : 0 ≤ Real.log B := Real.log_nonneg (by linarith)
    have hlogB : Real.log B ≤ 4 * r := by
      have h := le_trans (Real.log_le_sub_one_of_pos hr0) (by linarith : r - 1 ≤ r)
      rw [hlogr] at h
      linarith
    have hsq : (Real.log B) ^ 2 ≤ 16 * Real.sqrt B := by
      have hm := mul_le_mul hlogB hlogB hlogB0 (by linarith)
      calc (Real.log B) ^ 2 ≤ 16 * r ^ 2 := by linarith [hm]
        _ = 16 * Real.sqrt B := by rw [hrsq]
    have hsqrtge : 32 * b ≤ Real.sqrt B := by
      have h1 : (32 * b) ^ 2 ≤ B := by linarith [hbsq]
      have h2 : Real.sqrt ((32 * b) ^ 2) ≤ Real.sqrt B := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 32 * b)] at h2
    have hBsq : Real.sqrt B * Real.sqrt B = B := Real.mul_self_sqrt hBpos.le
    have p1 : b * (Real.log B) ^ 2 ≤ b * (16 * Real.sqrt B) :=
      mul_le_mul_of_nonneg_left hsq hb0.le
    have p2 : 32 * b * Real.sqrt B ≤ Real.sqrt B * Real.sqrt B :=
      mul_le_mul_of_nonneg_right hsqrtge hsB0
    rw [hBsq] at p2
    linarith
  -- ===================== the data of one instance ===================================
  intro v hfit hcent K hK z hzx hzt
  obtain ⟨L, hLd⟩ : ∃ s : ℝ, s = 1 + Real.log K := ⟨_, rfl⟩
  rw [← hLd]
  have hK0 : 0 < K := by linarith
  have hlogK : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK
  have hlogK0 : 0 ≤ Real.log K := by linarith
  have hL1 : 1 ≤ L := by rw [hLd]; linarith
  have hL0 : 0 < L := by linarith
  have hL2ge : (1 : ℝ) ≤ L ^ 2 := by nlinarith
  have hL4ge : L ^ 2 ≤ L ^ 4 := by
    calc L ^ 2 ≤ L ^ 2 * L ^ 2 := le_mul_of_one_le_right (by positivity) hL2ge
      _ = L ^ 4 := by ring
  have hlogL : Real.log L ≤ L := by
    rcases eq_or_lt_of_le hL1 with heq | hlt
    · rw [← heq]; simp
    · exact le_trans (Real.log_le_sub_one_of_pos (by linarith)) (by linarith)
  -- Step 0: `v` is a solution on all of space-time with subquadratic spatial growth,
  -- so the envelope machinery applies with `I = ℝ`.
  have hIuniv : ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hsol : IsLimitSolutionOn
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ)) v := by
    rw [hIuniv]; exact hfit.1
  have hvcont : ContinuousOn v
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hfit.1.1.2.1
  have hgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc ε hε
    rcases hcent with hc | hc
    · obtain ⟨M, hM0, hMb⟩ :=
        UniformSubquadratic (F := F) C₀ hC₀ 0 (Or.inl rfl) J hJc ε hε
      exact ⟨M, hM0, fun ζ hζ hζJ => hMb v hfit hc ζ hζ hζJ⟩
    · obtain ⟨M, hM0, hMb⟩ :=
        UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl)
          J hJc ε hε
      exact ⟨M, hM0, fun ζ hζ hζJ => hMb v hfit hc ζ hζ hζJ⟩
  obtain ⟨hattP, hattM, -, -, -, -⟩ :=
    QuadEnvAttained (Set.univ : Set ℝ) isOpen_univ v hvcont hgrow
  obtain ⟨hdomP, hdomM, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont hgrow
  have hgb : ∀ (Θ : ℝ), 2 ≤ Θ → ∀ (y : F) (s : ℝ), ‖y‖ ≤ Θ → |s| ≤ Θ →
      |v (toLp 2 (y, s))| ≤ Cg * Θ * (1 + Real.log Θ) ^ 2 :=
    fun Θ hΘ y s hy hs => hCgb v hfit hcent Θ hΘ (toLp 2 (y, s)) hy hs
  -- ===================== Step 1: the optimizing displacements =======================
  -- One argument, used at `s = t + K` for the forward envelope and at `s = t - K` for
  -- the backward one; the hypothesis is the comparison with the competitor `y = x`.
  have hdisp : ∀ (s : ℝ), |s| ≤ 2 * K → ∀ y : F,
      ‖y - (ofLp z).1‖ ^ 2 / (2 * K)
          ≤ |v (toLp 2 (y, s))| + |v (toLp 2 ((ofLp z).1, s))| →
        ‖y - (ofLp z).1‖ ≤ C6 * K * L ^ 2 := by
    intro s hs y hcmp
    obtain ⟨D, hDd⟩ : ∃ t : ℝ, t = ‖y - (ofLp z).1‖ := ⟨_, rfl⟩
    have hD0 : 0 ≤ D := by rw [hDd]; exact norm_nonneg _
    rw [← hDd] at hcmp ⊢
    rcases le_or_gt D (2 * K) with hsmall | hbig
    · -- small displacement: `2K ≤ C₆ K L²` since `C₆ ≥ 2` and `L ≥ 1`
      have p1 : 2 * K ≤ C6 * K := mul_le_mul_of_nonneg_right hC62 hK0.le
      have p2 : C6 * K ≤ C6 * K * L ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg (by linarith) hK0.le) hL2ge
      linarith
    · -- large displacement: the growth bound in a box of size `D + 2K`
      have hDpos : 0 < D := by linarith
      obtain ⟨Θ, hΘd⟩ : ∃ t : ℝ, t = D + 2 * K := ⟨_, rfl⟩
      have hΘ4K : 4 * K ≤ Θ := by rw [hΘd]; linarith
      have hΘ2 : (2 : ℝ) ≤ Θ := by linarith
      have hΘ0 : 0 < Θ := by linarith
      have hyΘ : ‖y‖ ≤ Θ := by
        have h1 : ‖y‖ ≤ ‖y - (ofLp z).1‖ + ‖(ofLp z).1‖ := by
          simpa using norm_add_le (y - (ofLp z).1) ((ofLp z).1)
        rw [← hDd] at h1
        rw [hΘd]
        linarith
      have hxΘ : ‖(ofLp z).1‖ ≤ Θ := by linarith
      have hsΘ : |s| ≤ Θ := by linarith
      have hlogΘ0 : 0 ≤ Real.log Θ := Real.log_nonneg (by linarith)
      have hΘ2D : Θ ≤ 2 * D := by rw [hΘd]; linarith
      have hlogle : Real.log Θ ≤ Real.log (2 * D) := Real.log_le_log hΘ0 hΘ2D
      have hg1 := hgb Θ hΘ2 y s hyΘ hsΘ
      have hg2 := hgb Θ hΘ2 (ofLp z).1 s hxΘ hsΘ
      obtain ⟨P, hPd⟩ : ∃ t : ℝ, t = 1 + Real.log (2 * D) := ⟨_, rfl⟩
      have hP1 : 1 ≤ P := by
        rw [hPd]
        have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * D)
        linarith
      have hsqle : (1 + Real.log Θ) ^ 2 ≤ P ^ 2 := by
        have h1 : (0 : ℝ) ≤ 1 + Real.log Θ := by linarith
        have h2 : 1 + Real.log Θ ≤ P := by rw [hPd]; linarith
        have hm := mul_le_mul h2 h2 h1 (by linarith)
        linarith [hm]
      have hcmp' : D ^ 2 ≤ 2 * K * (|v (toLp 2 (y, s))| + |v (toLp 2 ((ofLp z).1, s))|) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * K)] at hcmp
        linarith
      have hGle : Cg * Θ * (1 + Real.log Θ) ^ 2 ≤ Cg * (2 * D) * P ^ 2 := by
        have s1 : Cg * Θ * (1 + Real.log Θ) ^ 2 ≤ Cg * Θ * P ^ 2 :=
          mul_le_mul_of_nonneg_left hsqle (by positivity)
        have s2 : Cg * Θ * P ^ 2 ≤ Cg * (2 * D) * P ^ 2 := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_left hΘ2D hCg0.le
        linarith
      -- `D² ≤ 8 Cg K D P²`, each product named so that `linarith` suffices
      have q1 : K * |v (toLp 2 (y, s))| ≤ K * (Cg * Θ * (1 + Real.log Θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hg1 hK0.le
      have q2 : K * |v (toLp 2 ((ofLp z).1, s))| ≤ K * (Cg * Θ * (1 + Real.log Θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hg2 hK0.le
      have q3 : K * (Cg * Θ * (1 + Real.log Θ) ^ 2) ≤ K * (Cg * (2 * D) * P ^ 2) :=
        mul_le_mul_of_nonneg_left hGle hK0.le
      have hDD : D * D ≤ (8 * Cg * K * P ^ 2) * D := by linarith
      have hDle : D ≤ 8 * Cg * K * P ^ 2 := le_of_mul_le_mul_right (by linarith) hDpos
      -- in terms of `B = D / K`
      obtain ⟨B, hBd⟩ : ∃ t : ℝ, t = D / K := ⟨_, rfl⟩
      have hDBK : D = B * K := by rw [hBd]; field_simp
      have hB0 : 0 < B := by rw [hBd]; positivity
      have hBle : B ≤ 8 * Cg * P ^ 2 := by
        rw [hBd, div_le_iff₀ hK0]
        linarith
      have hlogsplit : Real.log (2 * D) = Real.log 2 + Real.log B + Real.log K := by
        rw [hDBK, Real.log_mul (by norm_num) (mul_ne_zero (ne_of_gt hB0) (ne_of_gt hK0)),
          Real.log_mul (ne_of_gt hB0) (ne_of_gt hK0)]
        ring
      -- absorb the constant and the `log K` into `L`
      have hu0 : (0 : ℝ) ≤ 1 + Real.log 2 + Real.log K := by linarith
      have hu : 1 + Real.log 2 + Real.log K ≤ (1 + Real.log 2) * L := by
        have he : (1 + Real.log 2) * L = (1 + Real.log 2) + (1 + Real.log 2) * Real.log K := by
          rw [hLd]; ring
        have hp : Real.log K ≤ (1 + Real.log 2) * Real.log K := by
          linarith [mul_nonneg hlog2.le hlogK0]
        linarith
      have husq : (1 + Real.log 2 + Real.log K) ^ 2 ≤ (1 + Real.log 2) ^ 2 * L ^ 2 := by
        have hm := mul_le_mul hu hu hu0 (mul_nonneg (by linarith) hL0.le)
        linarith [hm]
      have hPsq : P ^ 2 ≤ 2 * (1 + Real.log 2 + Real.log K) ^ 2 + 2 * (Real.log B) ^ 2 := by
        have hP : P = (1 + Real.log 2 + Real.log K) + Real.log B := by
          rw [hPd, hlogsplit]; ring
        rw [hP]
        linarith [sq_nonneg ((1 + Real.log 2 + Real.log K) - Real.log B)]
      have hBineq : B ≤ a * L ^ 2 + b * (Real.log B) ^ 2 := by
        have r1 : Cg * P ^ 2
            ≤ Cg * (2 * (1 + Real.log 2 + Real.log K) ^ 2 + 2 * (Real.log B) ^ 2) :=
          mul_le_mul_of_nonneg_left hPsq hCg0.le
        have r2 : Cg * (1 + Real.log 2 + Real.log K) ^ 2
            ≤ Cg * ((1 + Real.log 2) ^ 2 * L ^ 2) :=
          mul_le_mul_of_nonneg_left husq hCg0.le
        rw [had, hbd]
        linarith
      -- the bootstrap
      have hBfinal : B ≤ C6 * L ^ 2 := by
        rcases le_or_gt B₀ B with hge | hlt
        · have h1 := hboot B hge
          have h3 : B ≤ 2 * a * L ^ 2 := by linarith
          have h4 : 2 * a * L ^ 2 ≤ C6 * L ^ 2 :=
            mul_le_mul_of_nonneg_right hC6a (by positivity)
          linarith
        · have h5 : B ≤ C6 := by linarith
          have h6 : C6 ≤ C6 * L ^ 2 := le_mul_of_one_le_right (by linarith) hL2ge
          linarith
      rw [hDBK]
      have hfin := mul_le_mul_of_nonneg_right hBfinal hK0.le
      linarith
  -- ===================== Step 2: the slopes at length `K` ===========================
  have hvbig : ∀ (s : ℝ), |s| ≤ 2 * K → ∀ y : F, ‖y - (ofLp z).1‖ ≤ C6 * K * L ^ 2 →
      |v (toLp 2 (y, s))| ≤ C8 * K * L ^ 4 := by
    intro s hs y hy
    obtain ⟨K₁, hK₁d⟩ : ∃ t : ℝ, t = C7 * K * L ^ 2 := ⟨_, rfl⟩
    have hK₁K : 5 * K ≤ K₁ := by
      rw [hK₁d]
      have p1 : 5 * K ≤ C7 * K := mul_le_mul_of_nonneg_right hC75 hK0.le
      have p2 : C7 * K ≤ C7 * K * L ^ 2 :=
        le_mul_of_one_le_right (mul_nonneg hC70.le hK0.le) hL2ge
      linarith
    have hK₁2 : (2 : ℝ) ≤ K₁ := by linarith
    have hK₁0 : 0 < K₁ := by linarith
    have hyK₁ : ‖y‖ ≤ K₁ := by
      have h1 : ‖y‖ ≤ ‖y - (ofLp z).1‖ + ‖(ofLp z).1‖ := by
        simpa using norm_add_le (y - (ofLp z).1) ((ofLp z).1)
      have h2 : ‖y‖ ≤ C6 * K * L ^ 2 + K := by linarith
      have h3 : K ≤ K * L ^ 2 := le_mul_of_one_le_right hK0.le hL2ge
      have he : K₁ = 3 * (K * L ^ 2) + C6 * K * L ^ 2 := by rw [hK₁d, hC7d]; ring
      rw [he]
      linarith
    have hsK₁ : |s| ≤ K₁ := by linarith
    have hgK₁ := hgb K₁ hK₁2 y s hyK₁ hsK₁
    have he : Real.log K₁ = Real.log C7 + Real.log K + 2 * Real.log L := by
      rw [hK₁d, Real.log_mul (mul_ne_zero (ne_of_gt hC70) (ne_of_gt hK0))
          (pow_ne_zero 2 (ne_of_gt hL0)),
        Real.log_mul (ne_of_gt hC70) (ne_of_gt hK0), Real.log_pow]
      push_cast
      ring
    have hlogK₁ : 1 + Real.log K₁ ≤ (3 + Real.log C7) * L := by
      have p1 : Real.log C7 ≤ Real.log C7 * L := le_mul_of_one_le_right hlogC7.le hL1
      have p2 : (3 + Real.log C7) * L = 3 * L + Real.log C7 * L := by ring
      rw [he]
      have p3 : L = 1 + Real.log K := hLd
      linarith
    have hlogK₁0 : (0 : ℝ) ≤ 1 + Real.log K₁ := by
      have h := Real.log_nonneg (by linarith : (1 : ℝ) ≤ K₁)
      linarith
    have hsq : (1 + Real.log K₁) ^ 2 ≤ (3 + Real.log C7) ^ 2 * L ^ 2 := by
      have hm := mul_le_mul hlogK₁ hlogK₁ hlogK₁0 (mul_nonneg (by linarith) hL0.le)
      linarith [hm]
    calc |v (toLp 2 (y, s))| ≤ Cg * K₁ * (1 + Real.log K₁) ^ 2 := hgK₁
      _ ≤ Cg * K₁ * ((3 + Real.log C7) ^ 2 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (mul_nonneg hCg0.le hK₁0.le)
      _ = C8 * K * L ^ 4 := by rw [hK₁d, hC8d]; ring
  -- the two attained optimizers at length `K`, and the two comparison inequalities
  obtain ⟨yP, hyP⟩ : ∃ y : F, QuadEnvP v K z
      = v (toLp 2 (y, (ofLp z).2 + K)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * K) :=
    hattP K z hK0 (Set.mem_univ _) (Set.mem_univ _)
  obtain ⟨yM, hyM⟩ : ∃ y : F, QuadEnvM v K z
      = v (toLp 2 (y, (ofLp z).2 - K)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * K) :=
    hattM K z hK0 (Set.mem_univ _) (Set.mem_univ _)
  have hsP : |(ofLp z).2 + K| ≤ 2 * K := by
    rcases abs_le.mp hzt with ⟨h1, h2⟩
    rw [abs_le]; constructor <;> linarith
  have hsM : |(ofLp z).2 - K| ≤ 2 * K := by
    rcases abs_le.mp hzt with ⟨h1, h2⟩
    rw [abs_le]; constructor <;> linarith
  have hcmpP : ∀ y : F, QuadEnvP v K z
      = v (toLp 2 (y, (ofLp z).2 + K)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * K) →
      ‖y - (ofLp z).1‖ ^ 2 / (2 * K)
        ≤ |v (toLp 2 (y, (ofLp z).2 + K))| + |v (toLp 2 ((ofLp z).1, (ofLp z).2 + K))| := by
    intro y hy
    have hcomp := (hdomP K z hK0 (Set.mem_univ _) (Set.mem_univ _)).1 (ofLp z).1
    rw [sub_self, norm_zero] at hcomp
    have h0 : (0 : ℝ) ^ 2 / (2 * K) = 0 := by norm_num
    rw [h0, sub_zero] at hcomp
    have h1 := le_abs_self (v (toLp 2 (y, (ofLp z).2 + K)))
    have h2 := neg_abs_le (v (toLp 2 ((ofLp z).1, (ofLp z).2 + K)))
    rw [hy] at hcomp
    linarith
  have hcmpM : ∀ y : F, QuadEnvM v K z
      = v (toLp 2 (y, (ofLp z).2 - K)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * K) →
      ‖y - (ofLp z).1‖ ^ 2 / (2 * K)
        ≤ |v (toLp 2 (y, (ofLp z).2 - K))| + |v (toLp 2 ((ofLp z).1, (ofLp z).2 - K))| := by
    intro y hy
    have hcomp := (hdomM K z hK0 (Set.mem_univ _) (Set.mem_univ _)).1 (ofLp z).1
    rw [sub_self, norm_zero] at hcomp
    have h0 : (0 : ℝ) ^ 2 / (2 * K) = 0 := by norm_num
    rw [h0, add_zero] at hcomp
    have h1 := neg_abs_le (v (toLp 2 (y, (ofLp z).2 - K)))
    have h2 := le_abs_self (v (toLp 2 ((ofLp z).1, (ofLp z).2 - K)))
    rw [hy] at hcomp
    linarith
  have hvz : |v z| ≤ Cg * K * L ^ 2 := by
    rw [hLd]
    exact hCgb v hfit hcent K hK z hzx hzt
  have hvz4 : |v z| ≤ Cg * K * L ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hL4ge (mul_nonneg hCg0.le hK0.le)
    linarith
  have hslopeP : EnvSlopeP v K z ≤ (C8 + Cg) * L ^ 4 := by
    have hd := hdisp _ hsP yP (hcmpP yP hyP)
    have hbg := hvbig _ hsP yP hd
    have hle : QuadEnvP v K z ≤ C8 * K * L ^ 4 := by
      have h1 := le_abs_self (v (toLp 2 (yP, (ofLp z).2 + K)))
      have h2 : (0 : ℝ) ≤ ‖yP - (ofLp z).1‖ ^ 2 / (2 * K) := by positivity
      rw [hyP]
      linarith
    have h3 := neg_abs_le (v z)
    rw [EnvSlopeP, div_le_iff₀ hK0]
    linarith
  have hslopeM : EnvSlopeM v K z ≤ (C8 + Cg) * L ^ 4 := by
    have hd := hdisp _ hsM yM (hcmpM yM hyM)
    have hbg := hvbig _ hsM yM hd
    have hge : -(C8 * K * L ^ 4) ≤ QuadEnvM v K z := by
      have h1 := neg_abs_le (v (toLp 2 (yM, (ofLp z).2 - K)))
      have h2 : (0 : ℝ) ≤ ‖yM - (ofLp z).1‖ ^ 2 / (2 * K) := by positivity
      rw [hyM]
      linarith
    have h3 := le_abs_self (v z)
    rw [EnvSlopeM, div_le_iff₀ hK0]
    linarith
  -- ===================== Step 3: all lengths `0 < l ≤ K` ===========================
  obtain ⟨hmono, -, -, -⟩ :=
    EnvHamiltonianSolution (Set.univ : Set ℝ) isOpen_univ v hvcont hgrow hsol
  have hCmax : C8 + Cg ≤ max (C8 + Cg) C6 := le_max_left _ _
  have hCmax6 : C6 ≤ max (C8 + Cg) C6 := le_max_right _ _
  have hslope4 : (C8 + Cg) * L ^ 4 ≤ (max (C8 + Cg) C6 + 1) * L ^ 4 :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hdisp4 : C6 * K * L ^ 2 ≤ (max (C8 + Cg) C6 + 1) * K * L ^ 2 := by
    have p1 : C6 * K ≤ (max (C8 + Cg) C6 + 1) * K :=
      mul_le_mul_of_nonneg_right (by linarith) hK0.le
    exact mul_le_mul_of_nonneg_right p1 (by positivity)
  refine ⟨fun l hl hlK => ?_, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · obtain ⟨m1, m2⟩ := hmono z l K hl hlK fun σ _ => Set.mem_univ _
    exact ⟨by linarith, by linarith⟩
  · have hd := hdisp _ hsP y (hcmpP y hy)
    linarith
  · have hd := hdisp _ hsM y (hcmpM y hy)
    linarith
