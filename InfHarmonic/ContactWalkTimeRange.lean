import InfHarmonic.IsContactWalk
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The grid consequence (G4) for a stopped contact walk: the time coordinate
never leaves the closed interval `[δ_N, T]`, at any index and at every point,
even after the walk has stopped. -/
theorem ContactWalkTimeRange (κ H : ℝ) (v : WithLp 2 (F × ℝ) → ℝ)
    (T : ℕ) (R : ℝ) (N : ℕ) (ε : ℝ)
    (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
    (ξ : ℕ → Ω → ℝ) (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F)
    (τ : Ω → ℕ) :
    IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ → 1 ≤ N → 1 ≤ T →
    ∀ (n : ℕ) (ω : Ω),
      (1 / 2 : ℝ) ^ N ≤ (ofLp (z n ω)).2 ∧ (ofLp (z n ω)).2 ≤ (T : ℝ) := by
  classical
  intro hcw hN hT
  obtain ⟨hμ1, ⟨k, hεk⟩, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
    hstep, hrec, hgradc, hτst, hτint, hlive, hexit, hxbd, hstart⟩ := hcw
  -- ## (G1) the grid: `ε = 2⁻ᵏ` with `k ≥ N + 2`, so `δ_N`, `1` and `T` are multiples of `ε`
  have hhalfpow : ∀ i : ℕ, (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ i = 1 := by
    intro i
    rw [← mul_pow]
    norm_num
  have hkN : N + 2 ≤ k := by
    have h2 : (1 / 2 : ℝ) ^ N / 4 = (1 / 2 : ℝ) ^ (N + 2) := by
      rw [pow_add]
      ring
    rw [hεk, h2] at hεN
    exact (pow_le_pow_iff_right_of_lt_one₀ (by norm_num) (by norm_num)).mp hεN
  have hgridpow : ∀ i : ℕ, i ≤ k → ∃ m : ℤ, (1 / 2 : ℝ) ^ i = (m : ℝ) * ε := by
    intro i hik
    refine ⟨2 ^ (k - i), ?_⟩
    have h1 : (2 : ℝ) ^ (k - i) * (2 : ℝ) ^ i = (2 : ℝ) ^ k := by
      rw [← pow_add, Nat.sub_add_cancel hik]
    have h2 : (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ k = (2 : ℝ) ^ (k - i) := by
      calc (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ k
          = (1 / 2 : ℝ) ^ i * ((2 : ℝ) ^ i * (2 : ℝ) ^ (k - i)) := by
            rw [← h1]; ring
        _ = ((1 / 2 : ℝ) ^ i * (2 : ℝ) ^ i) * (2 : ℝ) ^ (k - i) := by ring
        _ = (2 : ℝ) ^ (k - i) := by rw [hhalfpow i, one_mul]
    have h3 : (((2 : ℤ) ^ (k - i) : ℤ) : ℝ) * ε = (2 : ℝ) ^ (k - i) * ε := by
      norm_num
    rw [h3, hεk]
    have h4 : (2 : ℝ) ^ (k - i) * (1 / 2 : ℝ) ^ k = (1 / 2 : ℝ) ^ i := by
      rw [← h2]
      calc (1 / 2 : ℝ) ^ i * (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k
          = (1 / 2 : ℝ) ^ i * ((1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k) := by ring
        _ = (1 / 2 : ℝ) ^ i := by rw [hhalfpow k, mul_one]
    rw [h4]
  have hone : ∃ m : ℤ, (1 : ℝ) = (m : ℝ) * ε := by
    have h1 := hgridpow 0 (by omega)
    simpa using h1
  have hdN : ∃ m : ℤ, (1 / 2 : ℝ) ^ N = (m : ℝ) * ε := hgridpow N (by omega)
  have hTmult : ∃ m : ℤ, (T : ℝ) = (m : ℝ) * ε := by
    obtain ⟨m, hm⟩ := hone
    refine ⟨(T : ℤ) * m, ?_⟩
    push_cast
    rw [mul_assoc, ← hm, mul_one]
  -- ## (G2) the time coordinate moves by `0` or `±ε`
  have hstepT : ∀ (n : ℕ) (ω : Ω),
      (ofLp (z (n + 1) ω)).2 = (ofLp (z n ω)).2
        ∨ (ofLp (z (n + 1) ω)).2 = (ofLp (z n ω)).2 + ε
        ∨ (ofLp (z (n + 1) ω)).2 = (ofLp (z n ω)).2 - ε := by
    intro n ω
    rcases Nat.lt_or_ge n (τ ω) with hn | hn
    · obtain ⟨Yp, Ym, -, -, hzpe, hzme⟩ := hstep n ω hn
      rw [hrec n ω, if_pos hn]
      by_cases hb : ξ n ω = 1
      · rw [if_pos hb, hzpe]
        refine Or.inr (Or.inl ?_)
        simp
      · rw [if_neg hb, hzme]
        refine Or.inr (Or.inr ?_)
        simp
    · rw [hrec n ω, if_neg (by omega)]
      exact Or.inl rfl
  -- ## (G3) every time coordinate is an integer multiple of `ε`
  have hmult : ∀ (n : ℕ) (ω : Ω), ∃ m : ℤ, (ofLp (z n ω)).2 = (m : ℝ) * ε := by
    intro n ω
    induction n with
    | zero =>
      rw [hz0 ω]
      have h1 : (ofLp (toLp 2 ((0 : F), (1 : ℝ))) : F × ℝ).2 = 1 := by simp
      rw [h1]
      exact hone
    | succ n ih =>
      obtain ⟨m, hm⟩ := ih
      rcases hstepT n ω with h | h | h
      · exact ⟨m, by rw [h, hm]⟩
      · refine ⟨m + 1, ?_⟩
        rw [h, hm]
        push_cast
        ring
      · refine ⟨m - 1, ?_⟩
        rw [h, hm]
        push_cast
        ring
  -- ## a strict inequality between multiples of `ε` leaves a gap of at least `ε`
  have hgap : ∀ x c : ℝ, (∃ m : ℤ, x = (m : ℝ) * ε) → (∃ m : ℤ, c = (m : ℝ) * ε) →
      x < c → x + ε ≤ c := by
    intro x c hx hc hlt
    obtain ⟨m1, hm1⟩ := hx
    obtain ⟨m2, hm2⟩ := hc
    have h1 : (m1 : ℝ) < (m2 : ℝ) := by
      refine lt_of_mul_lt_mul_right ?_ hε0.le
      rw [← hm1, ← hm2]
      exact hlt
    have h2 : m1 + 1 ≤ m2 := by
      have h3 : m1 < m2 := by exact_mod_cast h1
      omega
    have h4 : ((m1 + 1 : ℤ) : ℝ) ≤ ((m2 : ℤ) : ℝ) := by exact_mod_cast h2
    have h5 : ((m1 : ℝ) + 1) * ε ≤ (m2 : ℝ) * ε := by
      refine mul_le_mul_of_nonneg_right ?_ hε0.le
      push_cast at h4
      exact h4
    rw [hm1, hm2]
    nlinarith [h5]
  -- ## (G4) the time coordinate stays in `[δ_N, T]`
  have hδ1 : (1 / 2 : ℝ) ^ N ≤ 1 / 2 := by
    calc (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ 1 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) hN
      _ = 1 / 2 := by norm_num
  have hT1 : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
  intro n ω
  induction n with
  | zero =>
    rw [hz0 ω]
    have h1 : (ofLp (toLp 2 ((0 : F), (1 : ℝ))) : F × ℝ).2 = 1 := by simp
    rw [h1]
    exact ⟨by linarith, hT1⟩
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rcases Nat.lt_or_ge n (τ ω) with hn | hn
    · obtain ⟨hlo, hhi, -⟩ := hlive n ω hn
      have hlow : (1 / 2 : ℝ) ^ N + ε ≤ (ofLp (z n ω)).2 :=
        hgap _ _ hdN (hmult n ω) hlo
      have hhigh : (ofLp (z n ω)).2 + ε ≤ (T : ℝ) :=
        hgap _ _ (hmult n ω) hTmult hhi
      rcases hstepT n ω with h | h | h
      · rw [h]; exact ⟨ih1, ih2⟩
      · rw [h]; exact ⟨by linarith, hhigh⟩
      · rw [h]; exact ⟨by linarith, by linarith [hε0]⟩
    · rw [hrec n ω, if_neg (by omega)]
      exact ⟨ih1, ih2⟩
