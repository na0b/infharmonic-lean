import InfHarmonic.IsContactWalk
import InfHarmonic.IsMarkData
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The grid consequence for the marks of a stopped contact walk: the time of
the mark at level `j` is never below `2⁻ʲ`, and it is exactly `2⁻ʲ` whenever the
walk stops at the bottom level `2⁻ᴺ`. -/
theorem ContactWalkMarkLevels (C₀ κ H : ℝ) (v : WithLp 2 (F × ℝ) → ℝ)
    (T : ℕ) (R : ℝ) (N : ℕ) (ε : ℝ)
    (Ω : Type) (m0 : MeasurableSpace Ω) (μ : Measure Ω) (𝒢 : Filtration ℕ m0)
    (ξ : ℕ → Ω → ℝ) (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ)) (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ)
    (smark : ℕ → Ω → ℕ) (pj : ℕ → Ω → F) (aj : ℕ → Ω → ℝ) :
    IsContactWalk κ H T R v N ε μ 𝒢 ξ z zp zm Q₀ τ →
    IsMarkData C₀ v N 𝒢 z τ smark pj aj →
    ∀ j : ℕ, 1 ≤ j → j ≤ N →
      (∀ ω, (1 / 2 : ℝ) ^ j ≤ (ofLp (z (smark j ω) ω)).2) ∧
      (∀ ω, (ofLp (z (τ ω) ω)).2 = (1 / 2 : ℝ) ^ N →
        (ofLp (z (smark j ω) ω)).2 = (1 / 2 : ℝ) ^ j) := by
  classical
  intro hcw hmd j hj1 hjN
  obtain ⟨hμ1, ⟨k, hεk⟩, hε0, hεN, hξpm, hξsm, hξce, hzSM, hzpSM, hzmSM, hQSM, hz0,
    hstep, hrec, hgradc, hτst, hτint, hlive, hexit, hxbd, hstart⟩ := hcw
  obtain ⟨hsmst, hsmle, hsmlt, hsmalt, hpm5, hpm6, hfit7, hfit8⟩ := hmd j hj1 hjN
  -- ## (G1) the grid: `ε = 2⁻ᵏ` with `k ≥ N + 2`, and `1`, `δ_j` are multiples of `ε`
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
  have hε0' : 0 < ε := hε0
  have hone : ∃ m : ℤ, (1 : ℝ) = (m : ℝ) * ε := by
    have h1 := hgridpow 0 (by omega)
    simpa using h1
  have hdj : ∃ m : ℤ, (1 / 2 : ℝ) ^ j = (m : ℝ) * ε := hgridpow j (by omega)
  have hdN : ∃ m : ℤ, (1 / 2 : ℝ) ^ N = (m : ℝ) * ε := hgridpow N (by omega)
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
  -- ## two multiples of `ε` in a half-open interval of length `ε` coincide
  have hmultuniq : ∀ (x c : ℝ), (∃ m : ℤ, x = (m : ℝ) * ε) → (∃ m : ℤ, c = (m : ℝ) * ε) →
      c - ε < x → x ≤ c → x = c := by
    intro x c hx hc hlow hhigh
    obtain ⟨m1, hm1⟩ := hx
    obtain ⟨m2, hm2⟩ := hc
    have h1 : ((m2 : ℝ) - 1) * ε < (m1 : ℝ) * ε := by
      have h0 : ((m2 : ℝ) - 1) * ε = (m2 : ℝ) * ε - ε := by ring
      rw [h0, ← hm1, ← hm2]
      exact hlow
    have h2 : (m1 : ℝ) * ε ≤ (m2 : ℝ) * ε := by
      rw [← hm1, ← hm2]
      exact hhigh
    have h3 : (m2 : ℝ) - 1 < (m1 : ℝ) := lt_of_mul_lt_mul_right h1 hε0.le
    have h4 : (m1 : ℝ) ≤ (m2 : ℝ) := le_of_mul_le_mul_right h2 hε0
    have h5 : m1 = m2 := by
      have h6 : m2 - 1 < m1 := by
        have h7 : ((m2 - 1 : ℤ) : ℝ) < ((m1 : ℤ) : ℝ) := by
          push_cast
          linarith
        exact_mod_cast h7
      have h8 : m1 ≤ m2 := by exact_mod_cast h4
      omega
    rw [hm1, hm2, h5]
  -- ## (G5) the discrete intermediate value property
  have hIVT : ∀ (ω : Ω) (c : ℝ), (∃ m : ℤ, c = (m : ℝ) * ε) →
      ∀ b : ℕ, (ofLp (z b ω)).2 ≤ c → c ≤ (ofLp (z 0 ω)).2 →
        ∃ n : ℕ, n ≤ b ∧ (ofLp (z n ω)).2 = c := by
    intro ω c hc b
    induction b with
    | zero =>
      intro h1 h2
      exact ⟨0, le_rfl, le_antisymm h1 h2⟩
    | succ b ih =>
      intro h1 h2
      by_cases hb : (ofLp (z b ω)).2 ≤ c
      · obtain ⟨n, hn1, hn2⟩ := ih hb h2
        exact ⟨n, by omega, hn2⟩
      · have hbc : c < (ofLp (z b ω)).2 := lt_of_not_ge hb
        have heq : (ofLp (z (b + 1) ω)).2 = (ofLp (z b ω)).2 - ε := by
          rcases hstepT b ω with h | h | h
          · exfalso
            rw [h] at h1
            linarith
          · exfalso
            rw [h] at h1
            linarith
          · exact h
        have hlow : c - ε < (ofLp (z (b + 1) ω)).2 := by
          rw [heq]
          linarith
        exact ⟨b + 1, le_rfl, hmultuniq _ _ (hmult (b + 1) ω) hc hlow h1⟩
  -- ## the two mark-level facts
  have h0t : ∀ ω : Ω, (ofLp (z 0 ω)).2 = 1 := by
    intro ω
    rw [hz0 ω]
  have hdjle1 : (1 / 2 : ℝ) ^ j ≤ 1 := by
    calc (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ 0 :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      _ = 1 := by norm_num
  refine ⟨fun ω => ?_, fun ω hflag => ?_⟩
  · by_contra hc
    have hlt : (ofLp (z (smark j ω) ω)).2 < (1 / 2 : ℝ) ^ j := lt_of_not_ge hc
    obtain ⟨n, hn1, hn2⟩ := hIVT ω ((1 / 2 : ℝ) ^ j) hdj (smark j ω) (le_of_lt hlt)
      (by rw [h0t ω]; exact hdjle1)
    have hne : n ≠ smark j ω := by
      intro hceq
      rw [hceq] at hn2
      rw [hn2] at hlt
      linarith
    exact (hsmlt ω n (by omega)).2 hn2
  · have hdNj : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ j :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hjN
    have hex0 : ∃ n : ℕ, n ≤ τ ω ∧ (ofLp (z n ω)).2 = (1 / 2 : ℝ) ^ j := by
      refine hIVT ω _ hdj (τ ω) ?_ (by rw [h0t ω]; exact hdjle1)
      rw [hflag]
      exact hdNj
    have hex : ∃ n : ℕ, (ofLp (z n ω)).2 = (1 / 2 : ℝ) ^ j := by
      obtain ⟨n, -, hn⟩ := hex0
      exact ⟨n, hn⟩
    obtain ⟨nw, hnw1, hnw2⟩ := hex0
    have hfind : (ofLp (z (Nat.find hex) ω)).2 = (1 / 2 : ℝ) ^ j := Nat.find_spec hex
    have hfindle : Nat.find hex ≤ τ ω := le_trans (Nat.find_le hnw2) hnw1
    have hsmlefind : smark j ω ≤ Nat.find hex := by
      by_contra hcc
      have h1 : Nat.find hex < smark j ω := by omega
      exact (hsmlt ω (Nat.find hex) h1).2 hfind
    rcases hsmalt ω with h | h
    · have h2 : smark j ω = Nat.find hex := by
        have h3 : Nat.find hex ≤ smark j ω := by
          rw [h]
          exact hfindle
        omega
      rw [h2]
      exact hfind
    · exact h
