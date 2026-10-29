import InfHarmonic.BaryEnv
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Steps 0 and 1 of Lemma 5.2: the configuration-radius identity that turns the
competitor set of `BaryEnv` into the set of `g`-averages, the resulting fact that
the barycentric supremum is a genuine least upper bound dominating every
configuration value, and weak duality against every slope. -/
theorem BaryEnvWeakDuality (f : WithLp 2 (F × ℝ) → ℝ) (s : ℝ) (hs : 0 < s)
    (z : WithLp 2 (F × ℝ))
    (hbdd : ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, (ofLp z).2)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)}) :
    (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), IsBaryConfig n θ y (ofLp z).1 →
        (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s) - ‖(ofLp z).1‖ ^ 2 / (2 * s)
          = ∑ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s))) ∧
    (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), IsBaryConfig n θ y (ofLp z).1 →
        (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s) ≤ BaryEnv f s z) ∧
    (∀ A : F, BaryEnv f s z - ‖(ofLp z).1‖ ^ 2 / (2 * s)
        ≤ sSup {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, (ofLp z).2)) - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - (ofLp z).1)}) := by
  -- Body-only acknowledgements (traps 2 and 3): the instance bundle and `hs` are part of this
  -- node's protected signature, and this Lean route reaches the conclusions without consuming
  -- them, so they are named here rather than by editing any line above `-- BODY`.
  have _ : FiniteDimensional ℝ F := inferInstance
  have _ := hs
  -- Each slope functional is a genuine least upper bound: this is `hbdd` plus nonemptiness.
  have hlub : ∀ A y : F, f (toLp 2 (y, (ofLp z).2)) - ‖y‖ ^ 2 / (2 * s)
        - inner ℝ A (y - (ofLp z).1)
      ≤ sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A (y' - (ofLp z).1)} :=
    fun A y => le_csSup (hbdd A) ⟨y, rfl⟩
  -- STEP 0 / conclusion (1): the configuration-radius identity.
  have hid : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), IsBaryConfig n θ y (ofLp z).1 →
      (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
          - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s) - ‖(ofLp z).1‖ ^ 2 / (2 * s)
        = ∑ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s)) := by
    intro n θ y hcfg
    obtain ⟨hpos, hθ1, hmean⟩ := hcfg
    -- ∑ θᵢ ⟪yᵢ, x⟫ = ‖x‖², by pulling the weights into the first argument
    have hinner : ∑ i, θ i * (inner ℝ (y i) ((ofLp z).1) : ℝ) = ‖(ofLp z).1‖ ^ 2 := by
      have h1 : ∑ i, θ i * (inner ℝ (y i) ((ofLp z).1) : ℝ)
          = (inner ℝ (∑ i, θ i • y i) ((ofLp z).1) : ℝ) := by
        rw [sum_inner]
        exact Finset.sum_congr rfl fun i _ => (real_inner_smul_left _ _ _).symm
      rw [h1, hmean, real_inner_self_eq_norm_sq]
    -- the expansion of the squared distances
    have hexp : ∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2
        = (∑ i, θ i * ‖y i‖ ^ 2) - ‖(ofLp z).1‖ ^ 2 := by
      have hterm : ∀ i : Fin n, θ i * ‖y i - (ofLp z).1‖ ^ 2
          = θ i * ‖y i‖ ^ 2 - 2 * (θ i * (inner ℝ (y i) ((ofLp z).1) : ℝ))
            + θ i * ‖(ofLp z).1‖ ^ 2 := by
        intro i
        rw [norm_sub_sq_real]
        ring
      calc ∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2
          = ∑ i, (θ i * ‖y i‖ ^ 2 - 2 * (θ i * (inner ℝ (y i) ((ofLp z).1) : ℝ))
              + θ i * ‖(ofLp z).1‖ ^ 2) := Finset.sum_congr rfl fun i _ => hterm i
        _ = (∑ i, θ i * ‖y i‖ ^ 2) - ‖(ofLp z).1‖ ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hinner,
              ← Finset.sum_mul, hθ1, one_mul]
            ring
    -- the radius is a square root, so establish nonnegativity BEFORE squaring
    have hnn : (0:ℝ) ≤ ∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)
    have hrad : BaryRadius n θ y (ofLp z).1 ^ 2
        = (∑ i, θ i * ‖y i‖ ^ 2) - ‖(ofLp z).1‖ ^ 2 := by
      rw [BaryRadius, Real.sq_sqrt hnn, hexp]
    have hdist : ∑ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s))
        = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2))) - (∑ i, θ i * ‖y i‖ ^ 2) / (2 * s) := by
      rw [Finset.sum_div, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hrad, hdist]
    ring
  -- STEP 1: weak duality on the g-averages, against every slope.
  have hweak : ∀ (A : F) (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
      IsBaryConfig n θ y (ofLp z).1 →
      ∑ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s))
        ≤ sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2)) - ‖y'‖ ^ 2 / (2 * s)
            - inner ℝ A (y' - (ofLp z).1)} := by
    intro A n θ y hcfg
    obtain ⟨hpos, hθ1, hmean⟩ := hcfg
    obtain ⟨Γ, hΓ⟩ : ∃ r : ℝ, r = sSup {w : ℝ | ∃ y' : F,
        w = f (toLp 2 (y', (ofLp z).2)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A (y' - (ofLp z).1)} := ⟨_, rfl⟩
    rw [← hΓ]
    have hzero : ∑ i, θ i • (y i - (ofLp z).1) = (0:F) := by
      simp only [smul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_smul, hmean, hθ1, one_smul, sub_self]
    have hlin : ∑ i, θ i * (inner ℝ A (y i - (ofLp z).1) : ℝ)
        = (inner ℝ A (∑ i, θ i • (y i - (ofLp z).1)) : ℝ) := by
      rw [inner_sum]
      exact Finset.sum_congr rfl fun i _ => (real_inner_smul_right _ _ _).symm
    calc ∑ i, θ i * (f (toLp 2 (y i, (ofLp z).2)) - ‖y i‖ ^ 2 / (2 * s))
        ≤ ∑ i, (θ i * Γ + θ i * (inner ℝ A (y i - (ofLp z).1) : ℝ)) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h := hlub A (y i)
          rw [← hΓ] at h
          nlinarith [mul_le_mul_of_nonneg_left h (hpos i).le]
      _ = Γ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, hθ1, one_mul, hlin, hzero,
            inner_zero_right, add_zero]
  -- the barycentric competitor set is nonempty, via the single-point configuration
  have hBne : {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
      IsBaryConfig n θ y (ofLp z).1 ∧
      w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)}.Nonempty :=
    ⟨_, ⟨1, fun _ => 1, fun _ => (ofLp z).1,
      ⟨fun i => one_pos, by simp, by simp⟩, rfl⟩⟩
  -- and bounded above, by the A = 0 instance of weak duality together with (1)
  have hBbdd : BddAbove {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
      IsBaryConfig n θ y (ofLp z).1 ∧
      w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)} := by
    refine ⟨sSup {w : ℝ | ∃ y' : F, w = f (toLp 2 (y', (ofLp z).2)) - ‖y'‖ ^ 2 / (2 * s)
        - inner ℝ (0 : F) (y' - (ofLp z).1)} + ‖(ofLp z).1‖ ^ 2 / (2 * s), ?_⟩
    rintro w ⟨n, θ, y, hcfg, rfl⟩
    have h1 := hid n θ y hcfg
    have h2 := hweak 0 n θ y hcfg
    linarith
  refine ⟨hid, ?_, ?_⟩
  · -- (2)
    intro n θ y hcfg
    rw [BaryEnv]
    exact le_csSup hBbdd ⟨n, θ, y, hcfg, rfl⟩
  · -- (3)
    intro A
    obtain ⟨Γ, hΓ⟩ : ∃ r : ℝ, r = sSup {w : ℝ | ∃ y' : F,
        w = f (toLp 2 (y', (ofLp z).2)) - ‖y'‖ ^ 2 / (2 * s)
          - inner ℝ A (y' - (ofLp z).1)} := ⟨_, rfl⟩
    rw [← hΓ]
    have hupper : BaryEnv f s z ≤ Γ + ‖(ofLp z).1‖ ^ 2 / (2 * s) := by
      rw [BaryEnv]
      refine csSup_le hBne ?_
      rintro w ⟨n, θ, y, hcfg, rfl⟩
      have h1 := hid n θ y hcfg
      have h2 := hweak A n θ y hcfg
      rw [← hΓ] at h2
      linarith
    linarith
