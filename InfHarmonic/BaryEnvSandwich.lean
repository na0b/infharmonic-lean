module

public import InfHarmonic.BaryEnv
public import InfHarmonic.HasJensenBound
public import InfHarmonic.SubquadraticGrowth

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (5.5): under the horizontal Jensen bound with constant `κ` and
subquadratic spatial growth, the barycentric envelope exceeds the function by at
least zero and at most `κ² s / 2`. -/
theorem BaryEnvSandwich (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hJ : HasJensenBound I f κ) (hgrow : SubquadraticGrowth I f) :
    ∀ (s : ℝ) (z : WithLp 2 (F × ℝ)), 0 < s → (ofLp z).2 ∈ I →
      f z ≤ BaryEnv f s z ∧ BaryEnv f s z ≤ f z + κ ^ 2 * s / 2 := by
  intro s z hs ht
  -- The statement carries `0 ≤ κ` (the paper's hypothesis), but the completed square of
  -- Step 2 holds for every real `κ`, so the proof never needs the sign. Reference it
  -- body-only so the signature stays byte-identical and no warning is emitted.
  have _unused_hκ : 0 ≤ κ := hκ
  -- Handshake 1: the `WithLp` round trip, definitional.
  have hrt : (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := rfl
  -- Handshake 2: squaring `BaryRadius`.
  have hradsq : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F),
      IsBaryConfig n θ y x → BaryRadius n θ y x ^ 2 = ∑ i, θ i * ‖y i - x‖ ^ 2 := by
    intro n θ y x hcfg
    obtain ⟨hpos, -, -⟩ := hcfg
    refine Real.sq_sqrt (Finset.sum_nonneg ?_)
    intro i _
    exact mul_nonneg (hpos i).le (sq_nonneg _)
  -- Handshake 4: the Finset sum step.
  have hsumstep : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F) (x : F) (g : F → ℝ),
      IsBaryConfig n θ y x → ∀ N c : ℝ, (∀ i, g (y i) ≤ N + ‖y i - x‖ ^ 2 / c) →
        ∑ i, θ i * g (y i) ≤ N + BaryRadius n θ y x ^ 2 / c := by
    intro n θ y x g hcfg N c hterm
    obtain ⟨hpos, hsum, hmean⟩ := hcfg
    have hstep : ∑ i, θ i * g (y i) ≤ ∑ i, θ i * (N + ‖y i - x‖ ^ 2 / c) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hpos i).le
    have h1 : ∑ i, θ i * (N + ‖y i - x‖ ^ 2 / c)
        = ∑ i, (θ i * N + θ i * ‖y i - x‖ ^ 2 / c) :=
      Finset.sum_congr rfl fun i _ => by ring
    have h2 : ∑ i, (θ i * N + θ i * ‖y i - x‖ ^ 2 / c)
        = (∑ i, θ i * N) + ∑ i, θ i * ‖y i - x‖ ^ 2 / c := Finset.sum_add_distrib
    have h3 : ∑ i, θ i * N = (∑ i, θ i) * N := (Finset.sum_mul _ _ _).symm
    have h4 : ∑ i, θ i * ‖y i - x‖ ^ 2 / c
        = (∑ i, θ i * ‖y i - x‖ ^ 2) / c := (Finset.sum_div _ _ _).symm
    have hr := hradsq n θ y x ⟨hpos, hsum, hmean⟩
    rw [h1, h2, h3, h4, hsum, one_mul, ← hr] at hstep
    exact hstep
  -- Handshake 5: the paper's completed square, pointwise in `r`.
  have hsq : ∀ r : ℝ, κ * r - r ^ 2 / (2 * s) ≤ κ ^ 2 * s / 2 := by
    intro r
    have h2s : (0:ℝ) < 2 * s := by linarith
    have hd : r ^ 2 / (2 * s) * (2 * s) = r ^ 2 := div_mul_cancel₀ _ (ne_of_gt h2s)
    nlinarith [sq_nonneg (r - κ * s), hd, hs]
  -- Step 1: the growth constant, at the compact time set `{t}` with `ε = 1/(16 s)`.
  obtain ⟨M₀, hM₀pos, hM₀⟩ := hgrow {(ofLp z).2} (Set.singleton_subset_iff.mpr ht)
    isCompact_singleton (1 / (16 * s)) (by positivity)
  -- Handshake 3: the near-field bound, where `[FiniteDimensional ℝ F]` is consumed
  -- through `[ProperSpace F]` in `isCompact_closedBall`.
  obtain ⟨N, hN0, hN⟩ : ∃ N : ℝ, 0 ≤ N ∧ ∀ y : F, ‖y‖ ≤ max M₀ (2 * ‖(ofLp z).1‖) →
      f (toLp 2 (y, (ofLp z).2)) ≤ N := by
    have hmap : Continuous fun y : F => (toLp 2 (y, (ofLp z).2) : WithLp 2 (F × ℝ)) := by
      fun_prop
    have hmem : ∀ y : F, (toLp 2 (y, (ofLp z).2) : WithLp 2 (F × ℝ))
        ∈ (fun w : WithLp 2 (F × ℝ) => (ofLp w).2) ⁻¹' I := by
      intro y; exact ht
    have hg : ContinuousOn (fun y : F => f (toLp 2 (y, (ofLp z).2)))
        (Metric.closedBall (0:F) (max M₀ (2 * ‖(ofLp z).1‖))) :=
      hcont.comp hmap.continuousOn (fun y _ => hmem y)
    obtain ⟨y₀, -, hy₀max⟩ :=
      (isCompact_closedBall (0:F) (max M₀ (2 * ‖(ofLp z).1‖))).exists_isMaxOn
        ⟨0, by simp⟩ hg
    refine ⟨max 0 (f (toLp 2 (y₀, (ofLp z).2))), le_max_left _ _, ?_⟩
    intro y hy
    have h := hy₀max (by simpa [Metric.mem_closedBall] using hy)
    exact h.trans (le_max_right _ _)
  -- the termwise bound: near field by `N`, far field by the growth bound
  have hterm : ∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), IsBaryConfig n θ y (ofLp z).1 →
      ∀ i, f (toLp 2 (y i, (ofLp z).2)) ≤ N + ‖y i - (ofLp z).1‖ ^ 2 / (4 * s) := by
    intro n θ y _ i
    rcases le_or_gt ‖y i‖ (max M₀ (2 * ‖(ofLp z).1‖)) with hle | hgt
    · have hnn : (0:ℝ) ≤ ‖y i - (ofLp z).1‖ ^ 2 / (4 * s) := by positivity
      linarith [hN (y i) hle]
    · have hM0le : M₀ ≤ ‖y i‖ := le_trans (le_max_left _ _) hgt.le
      have hxle : 2 * ‖(ofLp z).1‖ ≤ ‖y i‖ := le_trans (le_max_right _ _) hgt.le
      have hgrowi : |f (toLp 2 (y i, (ofLp z).2))| ≤ 1 / (16 * s) * ‖y i‖ ^ 2 := by
        have h := hM₀ (toLp 2 (y i, (ofLp z).2)) (by simpa using hM0le) (by simp)
        simpa using h
      have hgi : f (toLp 2 (y i, (ofLp z).2)) ≤ 1 / (16 * s) * ‖y i‖ ^ 2 :=
        (le_abs_self _).trans hgrowi
      -- clear the growth denominator
      have hgi' : f (toLp 2 (y i, (ofLp z).2)) * (16 * s) ≤ ‖y i‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hgi (by positivity : (0:ℝ) ≤ 16 * s)
        have hid : 1 / (16 * s) * ‖y i‖ ^ 2 * (16 * s) = ‖y i‖ ^ 2 := by field_simp
        rw [hid] at hmul
        exact hmul
      -- the far-field geometry: ‖y i‖ ≥ 2‖x‖ forces ‖y i‖² ≤ 4‖y i - x‖²
      have htri : ‖y i‖ - ‖(ofLp z).1‖ ≤ ‖y i - (ofLp z).1‖ := norm_sub_norm_le _ _
      have hAB : ‖y i‖ ^ 2 ≤ 4 * ‖y i - (ofLp z).1‖ ^ 2 := by
        nlinarith [htri, hxle, norm_nonneg (y i), norm_nonneg ((ofLp z).1)]
      have hfar : f (toLp 2 (y i, (ofLp z).2)) ≤ ‖y i - (ofLp z).1‖ ^ 2 / (4 * s) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * s)]
        nlinarith [hgi', hAB]
      linarith
  -- Step 1: the competitor set is nonempty (the single-point configuration) and bounded above
  have hone : IsBaryConfig 1 (fun _ => (1:ℝ)) (fun _ => (ofLp z).1) (ofLp z).1 := by
    refine ⟨fun i => one_pos, by simp, by simp⟩
  have hmem0 : f z ∈ {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
      IsBaryConfig n θ y (ofLp z).1 ∧
      w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)} := by
    refine ⟨1, fun _ => (1:ℝ), fun _ => (ofLp z).1, hone, ?_⟩
    have hr0 : BaryRadius 1 (fun _ => (1:ℝ)) (fun _ => (ofLp z).1) (ofLp z).1 = 0 := by
      simp [BaryRadius]
    rw [hr0]
    have hrt' : (toLp 2 (z.fst, z.snd) : WithLp 2 (F × ℝ)) = z := rfl
    simp [hrt']
  have hbdd : BddAbove {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
      IsBaryConfig n θ y (ofLp z).1 ∧
      w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)} := by
    refine ⟨N, ?_⟩
    rintro w ⟨n, θ, y, hcfg, rfl⟩
    have hss := hsumstep n θ y (ofLp z).1 (fun u => f (toLp 2 (u, (ofLp z).2))) hcfg N (4 * s)
      (hterm n θ y hcfg)
    have hcmp : BaryRadius n θ y (ofLp z).1 ^ 2 / (4 * s)
        ≤ BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s) := by
      gcongr
      norm_num
    linarith
  refine ⟨?_, ?_⟩
  · rw [BaryEnv]
    exact le_csSup hbdd hmem0
  · rw [BaryEnv]
    refine csSup_le ⟨f z, hmem0⟩ ?_
    rintro w ⟨n, θ, y, hcfg, rfl⟩
    have hjb := hJ (ofLp z).2 ht n θ y (ofLp z).1 hcfg
    rw [hrt] at hjb
    linarith [hsq (BaryRadius n θ y (ofLp z).1)]
