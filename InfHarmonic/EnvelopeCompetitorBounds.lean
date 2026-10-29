module

public import InfHarmonic.QuadEnvP
public import InfHarmonic.QuadEnvM
public import InfHarmonic.BaryEnv
public import InfHarmonic.SubquadraticGrowth

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- The three envelopes of a continuous function with subquadratic spatial
growth on compact time intervals are genuine suprema and infima: each
dominates every competitor value and is extremal among the bounds. This is the
boundedness side-condition the preamble's `sup`/`inf` convention attaches to
every use of `P_ℓ`, `M_ℓ` and `C_s`. -/
theorem EnvelopeCompetitorBounds (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hgrow : SubquadraticGrowth I f) :
    (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), 0 < l → (ofLp z).2 ∈ I → (ofLp z).2 + l ∈ I →
        (∀ y : F, f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)
            ≤ QuadEnvP f l z) ∧
        (∀ b : ℝ,
          (∀ y : F, f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l) ≤ b) →
            QuadEnvP f l z ≤ b)) ∧
    (∀ (l : ℝ) (z : WithLp 2 (F × ℝ)), 0 < l → (ofLp z).2 ∈ I → (ofLp z).2 - l ∈ I →
        (∀ y : F, QuadEnvM f l z
            ≤ f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) ∧
        (∀ b : ℝ,
          (∀ y : F, b ≤ f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)) →
            b ≤ QuadEnvM f l z)) ∧
    (∀ (s : ℝ) (z : WithLp 2 (F × ℝ)), 0 < s → (ofLp z).2 ∈ I →
        (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), IsBaryConfig n θ y (ofLp z).1 →
            (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
                - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)
              ≤ BaryEnv f s z) ∧
        (∀ b : ℝ,
          (∀ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F), IsBaryConfig n θ y (ofLp z).1 →
              (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
                  - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)
                ≤ b) →
            BaryEnv f s z ≤ b)) := by
  -- Step 1: `‖y‖²/2 - ‖x‖² ≤ ‖y - x‖²`, from `‖y‖² ≤ 2‖y-x‖² + 2‖x‖²`.
  have hquad : ∀ y x : F, ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by
    intro y x
    have h1 : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
      calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
    nlinarith [norm_nonneg (y - x), norm_nonneg x, sq_nonneg (‖y - x‖ - ‖x‖), norm_nonneg y]
  -- Step 2: subquadratic growth plus continuity bound `f` on a whole time slice:
  -- `|f(y, τ)| ≤ C + ε‖y‖²` for all `y`, with `C ≥ 0` from compactness of a ball.
  have hbound : ∀ τ ∈ I, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧
      ∀ y : F, |f (toLp 2 (y, τ))| ≤ C + ε * ‖y‖ ^ 2 := by
    intro τ hτ ε hε
    obtain ⟨M, hM, hfar⟩ := hgrow {τ} (by simpa using hτ) isCompact_singleton ε hε
    have hmaps : Set.MapsTo (fun y : F => (toLp 2 (y, τ) : WithLp 2 (F × ℝ)))
        (Metric.closedBall (0 : F) M) ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) := by
      intro y _; simpa using hτ
    have hcty : ContinuousOn (fun y : F => f (toLp 2 (y, τ))) (Metric.closedBall (0 : F) M) := by
      refine hcont.comp ?_ hmaps
      fun_prop
    obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : F) M).exists_bound_of_continuousOn hcty
    refine ⟨max C₀ 0, le_max_right _ _, fun y => ?_⟩
    rcases le_or_gt M ‖y‖ with h | h
    · have hf := hfar (toLp 2 (y, τ)) (by simpa using h) (by simp)
      simp only at hf
      have h0 : (0 : ℝ) ≤ max C₀ 0 := le_max_right _ _
      linarith
    · have hy : y ∈ Metric.closedBall (0 : F) M := by
        simp only [Metric.mem_closedBall, dist_zero_right]
        exact h.le
      have h1 : ‖f (toLp 2 (y, τ))‖ ≤ C₀ := hC₀ y hy
      have h2 : (0 : ℝ) ≤ ε * ‖y‖ ^ 2 := by positivity
      have h3 : C₀ ≤ max C₀ 0 := le_max_left _ _
      rw [Real.norm_eq_abs] at h1
      linarith
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1): the forward envelope is the least upper bound of `P`.
    intro l z hl _ htl
    have hl' : l ≠ 0 := ne_of_gt hl
    have h2l : (0 : ℝ) < 2 * l := by linarith
    obtain ⟨C, hC0, hCb⟩ := hbound ((ofLp z).2 + l) htl (1 / (4 * l)) (by positivity)
    have hbdd : BddAbove {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      refine ⟨C + ‖(ofLp z).1‖ ^ 2 / (2 * l), ?_⟩
      rintro w ⟨y, rfl⟩
      have h1 : f (toLp 2 (y, (ofLp z).2 + l)) ≤ C + 1 / (4 * l) * ‖y‖ ^ 2 :=
        (abs_le.mp (hCb y)).2
      have h2 : (‖y‖ ^ 2 / 2 - ‖(ofLp z).1‖ ^ 2) / (2 * l)
          ≤ ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
        div_le_div_of_nonneg_right (hquad y (ofLp z).1) h2l.le
      have h3 : (‖y‖ ^ 2 / 2 - ‖(ofLp z).1‖ ^ 2) / (2 * l)
          = 1 / (4 * l) * ‖y‖ ^ 2 - ‖(ofLp z).1‖ ^ 2 / (2 * l) := by
        field_simp
        ring
      rw [h3] at h2
      linarith
    have hne : ({w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}).Nonempty :=
      ⟨_, (ofLp z).1, rfl⟩
    simp only [QuadEnvP, if_neg hl']
    refine ⟨fun y => le_csSup hbdd ⟨y, rfl⟩, fun b hb => csSup_le hne ?_⟩
    rintro w ⟨y, rfl⟩
    exact hb y
  · -- Part (2): the backward envelope is the greatest lower bound of `M`, via `-f`.
    intro l z hl _ htl
    have hl' : l ≠ 0 := ne_of_gt hl
    have h2l : (0 : ℝ) < 2 * l := by linarith
    obtain ⟨C, hC0, hCb⟩ := hbound ((ofLp z).2 - l) htl (1 / (4 * l)) (by positivity)
    have hbdd : BddBelow {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      refine ⟨-C - ‖(ofLp z).1‖ ^ 2 / (2 * l), ?_⟩
      rintro w ⟨y, rfl⟩
      have h1 : -(C + 1 / (4 * l) * ‖y‖ ^ 2) ≤ f (toLp 2 (y, (ofLp z).2 - l)) :=
        (abs_le.mp (hCb y)).1
      have h2 : (‖y‖ ^ 2 / 2 - ‖(ofLp z).1‖ ^ 2) / (2 * l)
          ≤ ‖y - (ofLp z).1‖ ^ 2 / (2 * l) :=
        div_le_div_of_nonneg_right (hquad y (ofLp z).1) h2l.le
      have h3 : (‖y‖ ^ 2 / 2 - ‖(ofLp z).1‖ ^ 2) / (2 * l)
          = 1 / (4 * l) * ‖y‖ ^ 2 - ‖(ofLp z).1‖ ^ 2 / (2 * l) := by
        field_simp
        ring
      rw [h3] at h2
      linarith
    have hne : ({w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}).Nonempty :=
      ⟨_, (ofLp z).1, rfl⟩
    simp only [QuadEnvM, if_neg hl']
    refine ⟨fun y => csInf_le hbdd ⟨y, rfl⟩, fun b hb => le_csInf hne ?_⟩
    rintro w ⟨y, rfl⟩
    exact hb y
  · -- Part (3): the barycentric envelope is the least upper bound of `C`.
    intro s z hs ht
    have h4s : (0 : ℝ) < 4 * s := by linarith
    obtain ⟨C, hC0, hCb⟩ := hbound (ofLp z).2 ht (1 / (4 * s)) (by positivity)
    have hbdd : BddAbove {w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
        IsBaryConfig n θ y (ofLp z).1 ∧
        w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)} := by
      refine ⟨C + ‖(ofLp z).1‖ ^ 2 / (4 * s), ?_⟩
      rintro w ⟨n, θ, y, hc, rfl⟩
      obtain ⟨hpos, hsum, hmean⟩ := hc
      have hsq : (0 : ℝ) ≤ ∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hpos i).le (sq_nonneg _)
      have hrho : BaryRadius n θ y (ofLp z).1 ^ 2
          = ∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2 := by
        simp only [BaryRadius]
        exact Real.sq_sqrt hsq
      -- the variance identity `∑ θᵢ‖yᵢ‖² = ρ² + ‖x‖²`
      have hinner : (∑ i, θ i * inner ℝ (y i) (ofLp z).1) = ‖(ofLp z).1‖ ^ 2 := by
        have h1 : (∑ i, θ i * inner ℝ (y i) (ofLp z).1)
            = inner ℝ (∑ i, θ i • y i) (ofLp z).1 := by
          rw [sum_inner]
          exact Finset.sum_congr rfl fun i _ =>
            (real_inner_smul_left (y i) (ofLp z).1 (θ i)).symm
        rw [h1, hmean, real_inner_self_eq_norm_sq]
      have hvar : (∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2)
          = (∑ i, θ i * ‖y i‖ ^ 2) - ‖(ofLp z).1‖ ^ 2 := by
        have hterm : ∀ i, θ i * ‖y i - (ofLp z).1‖ ^ 2
            = θ i * ‖y i‖ ^ 2 - 2 * (θ i * inner ℝ (y i) (ofLp z).1)
              + θ i * ‖(ofLp z).1‖ ^ 2 := by
          intro i; rw [norm_sub_sq_real]; ring
        rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hinner, hsum, one_mul]
        ring
      -- the weighted values are bounded by the slice bound
      have hsumf : (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
          ≤ C + 1 / (4 * s) * (∑ i, θ i * ‖y i‖ ^ 2) := by
        have hle : (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            ≤ ∑ i, θ i * (C + 1 / (4 * s) * ‖y i‖ ^ 2) :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (abs_le.mp (hCb (y i))).2 (hpos i).le
        have heq : (∑ i, θ i * (C + 1 / (4 * s) * ‖y i‖ ^ 2))
            = C + 1 / (4 * s) * (∑ i, θ i * ‖y i‖ ^ 2) := by
          rw [show (∑ i, θ i * (C + 1 / (4 * s) * ‖y i‖ ^ 2))
              = (∑ i, θ i) * C + 1 / (4 * s) * ∑ i, θ i * ‖y i‖ ^ 2 from by
            rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun i _ => by ring, hsum, one_mul]
        linarith [hle, heq.le, heq.ge]
      have hS : (∑ i, θ i * ‖y i‖ ^ 2)
          = (∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2) + ‖(ofLp z).1‖ ^ 2 := by linarith
      rw [hS] at hsumf
      rw [hrho]
      have harith : 1 / (4 * s) * ((∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2) + ‖(ofLp z).1‖ ^ 2)
          - (∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2) / (2 * s)
          = (‖(ofLp z).1‖ ^ 2 - (∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2)) / (4 * s) := by
        field_simp
        ring
      have hmono : (‖(ofLp z).1‖ ^ 2 - (∑ i, θ i * ‖y i - (ofLp z).1‖ ^ 2)) / (4 * s)
          ≤ ‖(ofLp z).1‖ ^ 2 / (4 * s) :=
        div_le_div_of_nonneg_right (by linarith) h4s.le
      linarith
    have hne : ({w : ℝ | ∃ (n : ℕ) (θ : Fin n → ℝ) (y : Fin n → F),
        IsBaryConfig n θ y (ofLp z).1 ∧
        w = (∑ i, θ i * f (toLp 2 (y i, (ofLp z).2)))
            - BaryRadius n θ y (ofLp z).1 ^ 2 / (2 * s)}).Nonempty :=
      ⟨_, 1, fun _ => 1, fun _ => (ofLp z).1,
        ⟨fun i => one_pos, by simp, by simp⟩, rfl⟩
    simp only [BaryEnv]
    refine ⟨fun n θ y hc => le_csSup hbdd ⟨n, θ, y, hc, rfl⟩, fun b hb => csSup_le hne ?_⟩
    rintro w ⟨n, θ, y, hc, rfl⟩
    exact hb n θ y hc
