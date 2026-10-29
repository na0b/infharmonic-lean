import InfHarmonic.IsStepPair
import InfHarmonic.DPLogVelocity
import InfHarmonic.UniformSubquadratic
import InfHarmonic.EnvelopeCompetitorBounds
set_option maxHeartbeats 400000
open Set Filter Topology WithLp MeasureTheory

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 3a of Proposition 6.7: the pathwise bounds along a stopped contact
walk.  These are statements about each trajectory separately: no measure and no
filtration enter.  The spatial coordinate stays in the ball of radius `R + 1`,
the time coordinate stays in `[4 eps, 8]` so its logarithm is bounded, the
reference velocity `Q0` is bounded by a constant `LamQ` depending only on the
data, and while the walk is live the two error increments have squared sum at
most a constant `LamE`. -/
theorem WalkPathwiseBounds (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ))
    (hsand : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧ ContactEnv v κ z ≤ v z)
    (C₂ : ℝ) (hC₂0 : 0 < C₂)
    (hC₂b : ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))) → HasJensenBound Set.univ v κ →
      ∀ K : ℝ, 2 ≤ K → ∀ (x : F) (t ε : ℝ),
        ‖x‖ ≤ K → |t| ≤ K → 0 < ε → ε ≤ 1 → ε < t →
        ∀ Q₀ : F,
          HasGradientAt (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', t)))
            Q₀ x →
          ‖Q₀‖ ≤ C₂ * ((1 + Real.log K) + |Real.log t|))
    (R : ℝ) (hR10 : (10:ℝ) ≤ R)
    (ε : ℝ) (hε0 : 0 < ε) (hεle : ε ≤ 1 / 8) (q : ℕ) (hεq : ε * (q : ℝ) = 8)
    {Ω : Type*} (ξ : ℕ → Ω → ℝ) (z zp zm : ℕ → Ω → WithLp 2 (F × ℝ))
    (Q₀ : ℕ → Ω → F) (τ : Ω → ℕ) (S : ℕ → Ω → ℤ)
    (hrec : ∀ n ω, z (n + 1) ω
      = if n < τ ω then (if ξ n ω = 1 then zp n ω else zm n ω) else z n ω)
    (hpair : ∀ n ω, n < τ ω → IsStepPair v κ ε (z n ω) (zp n ω) (zm n ω))
    (hgrad : ∀ n ω, HasGradientAt
      (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp (z n ω)).2)))
      (Q₀ n ω) (ofLp (z n ω)).1)
    (hxbnd : ∀ n ω, n ≤ τ ω → ‖(ofLp (z n ω)).1‖ ≤ R + 1)
    (hlat : ∀ n ω, (ofLp (z n ω)).2 = ε * (S n ω : ℝ))
    (hSrange : ∀ n ω, 4 ≤ S n ω ∧ S n ω ≤ (q : ℤ)) :
    ∃ ΛQ ΛE : ℝ, (0:ℝ) ≤ ΛE ∧
      (∀ (n : ℕ) (ω : Ω), ‖(ofLp (z n ω)).1‖ ≤ R + 1) ∧
      (∀ (n : ℕ) (ω : Ω), 4 * ε ≤ (ofLp (z n ω)).2 ∧ (ofLp (z n ω)).2 ≤ 8) ∧
      (∀ (n : ℕ) (ω : Ω),
        |Real.log ((ofLp (z n ω)).2)| ≤ |Real.log (4 * ε)| + Real.log 8) ∧
      (∀ (n : ℕ) (ω : Ω), ‖Q₀ n ω‖ ≤ ΛQ) ∧
      (∀ (n : ℕ) (ω : Ω), n < τ ω →
        ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
          + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2 ≤ ΛE) := by
  have hzfroz : ∀ (n : ℕ) (ω : Ω), τ ω ≤ n → z n ω = z (τ ω) ω := by
    intro n ω hn
    induction n with
    | zero => rw [Nat.le_zero.mp hn]
    | succ n ih =>
        rcases Nat.lt_or_ge (τ ω) (n + 1) with h | h
        · have h2 : τ ω ≤ n := by omega
          rw [hrec n ω, if_neg (by omega)]
          exact ih h2
        · rw [show τ ω = n + 1 by omega]
  have hxall : ∀ (n : ℕ) (ω : Ω), ‖(ofLp (z n ω)).1‖ ≤ R + 1 := by
    intro n ω
    rcases Nat.lt_or_ge n (τ ω) with h | h
    · exact hxbnd n ω (le_of_lt h)
    · rw [hzfroz n ω h]; exact hxbnd (τ ω) ω le_rfl
  have htall : ∀ (n : ℕ) (ω : Ω), 4 * ε ≤ (ofLp (z n ω)).2 ∧ (ofLp (z n ω)).2 ≤ 8 := by
    intro n ω
    obtain ⟨h1, h2⟩ := hSrange n ω
    rw [hlat n ω]
    constructor
    · have e1 : (4:ℝ) ≤ (S n ω : ℝ) := by
        have : (4:ℤ) ≤ S n ω := h1
        exact_mod_cast this
      nlinarith only [e1, hε0]
    · have e2 : (S n ω : ℝ) ≤ (q:ℝ) := by exact_mod_cast h2
      nlinarith only [e2, hε0, hεq]
  -- the uniform bound on `|log t|` along the walk
  have hlogt : ∀ (n : ℕ) (ω : Ω),
      |Real.log ((ofLp (z n ω)).2)| ≤ |Real.log (4 * ε)| + Real.log 8 := by
    intro n ω
    obtain ⟨h1, h2⟩ := htall n ω
    have h4ε : (0:ℝ) < 4 * ε := by linarith only [hε0]
    have hl8 : (0:ℝ) ≤ Real.log 8 := Real.log_nonneg (by norm_num)
    have h4le : 4 * ε ≤ 1 := by linarith only [hεle]
    have hlog4 : Real.log (4 * ε) ≤ 0 := Real.log_nonpos h4ε.le h4le
    rcases le_or_gt ((ofLp (z n ω)).2) 1 with hc | hc
    · have e1 : Real.log ((ofLp (z n ω)).2) ≤ 0 :=
        Real.log_nonpos (by linarith only [h1, h4ε]) hc
      have e2 : Real.log (4 * ε) ≤ Real.log ((ofLp (z n ω)).2) :=
        Real.log_le_log h4ε h1
      rw [abs_of_nonpos e1, abs_of_nonpos hlog4]
      linarith only [e2, hl8]
    · have e1 : (0:ℝ) ≤ Real.log ((ofLp (z n ω)).2) :=
        Real.log_nonneg (le_of_lt hc)
      have e2 : Real.log ((ofLp (z n ω)).2) ≤ Real.log 8 :=
        Real.log_le_log (by linarith only [hc]) h2
      rw [abs_of_nonneg e1]
      linarith only [e2, abs_nonneg (Real.log (4 * ε))]
  -- (A1) the reference velocities are bounded
  obtain ⟨ΛQ, hΛQd⟩ : ∃ r : ℝ, r = C₂ * (1 + Real.log (R + 10)
      + (|Real.log (4 * ε)| + Real.log 8)) := ⟨_, rfl⟩
  have hQbd : ∀ (n : ℕ) (ω : Ω), ‖Q₀ n ω‖ ≤ ΛQ := by
    intro n ω
    obtain ⟨h1, h2⟩ := htall n ω
    have hR2 : (2:ℝ) ≤ R + 10 := by linarith only [hR10]
    have hxK : ‖(ofLp (z n ω)).1‖ ≤ R + 10 := by
      have := hxall n ω; linarith only [this, hR10]
    have htK : |(ofLp (z n ω)).2| ≤ R + 10 := by
      rw [abs_of_nonneg (by linarith only [h1, hε0])]
      linarith only [h2, hR10]
    have hεt : ε < (ofLp (z n ω)).2 := by linarith only [h1, hε0]
    have h3 := hC₂b v hv hcent hJ (R + 10) hR2 (ofLp (z n ω)).1 (ofLp (z n ω)).2 ε
      hxK htK hε0 (by linarith only [hεle]) hεt (Q₀ n ω) (hgrad n ω)
    have h4 := hlogt n ω
    rw [hΛQd]
    have hC2nn : (0:ℝ) ≤ C₂ := hC₂0.le
    nlinarith only [h3, h4, hC2nn]
  -- (A2) the growth bound for `v` on a compact slab, and for `W`
  have hvcont : ContinuousOn v (Set.univ : Set (WithLp 2 (F × ℝ))) := hv.1.1.2.1
  have hvgrowth : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : F) (t : ℝ),
      t ∈ Set.Icc (-1 : ℝ) 9 → |v (toLp 2 (y, t))| ≤ C + δ * ‖y‖ ^ 2 := by
    intro δ hδ
    obtain ⟨M, hM0, hMb⟩ := UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0:F), (1:ℝ)))
      (Or.inr rfl) (Set.Icc (-1:ℝ) 9) isCompact_Icc δ hδ
    have hKc : IsCompact ((fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
        (Metric.closedBall (0:F) M ×ˢ Set.Icc (-1:ℝ) 9)) := by
      refine IsCompact.image ((isCompact_closedBall (0:F) M).prod isCompact_Icc) ?_
      exact WithLp.prod_continuous_toLp 2 F ℝ
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn (hvcont.mono (Set.subset_univ _))
    refine ⟨|C|, abs_nonneg C, fun y t ht => ?_⟩
    rcases le_or_gt M ‖y‖ with hc | hc
    · have h1 := hMb v hv hcent (toLp 2 (y, t)) (by simpa using hc) (by simpa using ht)
      linarith only [h1, abs_nonneg C]
    · have hmem : (toLp 2 (y, t) : WithLp 2 (F × ℝ))
          ∈ (fun p : F × ℝ => (toLp 2 p : WithLp 2 (F × ℝ))) ''
            (Metric.closedBall (0:F) M ×ˢ Set.Icc (-1:ℝ) 9) :=
        ⟨(y, t), ⟨by simpa using le_of_lt hc, ht⟩, rfl⟩
      have h1 := hC _ hmem
      rw [Real.norm_eq_abs] at h1
      have h2 : |C| ≥ C := le_abs_self C
      have h3 : (0:ℝ) ≤ δ * ‖y‖ ^ 2 := by positivity
      linarith only [h1, h2, h3]
  have hWbd : ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : F) (t : ℝ),
      0 < t → t ≤ 9 → |ContactEnv v κ (toLp 2 (y, t))| ≤ C + δ * ‖y‖ ^ 2 := by
    intro δ hδ
    obtain ⟨C, hC0, hCb⟩ := hvgrowth δ hδ
    refine ⟨C + κ ^ 2 * 9 / 2, by positivity, fun y t ht0 ht9 => ?_⟩
    have h1 := hCb y t ⟨by linarith only [ht0], ht9⟩
    have h2 := hsand (toLp 2 (y, t)) (by simpa using ht0)
    have h3 := abs_le.mp h1
    rw [abs_le]
    have hκ9 : (0:ℝ) ≤ κ ^ 2 * (9 - t) / 2 := by
      have : (0:ℝ) ≤ κ ^ 2 := sq_nonneg κ
      have h9 : (0:ℝ) ≤ 9 - t := by linarith only [ht9]
      positivity
    have hκ0 : (0:ℝ) ≤ κ ^ 2 * 9 / 2 := by positivity
    constructor
    · linarith only [h2.1, h3.1, hκ9, hκ0]
    · linarith only [h2.2, h3.2, hκ9, hκ0]
  -- the two envelope competitor bounds, and the optimizer bound
  have hIuniv : ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc δ hδ
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0:F), (1:ℝ))) (Or.inr rfl) J hJc δ hδ
    exact ⟨M, hM0, fun ζ hζ hζJ => hMb v hv hcent ζ hζ hζJ⟩
  obtain ⟨-, hMcomp, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) v
    (by rw [hIuniv]; exact hvcont) hvgrow
  obtain ⟨hPcomp, -, -⟩ := EnvelopeCompetitorBounds (Set.Ioi (0:ℝ)) (ContactEnv v κ)
    hWcont hWgrow
  obtain ⟨Cw, hCw0, hCwb⟩ := hWbd (1 / (32 * ε)) (by positivity)
  obtain ⟨Cv, hCv0, hCvb⟩ := hvgrowth (1 / (32 * ε)) (by positivity)
  obtain ⟨BY, hBYd⟩ : ∃ r : ℝ, r = 11 * ε * (Cw + Cv) + (R + 1) ^ 2 := ⟨_, rfl⟩
  have hBY0 : (0:ℝ) ≤ BY := by
    rw [hBYd]
    have : (0:ℝ) ≤ 11 * ε * (Cw + Cv) := by positivity
    positivity
  have hεne : ε ≠ 0 := ne_of_gt hε0
  have hG : 4 * ε * (1 / (32 * ε)) = 1 / 8 := by
    field_simp
    ring
  -- the generic absorption step
  have habs : ∀ a X C : ℝ, 0 ≤ a → 0 ≤ X → 0 ≤ C →
      a ^ 2 / (2 * (2 * ε)) ≤ 2 * C + (1 / (32 * ε)) * ((2 * a ^ 2 + 2 * X ^ 2) + X ^ 2) →
      X ≤ R + 1 → a ^ 2 ≤ 11 * ε * C + (R + 1) ^ 2 := by
    intro a X C ha hX hC hmain hXR
    have h4ε : (0:ℝ) < 4 * ε := by linarith only [hε0]
    have e1 : a ^ 2 = (a ^ 2 / (2 * (2 * ε))) * (4 * ε) := by
      field_simp
      ring
    have e2 : a ^ 2 ≤ (2 * C + (1 / (32 * ε)) * ((2 * a ^ 2 + 2 * X ^ 2) + X ^ 2)) * (4 * ε) :=
      calc a ^ 2 = (a ^ 2 / (2 * (2 * ε))) * (4 * ε) := e1
        _ ≤ (2 * C + (1 / (32 * ε)) * ((2 * a ^ 2 + 2 * X ^ 2) + X ^ 2)) * (4 * ε) :=
            mul_le_mul_of_nonneg_right hmain h4ε.le
    have e3 : (2 * C + (1 / (32 * ε)) * ((2 * a ^ 2 + 2 * X ^ 2) + X ^ 2)) * (4 * ε)
        = 8 * ε * C + (4 * ε * (1 / (32 * ε))) * ((2 * a ^ 2 + 2 * X ^ 2) + X ^ 2) := by
      ring
    rw [e3, hG] at e2
    have e4 : X ^ 2 ≤ (R + 1) ^ 2 := by nlinarith only [hX, hXR]
    nlinarith only [e2, e4, hε0, hC]
  have hYbd : ∀ (n : ℕ) (ω : Ω), n < τ ω → ∀ Yp Ym : F,
      QuadEnvP (ContactEnv v κ) (2 * ε) (z n ω)
          = ContactEnv v κ (toLp 2 (Yp, (ofLp (z n ω)).2 + 2 * ε))
            - ‖Yp - (ofLp (z n ω)).1‖ ^ 2 / (2 * (2 * ε)) →
      QuadEnvM v (2 * ε) (z n ω)
          = v (toLp 2 (Ym, (ofLp (z n ω)).2 - 2 * ε))
            + ‖Ym - (ofLp (z n ω)).1‖ ^ 2 / (2 * (2 * ε)) →
      ‖Yp - (ofLp (z n ω)).1‖ ^ 2 ≤ BY ∧ ‖Ym - (ofLp (z n ω)).1‖ ^ 2 ≤ BY := by
    intro n ω hn Yp Ym hYp hYm
    obtain ⟨ht1, ht2⟩ := htall n ω
    have ht0 : (0:ℝ) < (ofLp (z n ω)).2 := by linarith only [ht1, hε0]
    have hε2 : (0:ℝ) < 2 * ε := by linarith only [hε0]
    have heps8 : 2 * ε ≤ 1 / 4 := by linarith only [hεle]
    have hXR := hxall n ω
    have hXnn : (0:ℝ) ≤ ‖(ofLp (z n ω)).1‖ := norm_nonneg _
    -- the forward envelope
    have hPc := (hPcomp (2 * ε) (z n ω) hε2 ht0 (by
      simp only [Set.mem_Ioi]; linarith only [ht0, hε2])).1 (ofLp (z n ω)).1
    rw [hYp] at hPc
    have hWp := hCwb Yp ((ofLp (z n ω)).2 + 2 * ε) (by linarith only [ht0, hε2])
      (by linarith only [ht2, heps8])
    have hWx := hCwb (ofLp (z n ω)).1 ((ofLp (z n ω)).2 + 2 * ε)
      (by linarith only [ht0, hε2]) (by linarith only [ht2, heps8])
    have hnp : ‖Yp‖ ^ 2 ≤ 2 * ‖Yp - (ofLp (z n ω)).1‖ ^ 2 + 2 * ‖(ofLp (z n ω)).1‖ ^ 2 := by
      have h1 : ‖Yp‖ ≤ ‖Yp - (ofLp (z n ω)).1‖ + ‖(ofLp (z n ω)).1‖ := by
        calc ‖Yp‖ = ‖(Yp - (ofLp (z n ω)).1) + (ofLp (z n ω)).1‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have h2 := mul_self_le_mul_self (norm_nonneg Yp) h1
      nlinarith only [h2, sq_nonneg (‖Yp - (ofLp (z n ω)).1‖ - ‖(ofLp (z n ω)).1‖)]
    have hPabs := abs_le.mp hWp
    have hXabs := abs_le.mp hWx
    have hmainP : ‖Yp - (ofLp (z n ω)).1‖ ^ 2 / (2 * (2 * ε))
        ≤ 2 * Cw + (1 / (32 * ε)) * ((2 * ‖Yp - (ofLp (z n ω)).1‖ ^ 2
          + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) + ‖(ofLp (z n ω)).1‖ ^ 2) := by
      have hgnn : (0:ℝ) < 1 / (32 * ε) := by positivity
      have h5 : (1 / (32 * ε)) * ‖Yp‖ ^ 2
          ≤ (1 / (32 * ε)) * (2 * ‖Yp - (ofLp (z n ω)).1‖ ^ 2
            + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hnp hgnn.le
      have h6 : ‖(ofLp (z n ω)).1 - (ofLp (z n ω)).1‖ ^ 2 / (2 * (2 * ε)) = 0 := by
        simp
      rw [h6] at hPc
      have h7 : (1 / (32 * ε)) * ((2 * ‖Yp - (ofLp (z n ω)).1‖ ^ 2
          + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) + ‖(ofLp (z n ω)).1‖ ^ 2)
          = (1 / (32 * ε)) * (2 * ‖Yp - (ofLp (z n ω)).1‖ ^ 2
            + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) + (1 / (32 * ε)) * ‖(ofLp (z n ω)).1‖ ^ 2 := by
        ring
      rw [h7]
      linarith only [hPc, hPabs.1, hPabs.2, hXabs.1, hXabs.2, h5]
    -- the backward envelope
    have hMc := (hMcomp (2 * ε) (z n ω) hε2 (Set.mem_univ _) (Set.mem_univ _)).1
      (ofLp (z n ω)).1
    rw [hYm] at hMc
    have hVm := hCvb Ym ((ofLp (z n ω)).2 - 2 * ε)
      ⟨by linarith only [ht1, hε0, hε2], by linarith only [ht2, hε2]⟩
    have hVx := hCvb (ofLp (z n ω)).1 ((ofLp (z n ω)).2 - 2 * ε)
      ⟨by linarith only [ht1, hε0, hε2], by linarith only [ht2, hε2]⟩
    have hnm : ‖Ym‖ ^ 2 ≤ 2 * ‖Ym - (ofLp (z n ω)).1‖ ^ 2 + 2 * ‖(ofLp (z n ω)).1‖ ^ 2 := by
      have h1 : ‖Ym‖ ≤ ‖Ym - (ofLp (z n ω)).1‖ + ‖(ofLp (z n ω)).1‖ := by
        calc ‖Ym‖ = ‖(Ym - (ofLp (z n ω)).1) + (ofLp (z n ω)).1‖ := by rw [sub_add_cancel]
          _ ≤ _ := norm_add_le _ _
      have h2 := mul_self_le_mul_self (norm_nonneg Ym) h1
      nlinarith only [h2, sq_nonneg (‖Ym - (ofLp (z n ω)).1‖ - ‖(ofLp (z n ω)).1‖)]
    have hMabs := abs_le.mp hVm
    have hMxabs := abs_le.mp hVx
    have hmainM : ‖Ym - (ofLp (z n ω)).1‖ ^ 2 / (2 * (2 * ε))
        ≤ 2 * Cv + (1 / (32 * ε)) * ((2 * ‖Ym - (ofLp (z n ω)).1‖ ^ 2
          + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) + ‖(ofLp (z n ω)).1‖ ^ 2) := by
      have hgnn : (0:ℝ) < 1 / (32 * ε) := by positivity
      have h5 : (1 / (32 * ε)) * ‖Ym‖ ^ 2
          ≤ (1 / (32 * ε)) * (2 * ‖Ym - (ofLp (z n ω)).1‖ ^ 2
            + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) := by
        exact mul_le_mul_of_nonneg_left hnm hgnn.le
      have h6 : ‖(ofLp (z n ω)).1 - (ofLp (z n ω)).1‖ ^ 2 / (2 * (2 * ε)) = 0 := by
        simp
      rw [h6] at hMc
      have h7 : (1 / (32 * ε)) * ((2 * ‖Ym - (ofLp (z n ω)).1‖ ^ 2
          + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) + ‖(ofLp (z n ω)).1‖ ^ 2)
          = (1 / (32 * ε)) * (2 * ‖Ym - (ofLp (z n ω)).1‖ ^ 2
            + 2 * ‖(ofLp (z n ω)).1‖ ^ 2) + (1 / (32 * ε)) * ‖(ofLp (z n ω)).1‖ ^ 2 := by
        ring
      rw [h7]
      linarith only [hMc, hMabs.1, hMabs.2, hMxabs.1, hMxabs.2, h5]
    have hp := habs ‖Yp - (ofLp (z n ω)).1‖ ‖(ofLp (z n ω)).1‖ Cw (norm_nonneg _) hXnn hCw0
      hmainP hXR
    have hm := habs ‖Ym - (ofLp (z n ω)).1‖ ‖(ofLp (z n ω)).1‖ Cv (norm_nonneg _) hXnn hCv0
      hmainM hXR
    rw [hBYd]
    constructor
    · nlinarith only [hp, hε0, hCv0]
    · nlinarith only [hm, hε0, hCw0]
  -- (A2) the error increments are bounded pathwise while the walk is live
  obtain ⟨ΛE, hΛEd⟩ : ∃ r : ℝ, r = 2 * (Real.sqrt BY * (2 * ε)⁻¹ + ΛQ) ^ 2 := ⟨_, rfl⟩
  have hΛE0 : (0:ℝ) ≤ ΛE := by rw [hΛEd]; positivity
  have hstepx : ∀ (n : ℕ) (ω : Ω), n < τ ω →
      ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ≤ Real.sqrt BY * (2 * ε)⁻¹ + ΛQ ∧
      ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖
        ≤ Real.sqrt BY * (2 * ε)⁻¹ + ΛQ := by
    intro n ω hn
    obtain ⟨Yp, Ym, hYp, hYm, hzpd, hzmd⟩ := hpair n ω hn
    obtain ⟨hbp, hbm⟩ := hYbd n ω hn Yp Ym hYp hYm
    have h2ε : (0:ℝ) < 2 * ε := by linarith only [hε0]
    have hvp : ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1)
        = (2 * ε)⁻¹ • (Yp - (ofLp (z n ω)).1) := by
      rw [show (ofLp (zp n ω)).1 = (2:ℝ)⁻¹ • ((ofLp (z n ω)).1 + Yp) by rw [hzpd]]
      module
    have hvm : ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1)
        = (2 * ε)⁻¹ • ((ofLp (z n ω)).1 - Ym) := by
      rw [show (ofLp (zm n ω)).1 = (2:ℝ)⁻¹ • ((ofLp (z n ω)).1 + Ym) by rw [hzmd]]
      module
    have hsp : ‖Yp - (ofLp (z n ω)).1‖ ≤ Real.sqrt BY := by
      have h := Real.sqrt_le_sqrt hbp
      rwa [Real.sqrt_sq (norm_nonneg _)] at h
    have hsm : ‖(ofLp (z n ω)).1 - Ym‖ ≤ Real.sqrt BY := by
      have h := Real.sqrt_le_sqrt hbm
      rw [Real.sqrt_sq (norm_nonneg _)] at h
      rwa [norm_sub_rev]
    have hinv : (0:ℝ) ≤ (2 * ε)⁻¹ := by positivity
    constructor
    · calc ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖
          ≤ ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1)‖ + ‖Q₀ n ω‖ := norm_sub_le _ _
        _ = ‖Yp - (ofLp (z n ω)).1‖ * (2 * ε)⁻¹ + ‖Q₀ n ω‖ := by
            rw [hvp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]; ring
        _ ≤ Real.sqrt BY * (2 * ε)⁻¹ + ΛQ := by
            have := hQbd n ω
            have h2 := mul_le_mul_of_nonneg_right hsp hinv
            linarith only [this, h2]
    · calc ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖
          ≤ ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1)‖ + ‖Q₀ n ω‖ := norm_sub_le _ _
        _ = ‖(ofLp (z n ω)).1 - Ym‖ * (2 * ε)⁻¹ + ‖Q₀ n ω‖ := by
            rw [hvm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hinv]; ring
        _ ≤ Real.sqrt BY * (2 * ε)⁻¹ + ΛQ := by
            have := hQbd n ω
            have h2 := mul_le_mul_of_nonneg_right hsm hinv
            linarith only [this, h2]
  have hEbd : ∀ (n : ℕ) (ω : Ω), n < τ ω →
      ‖ε⁻¹ • ((ofLp (zp n ω)).1 - (ofLp (z n ω)).1) - Q₀ n ω‖ ^ 2
        + ‖ε⁻¹ • ((ofLp (z n ω)).1 - (ofLp (zm n ω)).1) - Q₀ n ω‖ ^ 2 ≤ ΛE := by
    intro n ω hn
    obtain ⟨h1, h2⟩ := hstepx n ω hn
    have e1 := mul_self_le_mul_self (norm_nonneg _) h1
    have e2 := mul_self_le_mul_self (norm_nonneg _) h2
    rw [hΛEd]
    nlinarith only [e1, e2]
  exact ⟨ΛQ, ΛE, hΛE0, hxall, htall, hlogt, hQbd, hEbd⟩
