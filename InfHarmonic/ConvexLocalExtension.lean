module

public import InfHarmonic.ConvexSubgradientExists

@[expose] public section
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A convex function on an open convex set agrees, on any ball well inside that
set, with a function that is convex on all of `E`. -/
theorem ConvexLocalExtension (Ω : Set E) (hΩo : IsOpen Ω) (ψ : E → ℝ)
    (hψ : ConvexOn ℝ Ω ψ) (x₀ : E) (r : ℝ) (hr : 0 < r)
    (hball : closedBall x₀ (2 * r) ⊆ Ω) :
    ∃ ψ' : E → ℝ, ConvexOn ℝ Set.univ ψ' ∧ ∀ x ∈ ball x₀ r, ψ' x = ψ x := by
  -- Step 1: the inner ball sits inside the compact outer ball, which sits in `Ω`
  have hballsub : ball x₀ r ⊆ closedBall x₀ (2 * r) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hcont : ContinuousOn ψ Ω := hψ.continuousOn hΩo
  obtain ⟨M, hM0, hMbd⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall x₀ (2 * r), |ψ x| ≤ M := by
    obtain ⟨z, -, hzmax⟩ := IsCompact.exists_isMaxOn (f := fun x => |ψ x|)
      (isCompact_closedBall x₀ (2 * r)) ⟨x₀, mem_closedBall_self (by linarith)⟩
      ((hcont.mono hball).abs)
    exact ⟨|ψ z|, abs_nonneg _, fun x hx => hzmax hx⟩
  -- one subgradient for each centre of the inner ball: a dependent choice
  have hqex : ∀ w ∈ ball x₀ r, ∃ p : E, ∀ x ∈ Ω, ψ w + inner ℝ p (x - w) ≤ ψ x :=
    fun w hw => ConvexSubgradientExists Ω hΩo ψ hψ w (hball (hballsub hw))
  choose! q hq using hqex
  -- the subgradients are bounded, tested at the fixed-length step `w + (r/‖q w‖) • q w`
  have hqbd : ∀ w ∈ ball x₀ r, ‖q w‖ ≤ 2 * M / r := by
    intro w hw
    rcases eq_or_lt_of_le (norm_nonneg (q w)) with h0 | hpos
    · rw [← h0]; exact div_nonneg (by linarith) hr.le
    · have hcpos : 0 < r / ‖q w‖ := by positivity
      have hnorm : ‖(r / ‖q w‖) • q w‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hcpos]
        field_simp
      have hmem : w + (r / ‖q w‖) • q w ∈ closedBall x₀ (2 * r) := by
        have hrw : w + (r / ‖q w‖) • q w - x₀ = (w - x₀) + (r / ‖q w‖) • q w := by abel
        have h1 : ‖w + (r / ‖q w‖) • q w - x₀‖ ≤ ‖w - x₀‖ + r := by
          rw [hrw]
          refine le_trans (norm_add_le _ _) ?_
          rw [hnorm]
        have h2 : ‖w - x₀‖ < r := by simpa [mem_ball, dist_eq_norm] using hw
        simp only [mem_closedBall, dist_eq_norm]
        linarith
      have hsg := hq w hw (w + (r / ‖q w‖) • q w) (hball hmem)
      have hinn : inner ℝ (q w) (w + (r / ‖q w‖) • q w - w) = r * ‖q w‖ := by
        rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      rw [hinn] at hsg
      have hub := (abs_le.1 (hMbd (w + (r / ‖q w‖) • q w) hmem)).2
      have hlb := (abs_le.1 (hMbd w (hballsub hw))).1
      rw [le_div_iff₀ hr]
      linarith
  -- Step 2: for each `x` the competitor set is nonempty and bounded above
  have hne : ∀ x : E, ((fun w => ψ w + inner ℝ (q w) (x - w)) '' ball x₀ r).Nonempty :=
    fun x => Set.Nonempty.image _ ⟨x₀, mem_ball_self hr⟩
  have hbdd : ∀ x : E,
      BddAbove ((fun w => ψ w + inner ℝ (q w) (x - w)) '' ball x₀ r) := by
    intro x
    refine ⟨M + (2 * M / r) * (‖x - x₀‖ + r), ?_⟩
    rintro y ⟨w, hw, rfl⟩
    have h1 : ψ w ≤ M := (abs_le.1 (hMbd w (hballsub hw))).2
    have h2 : inner ℝ (q w) (x - w) ≤ ‖q w‖ * ‖x - w‖ := real_inner_le_norm _ _
    have h3 : ‖x - w‖ ≤ ‖x - x₀‖ + r := by
      have hrw : x - w = (x - x₀) + (x₀ - w) := by abel
      have h4 : ‖x₀ - w‖ < r := by
        rw [norm_sub_rev]; simpa [mem_ball, dist_eq_norm] using hw
      rw [hrw]
      refine le_trans (norm_add_le _ _) ?_
      linarith
    have h5 : ‖q w‖ * ‖x - w‖ ≤ (2 * M / r) * (‖x - x₀‖ + r) :=
      mul_le_mul (hqbd w hw) h3 (norm_nonneg _) (div_nonneg (by linarith) hr.le)
    linarith
  refine ⟨fun x => sSup ((fun w => ψ w + inner ℝ (q w) (x - w)) '' ball x₀ r), ⟨convex_univ, ?_⟩, ?_⟩
  · -- Step 3: `ψ'` is convex on all of `E`
    intro x₁ _ x₂ _ a b ha hb hab
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [smul_eq_mul]
    refine csSup_le (hne _) ?_
    rintro y ⟨w, hw, rfl⟩
    have e1 : a • (x₁ - w) + (1 - a) • (x₂ - w) = (a • x₁ + (1 - a) • x₂) - w := by module
    have hinn : inner ℝ (q w) ((a • x₁ + (1 - a) • x₂) - w)
        = a * inner ℝ (q w) (x₁ - w) + (1 - a) * inner ℝ (q w) (x₂ - w) := by
      rw [← e1, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    have hle1 : ψ w + inner ℝ (q w) (x₁ - w)
        ≤ sSup ((fun u => ψ u + inner ℝ (q u) (x₁ - u)) '' ball x₀ r) :=
      le_csSup (hbdd x₁) ⟨w, hw, rfl⟩
    have hle2 : ψ w + inner ℝ (q w) (x₂ - w)
        ≤ sSup ((fun u => ψ u + inner ℝ (q u) (x₂ - u)) '' ball x₀ r) :=
      le_csSup (hbdd x₂) ⟨w, hw, rfl⟩
    simp only [hinn]
    nlinarith [mul_le_mul_of_nonneg_left hle1 ha, mul_le_mul_of_nonneg_left hle2 hb]
  · -- Step 4: `ψ' = ψ` on the inner ball
    intro x hx
    have hxΩ : x ∈ Ω := hball (hballsub hx)
    have hup : sSup ((fun w => ψ w + inner ℝ (q w) (x - w)) '' ball x₀ r) ≤ ψ x := by
      refine csSup_le (hne x) ?_
      rintro y ⟨w, hw, rfl⟩
      exact hq w hw x hxΩ
    have hlo : ψ x ≤ sSup ((fun w => ψ w + inner ℝ (q w) (x - w)) '' ball x₀ r) := by
      have hmemset : ψ x ∈ (fun w => ψ w + inner ℝ (q w) (x - w)) '' ball x₀ r := by
        refine ⟨x, hx, ?_⟩
        simp
      exact le_csSup (hbdd x) hmemset
    exact le_antisymm hup hlo
