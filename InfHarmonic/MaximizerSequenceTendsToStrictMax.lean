module

public import InfHarmonic.Preamble

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 2 of the viscosity stability argument: if `v₀ - ψ` has a strict maximum
at `z` over the closed ball of radius `ϱ`, if `v j → v₀` uniformly there, and if
each `v j - ψ` attains a maximum over the ball, then any choice of maximizers
`ζ j` converges to `z`. -/
theorem MaximizerSequenceTendsToStrictMax (z : WithLp 2 (F × ℝ)) (ϱ : ℝ) (hϱ : 0 < ϱ)
    (s : ℝ) (hsabs : |s| = 1)
    (v : ℕ → WithLp 2 (F × ℝ) → ℝ) (v₀ ψ : WithLp 2 (F × ℝ) → ℝ)
    (hv₀C : ContinuousOn v₀ (closedBall z ϱ))
    (hψC : ContinuousOn ψ (closedBall z ϱ))
    (hconvC : TendstoUniformlyOn v v₀ atTop (closedBall z ϱ))
    (hstrict : ∀ w ∈ closedBall z ϱ, w ≠ z →
      s * (v₀ w - ψ w) < s * (v₀ z - ψ z))
    (hex : ∀ j : ℕ, ∃ w ∈ closedBall z ϱ,
      IsMaxOn (fun y => s * (v j y - ψ y)) (closedBall z ϱ) w) :
    ∃ ζ : ℕ → WithLp 2 (F × ℝ), (∀ j, ζ j ∈ closedBall z ϱ) ∧
      (∀ j, IsMaxOn (fun y => s * (v j y - ψ y)) (closedBall z ϱ) (ζ j)) ∧
      Tendsto ζ atTop (𝓝 z) := by
  have hCcpt : IsCompact (closedBall z ϱ) := isCompact_closedBall _ _
  have hzC : z ∈ closedBall z ϱ := mem_closedBall_self hϱ.le
  choose ζ hζC hζmax using hex
  refine ⟨ζ, hζC, hζmax, ?_⟩
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  set r : ℝ := min ε ϱ with hrdef
  have hr : 0 < r := lt_min hε hϱ
  have hrε : r ≤ ε := min_le_left _ _
  by_cases hAempty : ∀ w ∈ closedBall z ϱ, dist w z < r
  · exact .of_forall fun j => lt_of_lt_of_le (hAempty _ (hζC j)) hrε
  · push Not at hAempty
    obtain ⟨w₀, hw₀C, hw₀r⟩ := hAempty
    set A : Set (WithLp 2 (F × ℝ)) := {w | w ∈ closedBall z ϱ ∧ r ≤ dist w z} with hAdef
    have hAcpt : IsCompact A := by
      have hAeq : A = closedBall z ϱ ∩ {w | r ≤ dist w z} := rfl
      rw [hAeq]
      exact hCcpt.inter_right
        (isClosed_le continuous_const (continuous_id.dist continuous_const))
    have hAne : A.Nonempty := ⟨w₀, hw₀C, hw₀r⟩
    have hgcont : ContinuousOn (fun y => s * (v₀ y - ψ y)) A :=
      continuousOn_const.mul ((hv₀C.sub hψC).mono fun w hw => hw.1)
    obtain ⟨m, hmA, hmmax⟩ := hAcpt.exists_isMaxOn hAne hgcont
    have hmz : m ≠ z := by
      intro h
      have : r ≤ dist z z := h ▸ hmA.2
      simp at this; linarith
    have hlt : s * (v₀ m - ψ m) < s * (v₀ z - ψ z) := hstrict m hmA.1 hmz
    set M : ℝ := s * (v₀ z - ψ z) with hMdef
    set μ : ℝ := s * (v₀ m - ψ m) with hμdef
    have hδpos : 0 < (M - μ) / 2 := by simp only [hMdef, hμdef]; linarith
    have hunif := Metric.tendstoUniformlyOn_iff.mp hconvC _ hδpos
    filter_upwards [hunif] with j hj
    refine lt_of_lt_of_le ?_ hrε
    by_contra hcon
    push Not at hcon
    have hζA : ζ j ∈ A := ⟨hζC j, hcon⟩
    -- `|s * (v j w - ψ w) - s * (v₀ w - ψ w)| < (M - μ)/2` on the ball
    have hclose : ∀ w ∈ closedBall z ϱ,
        |s * (v j w - ψ w) - s * (v₀ w - ψ w)| < (M - μ) / 2 := by
      intro w hw
      have h1 := hj w hw
      rw [Real.dist_eq] at h1
      have e : s * (v j w - ψ w) - s * (v₀ w - ψ w) = s * (v j w - v₀ w) := by ring
      rw [e, abs_mul, hsabs, one_mul, abs_sub_comm]
      exact h1
    have h1 := abs_lt.mp (hclose z hzC)
    have h2 := abs_lt.mp (hclose (ζ j) (hζC j))
    have h3 : s * (v j z - ψ z) ≤ s * (v j (ζ j) - ψ (ζ j)) := hζmax j hzC
    have h4 : s * (v₀ (ζ j) - ψ (ζ j)) ≤ μ := hmmax hζA
    simp only [← hMdef] at h1 h2 h3 h4 ⊢
    linarith [h1.1, h2.2]
