module

public import InfHarmonic.Preamble

@[expose] public section
open Metric Set Filter Topology

/-- Claim C of the family-flatness argument, an Arzelà--Ascoli extraction: a
sequence of functions that is uniformly bounded and uniformly Lipschitz on one
closed ball of a finite-dimensional inner-product space has a subsequence
converging uniformly on that ball.  The two constants are independent of the
index, and nothing is claimed about the limit off the ball. -/
theorem EquiLipschitzUniformLimit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (a : H) (ρ A Λ : ℝ) (hρ : 0 < ρ) (v : ℕ → H → ℝ)
    (hbd : ∀ i : ℕ, ∀ w ∈ closedBall a ρ, |v i w| ≤ A)
    (hlip : ∀ i : ℕ, ∀ w ∈ closedBall a ρ, ∀ w' ∈ closedBall a ρ,
      |v i w - v i w'| ≤ Λ * ‖w - w'‖) :
    ∃ (ι : ℕ → ℕ) (V : H → ℝ), StrictMono ι ∧
      TendstoUniformlyOn (fun k => v (ι k)) V atTop (closedBall a ρ) := by
  classical
  have hamem : a ∈ closedBall a ρ := by simp [hρ.le]
  have hA0 : 0 ≤ A := le_trans (abs_nonneg _) (hbd 0 a hamem)
  -- the Lipschitz constant may be replaced by a nonnegative one
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max Λ 0 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hMdef]; exact le_max_right _ _
  have hlip' : ∀ i : ℕ, ∀ w ∈ closedBall a ρ, ∀ w' ∈ closedBall a ρ,
      |v i w - v i w'| ≤ M * ‖w - w'‖ := by
    intro i w hw w' hw'
    refine le_trans (hlip i w hw w' hw') ?_
    exact mul_le_mul_of_nonneg_right (by rw [hMdef]; exact le_max_left _ _) (norm_nonneg _)
  -- ===== a countable dense subset of the ball =====
  have hne : Nonempty ↥(closedBall a ρ) := ⟨⟨a, hamem⟩⟩
  obtain ⟨q, hqdense⟩ : ∃ q : ℕ → ↥(closedBall a ρ), DenseRange q :=
    ⟨TopologicalSpace.denseSeq _, TopologicalSpace.denseRange_denseSeq _⟩
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℕ → H, Q = fun k => (q k : H) := ⟨_, rfl⟩
  have hQmem : ∀ k, Q k ∈ closedBall a ρ := by intro k; rw [hQdef]; exact (q k).2
  have hQapp : ∀ x ∈ closedBall a ρ, ∀ δ > 0, ∃ k, dist x (Q k) < δ := by
    intro x hx δ hδ
    obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hqdense ⟨x, hx⟩ δ hδ
    exact ⟨k, by rw [hQdef]; exact hk⟩
  -- ===== a subsequence converging at every point of that dense set =====
  have hcpt : IsCompact (Set.univ.pi (fun _ : ℕ => Set.Icc (-A) A)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ i : ℕ, (fun k => v i (Q k))
      ∈ Set.univ.pi (fun _ : ℕ => Set.Icc (-A) A) := by
    intro i k _
    have h := abs_le.mp (hbd i (Q k) (hQmem k))
    exact Set.mem_Icc.mpr ⟨h.1, h.2⟩
  obtain ⟨c, -, φ, hφmono, hφtend⟩ := hcpt.tendsto_subseq hmem
  have hptdense : ∀ k : ℕ, Tendsto (fun j => v (φ j) (Q k)) atTop (𝓝 (c k)) :=
    fun k => (tendsto_pi_nhds.mp hφtend) k
  -- ===== the subsequence is uniformly Cauchy on the ball =====
  have hcau : UniformCauchySeqOn (fun j => v (φ j)) atTop (closedBall a ρ) := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = ε / (4 * (M + 1)) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδdef]; positivity
    have hMδ : M * δ ≤ ε / 4 := by
      rw [hδdef, mul_div_assoc']
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith only [hM0, hε]
    -- cover the ball by finitely many δ-balls centred at dense points
    have hcov : closedBall a ρ ⊆ ⋃ k : ℕ, ball (Q k) δ := by
      intro x hx
      obtain ⟨k, hk⟩ := hQapp x hx δ hδ0
      exact Set.mem_iUnion.mpr ⟨k, by rwa [Metric.mem_ball]⟩
    obtain ⟨t, ht⟩ := (isCompact_closedBall a ρ).elim_finite_subcover
      (fun k : ℕ => ball (Q k) δ) (fun _ => Metric.isOpen_ball) hcov
    have hev : ∀ᶠ j in atTop, ∀ k ∈ t, |v (φ j) (Q k) - c k| < ε / 4 := by
      refine (Filter.eventually_all_finset t).mpr fun k _ => ?_
      have h := (hptdense k) (Metric.ball_mem_nhds (c k) (by positivity : (0:ℝ) < ε / 4))
      filter_upwards [h] with j hj
      have hj' : dist (v (φ j) (Q k)) (c k) < ε / 4 := hj
      rwa [Real.dist_eq] at hj'
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    obtain ⟨k, hkt, hkx⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hd : ‖x - Q k‖ ≤ δ := by
      have h1 : dist x (Q k) < δ := Metric.mem_ball.mp hkx
      rw [dist_eq_norm] at h1
      exact le_of_lt h1
    have hA1 : |v (φ m) x - v (φ m) (Q k)| ≤ M * δ := by
      refine le_trans (hlip' (φ m) x hx (Q k) (hQmem k)) ?_
      exact mul_le_mul_of_nonneg_left hd hM0
    have hA2 : |v (φ n) x - v (φ n) (Q k)| ≤ M * δ := by
      refine le_trans (hlip' (φ n) x hx (Q k) (hQmem k)) ?_
      exact mul_le_mul_of_nonneg_left hd hM0
    have hB1 := hN m hm k hkt
    have hB2 := hN n hn k hkt
    rw [Real.dist_eq]
    have hid : v (φ m) x - v (φ n) x
        = (v (φ m) x - v (φ m) (Q k)) + (v (φ m) (Q k) - c k)
          - (v (φ n) (Q k) - c k) - (v (φ n) x - v (φ n) (Q k)) := by ring
    have h1 := abs_le.mp hA1
    have h2 := abs_le.mp hA2
    have h3 := abs_lt.mp hB1
    have h4 := abs_lt.mp hB2
    rw [abs_lt]
    constructor
    · rw [hid]; linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, hMδ]
    · rw [hid]; linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, hMδ]
  -- ===== the pointwise limit on the ball, and uniform convergence =====
  have hptall : ∀ z : H, ∃ L : ℝ,
      z ∈ closedBall a ρ → Tendsto (fun j => v (φ j) z) atTop (𝓝 L) := by
    intro z
    by_cases hz : z ∈ closedBall a ρ
    · have hcs : CauchySeq (fun j => v (φ j) z) := by
        rw [Metric.cauchySeq_iff']
        intro ε hε
        obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp hcau) ε hε
        exact ⟨N, fun n hn => hN n hn N le_rfl z hz⟩
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
      exact ⟨L, fun _ => hL⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose V hV using hptall
  exact ⟨φ, V, hφmono, hcau.tendstoUniformlyOn_of_tendsto (fun x hx => hV x hx)⟩
