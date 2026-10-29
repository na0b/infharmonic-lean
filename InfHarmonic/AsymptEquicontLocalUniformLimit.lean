module

public import InfHarmonic.Preamble

@[expose] public section
open Metric Set Filter Topology

/-- An Arzelà--Ascoli extraction with an ASYMPTOTIC modulus of continuity and a
locally uniform conclusion: a sequence of real functions on a finite-dimensional
inner-product space that is eventually uniformly bounded on each ball about the
origin, and eventually equicontinuous there with a modulus independent of the
index, has ONE subsequence converging uniformly on EVERY compact set.  Both
hypotheses are allowed to hold only from an index onwards, and that index may
depend on the ball. -/
theorem AsymptEquicontLocalUniformLimit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (g : ℕ → H → ℝ)
    (hbd : ∀ ρ : ℝ, 0 < ρ → ∃ (A : ℝ) (j₀ : ℕ), ∀ j ≥ j₀,
      ∀ w ∈ closedBall (0 : H) ρ, |g j w| ≤ A)
    (hequi : ∀ ρ : ℝ, 0 < ρ → ∀ ε > 0, ∃ η > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∀ w ∈ closedBall (0 : H) ρ, ∀ w' ∈ closedBall (0 : H) ρ,
        ‖w - w'‖ ≤ η → |g j w - g j w'| ≤ ε) :
    ∃ (ψ : ℕ → ℕ) (w : H → ℝ), StrictMono ψ ∧
      ∀ C : Set H, IsCompact C → TendstoUniformlyOn (fun j => g (ψ j)) w atTop C := by
  classical
  -- a real sequence bounded past some index is bounded outright
  have hfin : ∀ (f : ℕ → ℝ) (n : ℕ), ∃ B : ℝ, ∀ j < n, |f j| ≤ B := by
    intro f n
    induction n with
    | zero => exact ⟨0, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    | succ m ih =>
        obtain ⟨B, hB⟩ := ih
        refine ⟨max B |f m|, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact le_trans (hB j h) (le_max_left _ _)
        · rw [h]; exact le_max_right _ _
  -- a countable dense subset of the WHOLE space
  have hne : Nonempty H := ⟨0⟩
  obtain ⟨Q, hQdense⟩ : ∃ Q : ℕ → H, DenseRange Q :=
    ⟨TopologicalSpace.denseSeq H, TopologicalSpace.denseRange_denseSeq H⟩
  have hQapp : ∀ (x : H) (δ : ℝ), 0 < δ → ∃ k, dist x (Q k) < δ := by
    intro x δ hδ
    exact Metric.denseRange_iff.mp hQdense x δ hδ
  -- at each point of the dense set the whole sequence of values is bounded
  have hbdall : ∀ k : ℕ, ∃ A : ℝ, ∀ j, |g j (Q k)| ≤ A := by
    intro k
    obtain ⟨A, j₀, hA⟩ := hbd (‖Q k‖ + 1) (by positivity)
    obtain ⟨B, hB⟩ := hfin (fun j => g j (Q k)) j₀
    have hQk : Q k ∈ closedBall (0 : H) (‖Q k‖ + 1) := by
      rw [mem_closedBall, dist_zero_right]
      linarith only [norm_nonneg (Q k)]
    refine ⟨max A B, fun j => ?_⟩
    rcases lt_or_ge j j₀ with h | h
    · exact le_trans (hB j h) (le_max_right _ _)
    · exact le_trans (hA j h (Q k) hQk) (le_max_left _ _)
  choose A hA using hbdall
  -- one subsequence converging at every point of the dense set
  have hcpt : IsCompact (Set.univ.pi (fun k : ℕ => Set.Icc (-(A k)) (A k))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ j : ℕ, (fun k => g j (Q k))
      ∈ Set.univ.pi (fun k : ℕ => Set.Icc (-(A k)) (A k)) := by
    intro j k _
    have h := abs_le.mp (hA k j)
    exact Set.mem_Icc.mpr ⟨h.1, h.2⟩
  obtain ⟨c, -, φ, hφmono, hφtend⟩ := hcpt.tendsto_subseq hmem
  have hptdense : ∀ k : ℕ, Tendsto (fun j => g (φ j) (Q k)) atTop (𝓝 (c k)) :=
    fun k => (tendsto_pi_nhds.mp hφtend) k
  -- the subsequence is uniformly Cauchy on every closed ball about the origin
  have hcau : ∀ ρ : ℝ, 0 < ρ →
      UniformCauchySeqOn (fun j => g (φ j)) atTop (closedBall (0 : H) ρ) := by
    intro ρ hρ
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨η, hη0, j₁, hj₁⟩ := hequi (ρ + 1) (by linarith only [hρ]) (ε / 4)
      (by linarith only [hε])
    obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min η 1 := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min hη0 (by norm_num)
    have hδη : δ ≤ η := by rw [hδdef]; exact min_le_left _ _
    have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_right _ _
    have hcov : closedBall (0 : H) ρ ⊆ ⋃ k : ℕ, ball (Q k) δ := by
      intro x _
      obtain ⟨k, hk⟩ := hQapp x δ hδ0
      exact Set.mem_iUnion.mpr ⟨k, by rwa [Metric.mem_ball]⟩
    obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : H) ρ).elim_finite_subcover
      (fun k : ℕ => ball (Q k) δ) (fun _ => Metric.isOpen_ball) hcov
    have hev : ∀ᶠ j in atTop, ∀ k ∈ t, |g (φ j) (Q k) - c k| < ε / 4 := by
      refine (Filter.eventually_all_finset t).mpr fun k _ => ?_
      have h := (hptdense k) (Metric.ball_mem_nhds (c k) (by positivity : (0:ℝ) < ε / 4))
      filter_upwards [h] with j hj
      have hj' : dist (g (φ j) (Q k)) (c k) < ε / 4 := hj
      rwa [Real.dist_eq] at hj'
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨max N j₁, fun m hm n hn x hx => ?_⟩
    have hmN : N ≤ m := le_trans (le_max_left _ _) hm
    have hnN : N ≤ n := le_trans (le_max_left _ _) hn
    have hmj : j₁ ≤ φ m := le_trans (le_trans (le_max_right _ _) hm) hφmono.le_apply
    have hnj : j₁ ≤ φ n := le_trans (le_trans (le_max_right _ _) hn) hφmono.le_apply
    obtain ⟨k, hkt, hkx⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hxn : ‖x‖ ≤ ρ := by
      rw [mem_closedBall, dist_zero_right] at hx; exact hx
    have hd : ‖x - Q k‖ ≤ η := by
      have h1 : dist x (Q k) < δ := Metric.mem_ball.mp hkx
      rw [dist_eq_norm] at h1
      linarith only [h1, hδη]
    have hxmem : x ∈ closedBall (0 : H) (ρ + 1) := by
      rw [mem_closedBall, dist_zero_right]
      linarith only [hxn]
    have hQmem : Q k ∈ closedBall (0 : H) (ρ + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have h1 : dist x (Q k) < δ := Metric.mem_ball.mp hkx
      rw [dist_eq_norm] at h1
      have h2 : ‖Q k‖ ≤ ‖x‖ + ‖x - Q k‖ := by
        have h3 := norm_sub_le x (x - Q k)
        rwa [sub_sub_cancel] at h3
      linarith only [h2, hxn, h1, hδ1]
    have hA1 : |g (φ m) x - g (φ m) (Q k)| ≤ ε / 4 :=
      hj₁ (φ m) hmj x hxmem (Q k) hQmem hd
    have hA2 : |g (φ n) x - g (φ n) (Q k)| ≤ ε / 4 :=
      hj₁ (φ n) hnj x hxmem (Q k) hQmem hd
    have hB1 := hN m hmN k hkt
    have hB2 := hN n hnN k hkt
    rw [Real.dist_eq]
    have hid : g (φ m) x - g (φ n) x
        = (g (φ m) x - g (φ m) (Q k)) + (g (φ m) (Q k) - c k)
          - (g (φ n) (Q k) - c k) - (g (φ n) x - g (φ n) (Q k)) := by ring
    have h1 := abs_le.mp hA1
    have h2 := abs_le.mp hA2
    have h3 := abs_lt.mp hB1
    have h4 := abs_lt.mp hB2
    rw [abs_lt]
    constructor
    · rw [hid]; linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
    · rw [hid]; linarith only [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  -- the pointwise limit, defined everywhere because every point lies in some ball
  have hptall : ∀ z : H, ∃ L : ℝ, Tendsto (fun j => g (φ j) z) atTop (𝓝 L) := by
    intro z
    have hz : z ∈ closedBall (0 : H) (‖z‖ + 1) := by
      rw [mem_closedBall, dist_zero_right]
      linarith only [norm_nonneg z]
    have hcs : CauchySeq (fun j => g (φ j) z) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp
        (hcau (‖z‖ + 1) (by positivity))) ε hε
      exact ⟨N, fun n hn => hN n hn N le_rfl z hz⟩
    exact cauchySeq_tendsto_of_complete hcs
  choose w hw using hptall
  refine ⟨φ, w, hφmono, fun C hC => ?_⟩
  obtain ⟨ρ, hρsub⟩ := (Metric.isBounded_iff_subset_closedBall (0 : H)).mp hC.isBounded
  have hρ1 : C ⊆ closedBall (0 : H) (|ρ| + 1) := by
    refine hρsub.trans (closedBall_subset_closedBall ?_)
    linarith only [le_abs_self ρ]
  refine TendstoUniformlyOn.mono ?_ hρ1
  exact (hcau (|ρ| + 1) (by positivity)).tendstoUniformlyOn_of_tendsto (fun x _ => hw x)
