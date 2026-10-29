module

public import InfHarmonic.AsymptEquicontLocalUniformLimit

@[expose] public section
open Metric Set Filter Topology

/-- The locally uniform limit of an asymptotically bounded, asymptotically
equicontinuous family, packaged with the three further properties a blow-up
argument needs and that local uniform convergence alone does not give: the
extracting subsequence may be taken past any prescribed index, the limit is
CONTINUOUS, and the limit vanishes at the origin when every late member does.
Continuity is the substantive part: the asymptotic modulus passes to the limit. -/
theorem AsymptEquicontOriginNormalizedLimit {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (g : ℕ → H → ℝ) (i₁ : ℕ)
    (hbd : ∀ ρ : ℝ, 0 < ρ → ∃ (A : ℝ) (j₀ : ℕ), ∀ j ≥ j₀,
      ∀ w ∈ closedBall (0 : H) ρ, |g j w| ≤ A)
    (hequi : ∀ ρ : ℝ, 0 < ρ → ∀ ε > 0, ∃ η > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀,
      ∀ w ∈ closedBall (0 : H) ρ, ∀ w' ∈ closedBall (0 : H) ρ,
        ‖w - w'‖ ≤ η → |g j w - g j w'| ≤ ε)
    (horigin : ∀ i ≥ i₁, g i 0 = 0) :
    ∃ (ψ : ℕ → ℕ) (w : H → ℝ),
      StrictMono ψ ∧ (∀ j, i₁ ≤ ψ j) ∧ Continuous w ∧
      (∀ C : Set H, IsCompact C → TendstoUniformlyOn (fun j => g (ψ j)) w atTop C) ∧
      w 0 = 0 := by
  classical
  obtain ⟨ψ₀, w, hmono₀, hconv₀⟩ := AsymptEquicontLocalUniformLimit g hbd hequi
  -- shift the subsequence so that every index is at least `i₁`
  refine ⟨fun j => ψ₀ (j + i₁), w, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun a b hab => hmono₀ (by omega)
  · intro j
    exact le_trans (by omega) (hmono₀.le_apply (x := j + i₁))
  -- CONTINUITY, from the asymptotic modulus and pointwise convergence
  · rw [Metric.continuous_iff]
    intro x ε hε
    obtain ⟨η, hη, j₀, hmod⟩ := hequi (‖x‖ + 2) (by positivity) (ε / 3) (by linarith)
    refine ⟨min η 1, lt_min hη one_pos, ?_⟩
    intro y hy
    have hxb : x ∈ closedBall (0 : H) (‖x‖ + 2) := by
      rw [mem_closedBall, dist_zero_right]; linarith
    have hyb : y ∈ closedBall (0 : H) (‖x‖ + 2) := by
      rw [mem_closedBall, dist_zero_right]
      have hny : ‖y‖ ≤ ‖x‖ + dist y x := by
        have h := norm_le_norm_add_norm_sub' y x
        simpa [dist_eq_norm] using h
      have hd1 : dist y x ≤ 1 := le_trans (le_of_lt hy) (min_le_right _ _)
      linarith
    have hpt : ∀ u : H, Tendsto (fun j => g (ψ₀ (j + i₁)) u) atTop (nhds (w u)) := by
      intro u
      have h1 : TendstoUniformlyOn (fun j => g (ψ₀ j)) w atTop ({u} : Set H) :=
        hconv₀ _ isCompact_singleton
      exact (h1.tendsto_at (mem_singleton u)).comp (tendsto_add_atTop_nat i₁)
    have hlim : |w x - w y| ≤ ε / 3 := by
      have hev : ∀ᶠ j in atTop, |g (ψ₀ (j + i₁)) x - g (ψ₀ (j + i₁)) y| ≤ ε / 3 := by
        filter_upwards [eventually_ge_atTop j₀] with j hj
        have hidx : j₀ ≤ ψ₀ (j + i₁) :=
          le_trans hj (le_trans (by omega) (hmono₀.le_apply (x := j + i₁)))
        refine hmod (ψ₀ (j + i₁)) hidx x hxb y hyb ?_
        have hxy : ‖x - y‖ = dist y x := by rw [dist_eq_norm, norm_sub_rev]
        rw [hxy]
        exact le_trans (le_of_lt hy) (min_le_left _ _)
      exact le_of_tendsto ((hpt x).sub (hpt y)).abs hev
    have hd : dist (w y) (w x) = |w x - w y| := by
      rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_comm]
    rw [hd]
    linarith
  · intro C hC
    exact fun u hu => (tendsto_add_atTop_nat i₁).eventually (hconv₀ C hC u hu)
  -- the limit vanishes at the origin
  · have hpt0 : Tendsto (fun j => g (ψ₀ (j + i₁)) 0) atTop (nhds (w 0)) := by
      have h1 : TendstoUniformlyOn (fun j => g (ψ₀ j)) w atTop ({0} : Set H) :=
        hconv₀ _ isCompact_singleton
      exact (h1.tendsto_at (mem_singleton 0)).comp (tendsto_add_atTop_nat i₁)
    have hz : ∀ j, g (ψ₀ (j + i₁)) 0 = 0 := by
      intro j
      exact horigin _ (le_trans (by omega) (hmono₀.le_apply (x := j + i₁)))
    have hc : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds (w 0)) := by
      simpa [hz] using hpt0
    exact tendsto_nhds_unique hc tendsto_const_nhds
