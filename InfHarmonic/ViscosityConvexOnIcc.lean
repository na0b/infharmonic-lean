import InfHarmonic.Preamble
open Set

/-- The one-dimensional viscosity criterion for convexity.  A continuous function on
`[0, T]` whose every quadratic upper test at an interior point has nonnegative leading
coefficient is convex.  Mathlib's second-derivative criteria require the function itself to
be twice differentiable; the point of this statement is that `G` need only be continuous,
the second-order information arriving entirely through test functions.  Quadratic tests
suffice because a failure of convexity is contradicted by a quadratic. -/
theorem ViscosityConvexOnIcc (T : ℝ) (hT : 0 < T) (G : ℝ → ℝ)
    (hGc : ContinuousOn G (Set.Icc 0 T))
    (htest : ∀ A B C l₀ : ℝ, l₀ ∈ Set.Ioo (0:ℝ) T →
      IsLocalMaxOn (fun τ : ℝ => G τ - (A * τ ^ 2 + B * τ + C)) (Set.Icc (0:ℝ) T) l₀ →
      0 ≤ A) :
    ConvexOn ℝ (Set.Icc (0:ℝ) T) G := by
  rw [convexOn_iff_slope_mono_adjacent]
  refine ⟨convex_Icc 0 T, ?_⟩
  intro a τ b ha hb haτ hτb
  by_contra hslope
  push_neg at hslope
  -- the chord through `(a, G a)` and `(b, G b)` lies strictly below `G` at `τ`
  have hab : a < b := lt_trans haτ hτb
  have hba : (0:ℝ) < b - a := by linarith
  have hτa : (0:ℝ) < τ - a := by linarith
  have hbτ : (0:ℝ) < b - τ := by linarith
  obtain ⟨lam, hlamd⟩ : ∃ L : ℝ → ℝ,
      L = fun r : ℝ => ((b - r) * G a + (r - a) * G b) / (b - a) := ⟨_, rfl⟩
  have hchord : lam τ < G τ := by
    have h1 := hslope
    rw [div_lt_div_iff₀ hbτ hτa] at h1
    rw [hlamd]
    show ((b - τ) * G a + (τ - a) * G b) / (b - a) < G τ
    rw [div_lt_iff₀ hba]
    nlinarith [h1]
  -- the gap between `G` and the chord, on `[a, b]`
  obtain ⟨hh, hhd⟩ : ∃ H : ℝ → ℝ, H = fun r : ℝ => G r - lam r := ⟨_, rfl⟩
  have habIcc : Set.Icc a b ⊆ Set.Icc (0:ℝ) T := Set.Icc_subset_Icc ha.1 hb.2
  have hlamc : Continuous lam := by rw [hlamd]; fun_prop
  have hHc : ContinuousOn hh (Set.Icc a b) := by
    rw [hhd]
    exact (hGc.mono habIcc).sub hlamc.continuousOn
  have hane : a ∈ Set.Icc a b := Set.left_mem_Icc.mpr hab.le
  obtain ⟨τ₁, hτ₁mem, hτ₁max⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn
    ⟨a, hane⟩ hHc
  obtain ⟨m, hmd⟩ : ∃ r : ℝ, r = hh τ₁ := ⟨_, rfl⟩
  have hm0 : 0 < m := by
    have h1 : hh τ ≤ hh τ₁ := hτ₁max ⟨haτ.le, hτb.le⟩
    have h2 : 0 < hh τ := by rw [hhd]; show 0 < G τ - lam τ; linarith
    rw [hmd]; linarith
  -- a strictly concave quadratic perturbation, small enough to keep the maximum positive
  obtain ⟨η, hηd⟩ : ∃ r : ℝ, r = m / (b - a) ^ 2 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηd]; positivity
  obtain ⟨KK, hKd⟩ : ∃ Kf : ℝ → ℝ,
      Kf = fun r : ℝ => hh r + η * ((r - a) * (r - b)) := ⟨_, rfl⟩
  have hKc : ContinuousOn KK (Set.Icc a b) := by
    rw [hKd]
    exact hHc.add (by fun_prop)
  obtain ⟨τ₂, hτ₂mem, hτ₂max⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn
    ⟨a, hane⟩ hKc
  -- the quadratic bound `|(r-a)(r-b)| ≤ (b-a)²/4` keeps `K (τ₁)` above `m/2`
  have hKτ₁ : m / 2 < KK τ₁ := by
    have hbnd : -((b - a) ^ 2 / 4) ≤ (τ₁ - a) * (τ₁ - b) := by
      nlinarith [sq_nonneg (2 * τ₁ - a - b)]
    have hmul : η * (-((b - a) ^ 2 / 4)) ≤ η * ((τ₁ - a) * (τ₁ - b)) :=
      mul_le_mul_of_nonneg_left hbnd hη0.le
    have he : η * ((b - a) ^ 2 / 4) = m / 4 := by
      rw [hηd]; field_simp
    rw [hKd]
    show m / 2 < hh τ₁ + η * ((τ₁ - a) * (τ₁ - b))
    rw [← hmd]
    nlinarith [hmul, he]
  have hK2 : m / 2 < KK τ₂ := lt_of_lt_of_le hKτ₁ (hτ₂max hτ₁mem)
  -- so the maximum is attained strictly inside, where the endpoint values vanish
  have hKa : KK a = 0 := by
    rw [hKd]
    show hh a + η * ((a - a) * (a - b)) = 0
    rw [hhd]
    show G a - lam a + η * ((a - a) * (a - b)) = 0
    rw [hlamd]
    field_simp
    ring
  have hKb : KK b = 0 := by
    rw [hKd]
    show hh b + η * ((b - a) * (b - b)) = 0
    rw [hhd]
    show G b - lam b + η * ((b - a) * (b - b)) = 0
    rw [hlamd]
    field_simp
    ring
  have hτ₂a : a < τ₂ := by
    rcases lt_or_eq_of_le hτ₂mem.1 with h | h
    · exact h
    · exact absurd (h ▸ hKa) (by linarith [hK2, hm0] : KK τ₂ ≠ 0)
  have hτ₂b : τ₂ < b := by
    rcases lt_or_eq_of_le hτ₂mem.2 with h | h
    · exact h
    · exact absurd (h ▸ hKb) (by linarith [hK2, hm0] : KK τ₂ ≠ 0)
  have hτ₂int : τ₂ ∈ Set.Ioo (0:ℝ) T :=
    ⟨lt_of_le_of_lt ha.1 hτ₂a, lt_of_lt_of_le hτ₂b hb.2⟩
  -- the quadratic upper test, written in standard form
  obtain ⟨A, hAd⟩ : ∃ r : ℝ, r = -η := ⟨_, rfl⟩
  obtain ⟨B, hBd⟩ : ∃ r : ℝ, r = (G b - G a) / (b - a) + η * (a + b) := ⟨_, rfl⟩
  obtain ⟨C, hCd⟩ : ∃ r : ℝ,
      r = (b * G a - a * G b) / (b - a) - η * (a * b) + KK τ₂ := ⟨_, rfl⟩
  have hshape : ∀ u : ℝ, G u - (A * u ^ 2 + B * u + C) = KK u - KK τ₂ := by
    intro u
    rw [hAd, hBd, hCd, hKd, hhd, hlamd]
    field_simp
    ring
  have hlocmax : IsLocalMaxOn
      (fun r : ℝ => G r - (A * r ^ 2 + B * r + C)) (Set.Icc (0:ℝ) T) τ₂ := by
    have hnb : Set.Ioo a b ∈ nhds τ₂ := isOpen_Ioo.mem_nhds ⟨hτ₂a, hτ₂b⟩
    filter_upwards [mem_nhdsWithin_of_mem_nhds hnb] with r hr
    show G r - (A * r ^ 2 + B * r + C) ≤ G τ₂ - (A * τ₂ ^ 2 + B * τ₂ + C)
    rw [hshape r, hshape τ₂]
    have hrab : r ∈ Set.Icc a b := ⟨hr.1.le, hr.2.le⟩
    have hmax : KK r ≤ KK τ₂ := hτ₂max hrab
    linarith [hmax]
  have := htest A B C τ₂ hτ₂int hlocmax
  rw [hAd] at this
  linarith
