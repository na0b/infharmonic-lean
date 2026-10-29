module

public import InfHarmonic.SqrtSumLogSquareBounds

@[expose] public section
set_option maxHeartbeats 600000
open Set

/-- Step 3(b) of Proposition 6.7, the deterministic half: a discrete Green
function on the lattice window `{0, …, q}` whose Laplacian dominates the
logarithmic weight, with a controlled value at the starting site.

The time walk of the proposition lives on the lattice `εℤ ∩ [0, 8]`, so the
sites are the integers `0 ≤ j ≤ q` with `ε q = 8`, and the walk starts at the
site `j₀` with `ε j₀ = 1`, i.e. at time `1`. The weight to be absorbed is
`u(j) = ε² |log(ε j)|²`, the squared logarithm of the time coordinate scaled by
`ε²`. The lemma produces `G : ℤ → ℝ` which is nonnegative on the window, is a
discrete supersolution with defect `u` there --- the mean of the two neighbouring
values falls short of the value at `j` by at least `u(j)` --- and satisfies
`G(j₀) ≤ 2 Λ₀` with `Λ₀ = 32 √8 + 8 (log 8)²`. Feeding `G` to the stopped-walk
supersolution bound converts the third assertion into the expected value of the
logarithmic time average along the walk, which is why only these three facts are
returned and no probabilistic data appears here.

`G` is built from the one-dimensional lattice Green kernel
`K(j,m) = (j ∧ m)(q - (j ∨ m)) / q` of the interval `{0, …, q}`, whose discrete
Laplacian at an interior site `j` is `-1/2` exactly when `m = j` and `0`
otherwise, by `G(j) = ∑_{m<q} 2 u(m) K(j,m)`. The value bound at `j₀` comes from
`K(j₀,m) ≤ j₀` together with the grid estimate
`∑_{m<q} u(m) ≤ ε Λ₀` of \noderef{SqrtSumLogSquareBounds}. -/
theorem LatticeLogGreenFunction (ε : ℝ) (q j₀ : ℕ) (Λ₀ : ℝ)
    (hε0 : 0 < ε) (hεj : ε * (j₀ : ℝ) = 1) (hεq : ε * (q : ℝ) = 8)
    (hΛ₀d : Λ₀ = 32 * Real.sqrt 8 + 8 * Real.log 8 ^ 2) :
    ∃ hGf : ℤ → ℝ,
      (∀ j : ℤ, 0 < j → j ≤ (q : ℤ) → 0 ≤ hGf j) ∧
      (∀ j : ℤ, 0 < j → j < (q : ℤ) →
        (hGf (j + 1) + hGf (j - 1)) / 2 - hGf j
          ≤ -(ε ^ 2 * |Real.log (ε * (j : ℝ))| ^ 2)) ∧
      hGf ((j₀ : ℕ) : ℤ) ≤ 2 * Λ₀ := by
  -- `q > 0`, which is all that `ε q = 8` and `ε > 0` give about `q`
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · rw [h] at hεq; norm_num at hεq
    · exact h
  have hqR0 : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqpos
  obtain ⟨hharm, hlogbd⟩ := SqrtSumLogSquareBounds
  obtain ⟨uw, huwd⟩ : ∃ f : ℕ → ℝ,
      f = fun m : ℕ => ε ^ 2 * |Real.log (ε * (m : ℝ))| ^ 2 := ⟨_, rfl⟩
  have huw0 : ∀ m, 0 ≤ uw m := by
    intro m; rw [huwd]; positivity
  have hUW : ∑ m ∈ Finset.range q, uw m ≤ ε * Λ₀ := by
    have hq1' : 1 ≤ q := hqpos
    obtain ⟨q', hq'⟩ : ∃ k : ℕ, q = k + 1 := ⟨q - 1, by omega⟩
    have hbound : ∀ m ∈ Finset.range q,
        uw m ≤ (ε ^ 2 * 16) * (1 / Real.sqrt (ε * (m : ℝ))) + ε ^ 2 * Real.log 8 ^ 2 := by
      intro m hm
      rcases Nat.eq_zero_or_pos m with hm0 | hm0
      · subst hm0
        have h0 : uw 0 = 0 := by
          rw [huwd]; simp
        rw [h0]
        have h2 : (ε ^ 2 * 16) * (1 / Real.sqrt (ε * ((0:ℕ) : ℝ))) = 0 := by
          simp
        rw [h2]
        have h3 : (0:ℝ) ≤ ε ^ 2 * Real.log 8 ^ 2 := by positivity
        linarith only [h3]
      · have hmq : (m : ℝ) ≤ (q : ℝ) - 1 := by
          have h1 : m < q := Finset.mem_range.mp hm
          have h2 : (m : ℝ) + 1 ≤ (q : ℝ) := by
            have : (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [this]
            exact Nat.cast_le.mpr (by omega)
          linarith only [h2]
        have hs0 : (0:ℝ) < ε * (m : ℝ) := by
          have : (1:ℝ) ≤ (m : ℝ) := by
            have : (1:ℕ) ≤ m := hm0
            exact_mod_cast this
          nlinarith only [hε0, this]
        have hs8 : ε * (m : ℝ) ≤ 8 := by
          have h3 : ε * (m : ℝ) ≤ ε * ((q : ℝ) - 1) := by
            exact mul_le_mul_of_nonneg_left hmq hε0.le
          nlinarith only [h3, hεq, hε0]
        have h4 := hlogbd (ε * (m : ℝ)) hs0 hs8
        rw [huwd]
        have h5 : (0:ℝ) ≤ ε ^ 2 := sq_nonneg ε
        have h6 := mul_le_mul_of_nonneg_left h4 h5
        calc ε ^ 2 * |Real.log (ε * (m : ℝ))| ^ 2
            ≤ ε ^ 2 * (16 / Real.sqrt (ε * (m : ℝ)) + Real.log 8 ^ 2) := h6
          _ = (ε ^ 2 * 16) * (1 / Real.sqrt (ε * (m : ℝ))) + ε ^ 2 * Real.log 8 ^ 2 := by
              ring
    have hsplit : ∑ m ∈ Finset.range q,
        ((ε ^ 2 * 16) * (1 / Real.sqrt (ε * (m : ℝ))) + ε ^ 2 * Real.log 8 ^ 2)
        = (ε ^ 2 * 16) * (∑ m ∈ Finset.range q, 1 / Real.sqrt (ε * (m : ℝ)))
          + (q : ℝ) * (ε ^ 2 * Real.log 8 ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
    have hshift : ∑ m ∈ Finset.range q, 1 / Real.sqrt (ε * (m : ℝ))
        ≤ 2 * Real.sqrt (ε * (q' : ℝ)) / ε := by
      rw [hq', Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero, div_zero, add_zero]
      have he : ∀ m ∈ Finset.range q', 1 / Real.sqrt (ε * ((m + 1 : ℕ) : ℝ))
          = 1 / Real.sqrt (ε * ((m : ℝ) + 1)) := by
        intro m _
        push_cast
        ring_nf
      rw [Finset.sum_congr rfl he]
      exact hharm ε hε0 q'
    have hfinal : (ε ^ 2 * 16) * (2 * Real.sqrt (ε * (q' : ℝ)) / ε)
        + (q : ℝ) * (ε ^ 2 * Real.log 8 ^ 2) ≤ ε * Λ₀ := by
      have h1 : Real.sqrt (ε * (q' : ℝ)) ≤ Real.sqrt 8 := by
        refine Real.sqrt_le_sqrt ?_
        have h2 : (q' : ℝ) ≤ (q : ℝ) := by
          rw [hq']; push_cast; linarith only []
        have h3 : ε * (q' : ℝ) ≤ ε * (q : ℝ) := mul_le_mul_of_nonneg_left h2 hε0.le
        linarith only [h3, hεq]
      have h4 : (ε ^ 2 * 16) * (2 * Real.sqrt (ε * (q' : ℝ)) / ε)
          = 32 * ε * Real.sqrt (ε * (q' : ℝ)) := by
        field_simp
        ring
      have h5 : (q : ℝ) * (ε ^ 2 * Real.log 8 ^ 2) = 8 * ε * Real.log 8 ^ 2 := by
        have h6 : (q : ℝ) * ε = 8 := by rw [mul_comm]; exact hεq
        calc (q : ℝ) * (ε ^ 2 * Real.log 8 ^ 2) = ((q : ℝ) * ε) * (ε * Real.log 8 ^ 2) := by
              ring
          _ = 8 * (ε * Real.log 8 ^ 2) := by rw [h6]
          _ = 8 * ε * Real.log 8 ^ 2 := by ring
      rw [h4, h5, hΛ₀d]
      have h7 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
      have h8 : 32 * ε * Real.sqrt (ε * (q' : ℝ)) ≤ 32 * ε * Real.sqrt 8 :=
        mul_le_mul_of_nonneg_left h1 (by linarith only [hε0])
      nlinarith only [h8]
    calc ∑ m ∈ Finset.range q, uw m
        ≤ ∑ m ∈ Finset.range q,
            ((ε ^ 2 * 16) * (1 / Real.sqrt (ε * (m : ℝ))) + ε ^ 2 * Real.log 8 ^ 2) :=
          Finset.sum_le_sum hbound
      _ = (ε ^ 2 * 16) * (∑ m ∈ Finset.range q, 1 / Real.sqrt (ε * (m : ℝ)))
            + (q : ℝ) * (ε ^ 2 * Real.log 8 ^ 2) := hsplit
      _ ≤ (ε ^ 2 * 16) * (2 * Real.sqrt (ε * (q' : ℝ)) / ε)
            + (q : ℝ) * (ε ^ 2 * Real.log 8 ^ 2) := by
          have h9 : (0:ℝ) ≤ ε ^ 2 * 16 := by positivity
          have h10 := mul_le_mul_of_nonneg_left hshift h9
          linarith only [h10]
      _ ≤ ε * Λ₀ := hfinal
  -- the Green function of the stopped time walk
  obtain ⟨Kf, hKfd⟩ : ∃ f : ℤ → ℤ → ℝ, f = fun j m =>
      ((min j m : ℤ) : ℝ) * ((q:ℝ) - ((max j m : ℤ) : ℝ)) / (q:ℝ) := ⟨_, rfl⟩
  have hKfnn : ∀ j m : ℤ, 0 ≤ j → j ≤ (q:ℤ) → 0 ≤ m → m ≤ (q:ℤ) → 0 ≤ Kf j m := by
    intro j m hj0 hjq hm0 hmq
    rw [hKfd]
    have h1 : (0:ℝ) ≤ ((min j m : ℤ) : ℝ) := by
      have h : (0:ℤ) ≤ min j m := le_min hj0 hm0
      exact_mod_cast h
    have h2 : ((max j m : ℤ) : ℝ) ≤ (q:ℝ) := by
      have h : max j m ≤ (q:ℤ) := max_le hjq hmq
      exact_mod_cast h
    have h3 : (0:ℝ) ≤ (q:ℝ) - ((max j m : ℤ) : ℝ) := by linarith only [h2]
    exact div_nonneg (mul_nonneg h1 h3) hqR0.le
  have hKfpoi : ∀ j m : ℤ, 0 < j → j < (q:ℤ) →
      (Kf (j + 1) m + Kf (j - 1) m) / 2 - Kf j m = (if m = j then -(1/2) else 0) := by
    intro j m hj1 hj2
    rcases lt_trichotomy m j with hc | hc | hc
    · rw [if_neg (by omega), hKfd]
      simp only [min_eq_right (show m ≤ j + 1 by omega), min_eq_right (show m ≤ j - 1 by omega),
        min_eq_right (show m ≤ j by omega), max_eq_left (show m ≤ j + 1 by omega),
        max_eq_left (show m ≤ j - 1 by omega), max_eq_left (show m ≤ j by omega)]
      push_cast
      field_simp
      ring
    · subst hc
      rw [if_pos rfl, hKfd]
      simp only [min_eq_right (show m ≤ m + 1 by omega), max_eq_left (show m ≤ m + 1 by omega),
        min_eq_left (show m - 1 ≤ m by omega), max_eq_right (show m - 1 ≤ m by omega),
        min_self, max_self]
      push_cast
      field_simp
      ring
    · rw [if_neg (by omega), hKfd]
      simp only [min_eq_left (show j + 1 ≤ m by omega), min_eq_left (show j - 1 ≤ m by omega),
        min_eq_left (show j ≤ m by omega), max_eq_right (show j + 1 ≤ m by omega),
        max_eq_right (show j - 1 ≤ m by omega), max_eq_right (show j ≤ m by omega)]
      push_cast
      field_simp
      ring
  obtain ⟨uf, hufd⟩ : ∃ f : ℤ → ℝ,
      f = fun j : ℤ => ε ^ 2 * |Real.log (ε * (j : ℝ))| ^ 2 := ⟨_, rfl⟩
  have hufuw : ∀ m : ℕ, uf ((m : ℕ) : ℤ) = uw m := by
    intro m
    rw [hufd, huwd]
    push_cast
    ring
  obtain ⟨hGf, hGfd⟩ : ∃ f : ℤ → ℝ,
      f = fun j => ∑ m ∈ Finset.range q, 2 * uw m * Kf j ((m : ℕ) : ℤ) := ⟨_, rfl⟩
  have hGfnn : ∀ j : ℤ, 0 < j → j ≤ (q:ℤ) → 0 ≤ hGf j := by
    intro j h1 h2
    rw [hGfd]
    refine Finset.sum_nonneg (fun m hm => ?_)
    have h3 : (0:ℤ) ≤ ((m : ℕ) : ℤ) := Int.natCast_nonneg m
    have h4 : ((m : ℕ) : ℤ) ≤ (q:ℤ) := by
      have h : m < q := Finset.mem_range.mp hm
      exact_mod_cast le_of_lt h
    have h5 := hKfnn j ((m : ℕ) : ℤ) (le_of_lt h1) h2 h3 h4
    have h6 := huw0 m
    exact mul_nonneg (mul_nonneg (by norm_num) h6) h5
  have hGfpoi : ∀ j : ℤ, 0 < j → j < (q:ℤ) →
      (hGf (j + 1) + hGf (j - 1)) / 2 - hGf j ≤ -(uf j) := by
    intro j h1 h2
    have hkey : (hGf (j + 1) + hGf (j - 1)) / 2 - hGf j
        = ∑ m ∈ Finset.range q, (if ((m : ℕ) : ℤ) = j then -(uw m) else 0) := by
      simp only [hGfd]
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have h3 := hKfpoi j ((m : ℕ) : ℤ) h1 h2
      have h4 : (2 * uw m * Kf (j + 1) ((m : ℕ) : ℤ) + 2 * uw m * Kf (j - 1) ((m : ℕ) : ℤ)) / 2
          - 2 * uw m * Kf j ((m : ℕ) : ℤ)
          = 2 * uw m * ((Kf (j + 1) ((m : ℕ) : ℤ) + Kf (j - 1) ((m : ℕ) : ℤ)) / 2
            - Kf j ((m : ℕ) : ℤ)) := by ring
      rw [h4, h3]
      by_cases hc : ((m : ℕ) : ℤ) = j
      · rw [if_pos hc, if_pos hc]; ring
      · rw [if_neg hc, if_neg hc]; ring
    have hufj : uf j = uw j.toNat := by
      have h5 : ((j.toNat : ℕ) : ℤ) = j := Int.toNat_of_nonneg (le_of_lt h1)
      have h6 := hufuw j.toNat
      rw [h5] at h6
      exact h6
    have hcollapse : ∑ m ∈ Finset.range q, (if ((m : ℕ) : ℤ) = j then -(uw m) else 0)
        = -(uw j.toNat) := by
      have he : ∀ m ∈ Finset.range q, (if ((m : ℕ) : ℤ) = j then -(uw m) else 0)
          = (if m = j.toNat then -(uw m) else 0) := by
        intro m _
        by_cases hc : ((m : ℕ) : ℤ) = j
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
      rw [Finset.sum_congr rfl he,
        Finset.sum_ite_eq' (Finset.range q) j.toNat (fun m => -(uw m)),
        if_pos (Finset.mem_range.mpr (by omega))]
    rw [hkey, hcollapse, hufj]
  have hGfj : hGf ((j₀ : ℕ) : ℤ) ≤ 2 * Λ₀ := by
    have hKle : ∀ m : ℕ, m < q → Kf ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) ≤ (j₀ : ℝ) := by
      intro m hm
      rw [hKfd]
      have hj0 : (0:ℤ) ≤ ((j₀ : ℕ) : ℤ) := Int.natCast_nonneg _
      have hm0 : (0:ℤ) ≤ ((m : ℕ) : ℤ) := Int.natCast_nonneg _
      have h1 : (0:ℝ) ≤ ((min ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) : ℤ) : ℝ) := by
        have h : (0:ℤ) ≤ min ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) := le_min hj0 hm0
        exact_mod_cast h
      have h2 : ((min ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) : ℤ) : ℝ) ≤ (j₀ : ℝ) := by
        have h : min ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) ≤ ((j₀ : ℕ) : ℤ) := min_le_left _ _
        exact_mod_cast h
      have h3 : (0:ℝ) ≤ ((max ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) : ℤ) : ℝ) := by
        have h : (0:ℤ) ≤ max ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ) := le_max_of_le_left hj0
        exact_mod_cast h
      rw [div_le_iff₀ hqR0]
      nlinarith only [h1, h2, h3, hqR0]
    have hstep : ∑ m ∈ Finset.range q, 2 * uw m * Kf ((j₀ : ℕ) : ℤ) ((m : ℕ) : ℤ)
        ≤ ∑ m ∈ Finset.range q, 2 * uw m * (j₀ : ℝ) := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      have h1 := hKle m (Finset.mem_range.mp hm)
      have h2 := huw0 m
      nlinarith only [h1, h2]
    have heq : ∑ m ∈ Finset.range q, 2 * uw m * (j₀ : ℝ)
        = (2 * (j₀ : ℝ)) * (∑ m ∈ Finset.range q, uw m) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    have hj0nn : (0:ℝ) ≤ 2 * (j₀ : ℝ) := by
      have := Nat.cast_nonneg (α := ℝ) j₀
      linarith only [this]
    have hfin : (2 * (j₀ : ℝ)) * (∑ m ∈ Finset.range q, uw m) ≤ 2 * Λ₀ := by
      have h1 := mul_le_mul_of_nonneg_left hUW hj0nn
      have h2 : (2 * (j₀ : ℝ)) * (ε * Λ₀) = 2 * Λ₀ := by
        calc (2 * (j₀ : ℝ)) * (ε * Λ₀) = 2 * Λ₀ * (ε * (j₀ : ℝ)) := by ring
          _ = 2 * Λ₀ := by rw [hεj]; ring
      linarith only [h1, h2]
    rw [hGfd]
    linarith only [hstep, heq, hfin]
  refine ⟨hGf, hGfnn, fun j h1 h2 => ?_, hGfj⟩
  have h3 : uf j = ε ^ 2 * |Real.log (ε * (j : ℝ))| ^ 2 := by rw [hufd]
  rw [← h3]
  exact hGfpoi j h1 h2
