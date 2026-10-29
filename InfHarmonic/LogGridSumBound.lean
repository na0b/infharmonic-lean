module

public import InfHarmonic.SqrtSumLogSquareBounds
public import InfHarmonic.StoppedLatticeSupersolutionBound

@[expose] public section
set_option maxHeartbeats 400000
open Metric Set Filter Topology MeasureTheory

/-- Step 6(b,c) of Proposition 6.7: the logarithmic grid sum.  The lattice
weight `uw` carries `(eps/r)^2 |log ((eps/r) i)|^2` on the open window
`(aa, bb)` and vanishes outside it.  The expected sum of `uw (S m)` along the
portion from the mark time to the portion stopping time is at most `4 * Lam`,
and that sum is integrable.  The bound comes from the discrete Green function of
the window, which turns the pointwise weight into a discrete supersolution and
lets Claim T' apply. -/
theorem LogGridSumBound {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (𝒢 : Filtration ℕ m0)
    (S : ℕ → Ω → ℤ) (σm tau' τ : Ω → ℕ)
    (aa bb qq : ℕ) (ε r Λ : ℝ) (uw : ℤ → ℝ)
    (hεr0 : (0:ℝ) < ε / r) (hbb0 : 0 < bb) (haa4 : 4 ≤ aa)
    (haaR : (0:ℝ) ≤ (aa:ℝ)) (haabbR : (0:ℝ) < (bb:ℝ) - (aa:ℝ))
    (hεrbb : (ε / r) * (bb:ℝ) = 8)
    (hΛd : Λ = 32 * Real.sqrt 8 + 8 * Real.log 8 ^ 2) (hΛ0 : (0:ℝ) ≤ Λ)
    (huwd : uw = fun i => if (aa:ℤ) < i ∧ i < (bb:ℤ)
      then (ε / r) ^ 2 * |Real.log ((ε / r) * (i:ℝ))| ^ 2 else 0)
    (hσst : IsStoppingTime 𝒢 (fun ω => (σm ω : ℕ∞)))
    (hσmeas : Measurable σm) (htau'meas : Measurable tau')
    (htau'τ : ∀ ω, tau' ω ≤ τ ω)
    (hτint : Integrable (fun ω => (τ ω : ℝ)) μ)
    (hSrange : ∀ n ω, (aa : ℤ) ≤ S n ω ∧ S n ω ≤ (qq : ℤ))
    (hstG : ∀ (ζ : Ω → ℕ), IsStoppingTime 𝒢 (fun ω => (ζ ω : ℕ∞)) →
      ∀ n : ℕ, MeasurableSet[𝒢 n] {ω | ζ ω ≤ n})
    (hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ,
      (∀ m, Measurable (G m)) → Measurable (fun ω => G (ζ ω) ω))
    (hrandidx2 : ∀ (ζ η : Ω → ℕ), Measurable ζ → Measurable η →
      ∀ G : ℕ → ℕ → Ω → ℝ, (∀ n m, Measurable (G n m)) →
      Measurable (fun ω => G (ζ ω) (η ω) ω))
    (hbddg : ∀ g : ℤ → ℝ, ∃ C : ℝ, ∀ i : ℤ, (aa:ℤ) ≤ i → i ≤ (qq:ℤ) → |g i| ≤ C)
    (hgSmeas : ∀ (g : ℤ → ℝ) (k : ℕ), Measurable (fun ω => g (S k ω)))
    (claimT : ∀ (hf uf : ℤ → ℝ) (A : Set Ω), (∀ i : ℤ, 0 ≤ uf i) →
      (∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) →
        (hf (i + 1) + hf (i - 1)) / 2 - hf i ≤ -(uf i)) →
      MeasurableSet A → (∀ n : ℕ, MeasurableSet[𝒢 n] (A ∩ {ω | σm ω ≤ n})) →
      ∀ n : ℕ,
        ∫ ω, Set.indicator A (fun _ => (1:ℝ)) ω *
            (hf (S (min (max (σm ω) n) (tau' ω)) ω)
              + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)) ∂μ
          ≤ ∫ ω, Set.indicator A (fun _ => (1:ℝ)) ω * hf (S (σm ω) ω) ∂μ) :
    Integrable (fun ω => ∑ m ∈ Finset.Ico (σm ω) (tau' ω), uw (S m ω)) μ ∧
      ∫ ω, (∑ m ∈ Finset.Ico (σm ω) (tau' ω), uw (S m ω)) ∂μ ≤ 4 * Λ := by
  obtain ⟨hharm, hlogbd⟩ := SqrtSumLogSquareBounds
  have huw0 : ∀ i : ℤ, 0 ≤ uw i := by
    intro i
    simp only [huwd]
    by_cases hc : (aa:ℤ) < i ∧ i < (bb:ℤ)
    · rw [if_pos hc]; positivity
    · rw [if_neg hc]
  have huwzero : ∀ i : ℤ, ¬ ((aa:ℤ) < i ∧ i < (bb:ℤ)) → uw i = 0 := by
    intro i hc
    simp only [huwd]
    rw [if_neg hc]
  have hUW : ∑ m ∈ Finset.range bb, uw ((m : ℕ) : ℤ) ≤ (ε / r) * Λ := by
    obtain ⟨bb', hbb'⟩ : ∃ k : ℕ, bb = k + 1 := ⟨bb - 1, by
      have h1 : 0 < bb := hbb0
      omega⟩
    have hbound : ∀ m ∈ Finset.range bb, uw ((m : ℕ) : ℤ)
        ≤ ((ε / r) ^ 2 * 16) * (1 / Real.sqrt ((ε / r) * (m : ℝ)))
          + (ε / r) ^ 2 * Real.log 8 ^ 2 := by
      intro m hm
      by_cases hc : (aa:ℤ) < ((m : ℕ) : ℤ) ∧ ((m : ℕ) : ℤ) < (bb:ℤ)
      · have hm0 : (0:ℝ) < (m:ℝ) := by
          have h1 : (4:ℤ) ≤ (aa:ℤ) := by exact_mod_cast haa4
          have h2 : (0:ℤ) < ((m : ℕ) : ℤ) := by omega
          have h3 : (0:ℕ) < m := by exact_mod_cast h2
          exact_mod_cast h3
        have hs0 : (0:ℝ) < (ε / r) * (m:ℝ) := by positivity
        have hs8 : (ε / r) * (m:ℝ) ≤ 8 := by
          have h4 : ((m:ℕ):ℝ) ≤ (bb:ℝ) := by
            have h5 : ((m : ℕ) : ℤ) ≤ (bb:ℤ) := by omega
            exact_mod_cast h5
          calc (ε / r) * (m:ℝ) ≤ (ε / r) * (bb:ℝ) :=
                mul_le_mul_of_nonneg_left h4 hεr0.le
            _ = 8 := hεrbb
        have h6 := hlogbd ((ε / r) * (m:ℝ)) hs0 hs8
        have h7 : (0:ℝ) ≤ (ε / r) ^ 2 := sq_nonneg _
        have h8 := mul_le_mul_of_nonneg_left h6 h7
        simp only [huwd]
        rw [if_pos hc]
        calc (ε / r) ^ 2 * |Real.log ((ε / r) * (m:ℝ))| ^ 2
            ≤ (ε / r) ^ 2 * (16 / Real.sqrt ((ε / r) * (m:ℝ)) + Real.log 8 ^ 2) := h8
          _ = ((ε / r) ^ 2 * 16) * (1 / Real.sqrt ((ε / r) * (m:ℝ)))
              + (ε / r) ^ 2 * Real.log 8 ^ 2 := by ring
      · rw [huwzero _ hc]
        have h1 : (0:ℝ) ≤ ((ε / r) ^ 2 * 16) * (1 / Real.sqrt ((ε / r) * (m : ℝ))) := by
          positivity
        have h2 : (0:ℝ) ≤ (ε / r) ^ 2 * Real.log 8 ^ 2 := by positivity
        linarith only [h1, h2]
    have hsplit : ∑ m ∈ Finset.range bb,
        (((ε / r) ^ 2 * 16) * (1 / Real.sqrt ((ε / r) * (m : ℝ)))
          + (ε / r) ^ 2 * Real.log 8 ^ 2)
        = ((ε / r) ^ 2 * 16) * (∑ m ∈ Finset.range bb, 1 / Real.sqrt ((ε / r) * (m : ℝ)))
          + (bb : ℝ) * ((ε / r) ^ 2 * Real.log 8 ^ 2) := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        ← Finset.mul_sum]
    have hshift : ∑ m ∈ Finset.range bb, 1 / Real.sqrt ((ε / r) * (m : ℝ))
        ≤ 2 * Real.sqrt ((ε / r) * (bb' : ℝ)) / (ε / r) := by
      rw [hbb', Finset.sum_range_succ']
      simp only [Nat.cast_zero, mul_zero, Real.sqrt_zero, div_zero, add_zero]
      have he : ∀ m ∈ Finset.range bb', 1 / Real.sqrt ((ε / r) * ((m + 1 : ℕ) : ℝ))
          = 1 / Real.sqrt ((ε / r) * ((m : ℝ) + 1)) := by
        intro m _
        push_cast
        ring_nf
      rw [Finset.sum_congr rfl he]
      exact hharm (ε / r) hεr0 bb'
    have hfinal : ((ε / r) ^ 2 * 16) * (2 * Real.sqrt ((ε / r) * (bb' : ℝ)) / (ε / r))
        + (bb : ℝ) * ((ε / r) ^ 2 * Real.log 8 ^ 2) ≤ (ε / r) * Λ := by
      have h1 : Real.sqrt ((ε / r) * (bb' : ℝ)) ≤ Real.sqrt 8 := by
        refine Real.sqrt_le_sqrt ?_
        have h2 : (bb' : ℝ) ≤ (bb : ℝ) := by
          rw [hbb']; push_cast; linarith only []
        have h3 : (ε / r) * (bb' : ℝ) ≤ (ε / r) * (bb : ℝ) :=
          mul_le_mul_of_nonneg_left h2 hεr0.le
        linarith only [h3, hεrbb]
      have h4 : ((ε / r) ^ 2 * 16) * (2 * Real.sqrt ((ε / r) * (bb' : ℝ)) / (ε / r))
          = 32 * (ε / r) * Real.sqrt ((ε / r) * (bb' : ℝ)) := by
        field_simp
        ring
      have h5 : (bb : ℝ) * ((ε / r) ^ 2 * Real.log 8 ^ 2)
          = 8 * (ε / r) * Real.log 8 ^ 2 := by
        calc (bb : ℝ) * ((ε / r) ^ 2 * Real.log 8 ^ 2)
            = ((ε / r) * (bb : ℝ)) * ((ε / r) * Real.log 8 ^ 2) := by ring
          _ = 8 * ((ε / r) * Real.log 8 ^ 2) := by rw [hεrbb]
          _ = 8 * (ε / r) * Real.log 8 ^ 2 := by ring
      rw [h4, h5, hΛd]
      have h6 : (0:ℝ) ≤ Real.sqrt 8 := Real.sqrt_nonneg 8
      have h7 : 32 * (ε / r) * Real.sqrt ((ε / r) * (bb' : ℝ))
          ≤ 32 * (ε / r) * Real.sqrt 8 :=
        mul_le_mul_of_nonneg_left h1 (by linarith only [hεr0])
      nlinarith only [h7]
    calc ∑ m ∈ Finset.range bb, uw ((m : ℕ) : ℤ)
        ≤ ∑ m ∈ Finset.range bb,
            (((ε / r) ^ 2 * 16) * (1 / Real.sqrt ((ε / r) * (m : ℝ)))
              + (ε / r) ^ 2 * Real.log 8 ^ 2) := Finset.sum_le_sum hbound
      _ = ((ε / r) ^ 2 * 16) * (∑ m ∈ Finset.range bb, 1 / Real.sqrt ((ε / r) * (m : ℝ)))
            + (bb : ℝ) * ((ε / r) ^ 2 * Real.log 8 ^ 2) := hsplit
      _ ≤ ((ε / r) ^ 2 * 16) * (2 * Real.sqrt ((ε / r) * (bb' : ℝ)) / (ε / r))
            + (bb : ℝ) * ((ε / r) ^ 2 * Real.log 8 ^ 2) := by
          have h9 : (0:ℝ) ≤ (ε / r) ^ 2 * 16 := by positivity
          have h10 := mul_le_mul_of_nonneg_left hshift h9
          linarith only [h10]
      _ ≤ (ε / r) * Λ := hfinal
  -- the Green function of the portion's time walk
  obtain ⟨Kf, hKfd⟩ : ∃ f : ℤ → ℤ → ℝ, f = fun i m =>
      if (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ) then
        (((min i m : ℤ) : ℝ) - (aa:ℝ)) * ((bb:ℝ) - ((max i m : ℤ) : ℝ))
          / ((bb:ℝ) - (aa:ℝ))
      else 0 := ⟨_, rfl⟩
  have hKfnn : ∀ i m : ℤ, (aa:ℤ) ≤ m → m ≤ (bb:ℤ) → 0 ≤ Kf i m := by
    intro i m h1 h2
    simp only [hKfd]
    by_cases hc : (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ)
    · rw [if_pos hc]
      have e1 : (aa:ℤ) ≤ min i m := le_min hc.1 h1
      have e2 : max i m ≤ (bb:ℤ) := max_le hc.2 h2
      have e3 : (aa:ℝ) ≤ ((min i m : ℤ) : ℝ) := by exact_mod_cast e1
      have e4 : ((max i m : ℤ) : ℝ) ≤ (bb:ℝ) := by exact_mod_cast e2
      have e5 : (0:ℝ) ≤ ((min i m : ℤ) : ℝ) - (aa:ℝ) := by linarith only [e3]
      have e6 : (0:ℝ) ≤ (bb:ℝ) - ((max i m : ℤ) : ℝ) := by linarith only [e4]
      exact div_nonneg (mul_nonneg e5 e6) haabbR.le
    · rw [if_neg hc]
  have hKfbd : ∀ i m : ℤ, (aa:ℤ) ≤ m → m ≤ (bb:ℤ) →
      Kf i m ≤ ((bb:ℝ) - (aa:ℝ)) / 4 := by
    intro i m h1 h2
    simp only [hKfd]
    by_cases hc : (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ)
    · rw [if_pos hc]
      have e1 : (aa:ℤ) ≤ min i m := le_min hc.1 h1
      have e2 : max i m ≤ (bb:ℤ) := max_le hc.2 h2
      have e7 : min i m ≤ max i m := min_le_max
      have e3 : (aa:ℝ) ≤ ((min i m : ℤ) : ℝ) := by exact_mod_cast e1
      have e4 : ((max i m : ℤ) : ℝ) ≤ (bb:ℝ) := by exact_mod_cast e2
      have e8 : ((min i m : ℤ) : ℝ) ≤ ((max i m : ℤ) : ℝ) := by exact_mod_cast e7
      rw [div_le_div_iff₀ haabbR (by norm_num : (0:ℝ) < 4)]
      nlinarith only [e3, e4, e8, haabbR,
        sq_nonneg ((((min i m : ℤ) : ℝ) - (aa:ℝ)) - ((bb:ℝ) - ((max i m : ℤ) : ℝ)))]
    · rw [if_neg hc]
      linarith only [haabbR]
  have hKfpoi : ∀ i m : ℤ, (aa:ℤ) < i → i < (bb:ℤ) → (aa:ℤ) ≤ m → m ≤ (bb:ℤ) →
      (Kf (i + 1) m + Kf (i - 1) m) / 2 - Kf i m = (if m = i then -(1/2) else 0) := by
    intro i m h1 h2 h3 h4
    have hqne : ((bb:ℝ) - (aa:ℝ)) ≠ 0 := ne_of_gt haabbR
    simp only [hKfd]
    rw [if_pos (⟨by omega, by omega⟩ : (aa:ℤ) ≤ i + 1 ∧ i + 1 ≤ (bb:ℤ)),
      if_pos (⟨by omega, by omega⟩ : (aa:ℤ) ≤ i - 1 ∧ i - 1 ≤ (bb:ℤ)),
      if_pos (⟨by omega, by omega⟩ : (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ))]
    rcases lt_trichotomy m i with hc | hc | hc
    · rw [if_neg (by omega)]
      simp only [min_eq_right (show m ≤ i + 1 by omega), min_eq_right (show m ≤ i - 1 by omega),
        min_eq_right (show m ≤ i by omega), max_eq_left (show m ≤ i + 1 by omega),
        max_eq_left (show m ≤ i - 1 by omega), max_eq_left (show m ≤ i by omega)]
      push_cast
      field_simp
      ring
    · subst hc
      rw [if_pos rfl]
      simp only [min_eq_right (show m ≤ m + 1 by omega), max_eq_left (show m ≤ m + 1 by omega),
        min_eq_left (show m - 1 ≤ m by omega), max_eq_right (show m - 1 ≤ m by omega),
        min_self, max_self]
      push_cast
      field_simp
      ring
    · rw [if_neg (by omega)]
      simp only [min_eq_left (show i + 1 ≤ m by omega), min_eq_left (show i - 1 ≤ m by omega),
        min_eq_left (show i ≤ m by omega), max_eq_right (show i + 1 ≤ m by omega),
        max_eq_right (show i - 1 ≤ m by omega), max_eq_right (show i ≤ m by omega)]
      push_cast
      field_simp
      ring
  obtain ⟨hG, hGd⟩ : ∃ f : ℤ → ℝ, f = fun i =>
      ∑ m ∈ Finset.range (bb + 1), 2 * uw ((m : ℕ) : ℤ) * Kf i ((m : ℕ) : ℤ) := ⟨_, rfl⟩
  have hGnn : ∀ i : ℤ, 0 ≤ hG i := by
    intro i
    simp only [hGd]
    refine Finset.sum_nonneg (fun m hm => ?_)
    by_cases hc : (aa:ℤ) < ((m : ℕ) : ℤ) ∧ ((m : ℕ) : ℤ) < (bb:ℤ)
    · have h1 := huw0 ((m : ℕ) : ℤ)
      have h2 := hKfnn i ((m : ℕ) : ℤ) (by omega) (by omega)
      exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
    · rw [huwzero _ hc]
      simp
  have hGpoi : ∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) →
      (hG (i + 1) + hG (i - 1)) / 2 - hG i ≤ -(uw i) := by
    intro i h1 h2
    have hkey : (hG (i + 1) + hG (i - 1)) / 2 - hG i
        = ∑ m ∈ Finset.range (bb + 1),
          (if ((m : ℕ) : ℤ) = i then -(uw ((m : ℕ) : ℤ)) else 0) := by
      simp only [hGd]
      rw [← Finset.sum_add_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      have halg : (2 * uw ((m : ℕ) : ℤ) * Kf (i + 1) ((m : ℕ) : ℤ)
            + 2 * uw ((m : ℕ) : ℤ) * Kf (i - 1) ((m : ℕ) : ℤ)) / 2
          - 2 * uw ((m : ℕ) : ℤ) * Kf i ((m : ℕ) : ℤ)
          = 2 * uw ((m : ℕ) : ℤ) * ((Kf (i + 1) ((m : ℕ) : ℤ)
            + Kf (i - 1) ((m : ℕ) : ℤ)) / 2 - Kf i ((m : ℕ) : ℤ)) := by ring
      rw [halg]
      by_cases hc : (aa:ℤ) < ((m : ℕ) : ℤ) ∧ ((m : ℕ) : ℤ) < (bb:ℤ)
      · rw [hKfpoi i ((m : ℕ) : ℤ) h1 h2 (by omega) (by omega)]
        by_cases hc2 : ((m : ℕ) : ℤ) = i
        · rw [if_pos hc2, if_pos hc2]; ring
        · rw [if_neg hc2, if_neg hc2]; ring
      · rw [huwzero _ hc]
        by_cases hc2 : ((m : ℕ) : ℤ) = i
        · rw [if_pos hc2]
          rw [hc2] at hc
          exact absurd ⟨h1, h2⟩ hc
        · rw [if_neg hc2]; ring
    have hcollapse : ∑ m ∈ Finset.range (bb + 1),
        (if ((m : ℕ) : ℤ) = i then -(uw ((m : ℕ) : ℤ)) else 0) = -(uw i) := by
      have he : ∀ m ∈ Finset.range (bb + 1),
          (if ((m : ℕ) : ℤ) = i then -(uw ((m : ℕ) : ℤ)) else 0)
          = (if m = i.toNat then -(uw ((m : ℕ) : ℤ)) else 0) := by
        intro m _
        by_cases hc : ((m : ℕ) : ℤ) = i
        · rw [if_pos hc, if_pos (by omega)]
        · rw [if_neg hc, if_neg (by omega)]
      have hi0 : (0:ℤ) ≤ i := by
        have h3 : (0:ℤ) ≤ (aa:ℤ) := Int.natCast_nonneg aa
        omega
      rw [Finset.sum_congr rfl he,
        Finset.sum_ite_eq' (Finset.range (bb + 1)) i.toNat
          (fun m => -(uw ((m : ℕ) : ℤ))),
        if_pos (Finset.mem_range.mpr (by omega))]
      congr 1
      congr 1
      omega
    rw [hkey, hcollapse]
  have hGbd : ∀ i : ℤ, hG i ≤ 4 * Λ := by
    intro i
    have hstep : ∑ m ∈ Finset.range (bb + 1), 2 * uw ((m : ℕ) : ℤ) * Kf i ((m : ℕ) : ℤ)
        ≤ ∑ m ∈ Finset.range (bb + 1),
          2 * uw ((m : ℕ) : ℤ) * (((bb:ℝ) - (aa:ℝ)) / 4) := by
      refine Finset.sum_le_sum (fun m hm => ?_)
      by_cases hc : (aa:ℤ) < ((m : ℕ) : ℤ) ∧ ((m : ℕ) : ℤ) < (bb:ℤ)
      · have h1 := hKfbd i ((m : ℕ) : ℤ) (by omega) (by omega)
        have h2 := huw0 ((m : ℕ) : ℤ)
        nlinarith only [h1, h2]
      · rw [huwzero _ hc]
        simp
    have heq : ∑ m ∈ Finset.range (bb + 1), 2 * uw ((m : ℕ) : ℤ) * (((bb:ℝ) - (aa:ℝ)) / 4)
        = (2 * (((bb:ℝ) - (aa:ℝ)) / 4)) * ∑ m ∈ Finset.range (bb + 1), uw ((m : ℕ) : ℤ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    have hsumbb : ∑ m ∈ Finset.range (bb + 1), uw ((m : ℕ) : ℤ)
        = ∑ m ∈ Finset.range bb, uw ((m : ℕ) : ℤ) := by
      rw [Finset.sum_range_succ, huwzero ((bb : ℕ) : ℤ) (by omega), add_zero]
    have hfin : (2 * (((bb:ℝ) - (aa:ℝ)) / 4)) * ∑ m ∈ Finset.range bb, uw ((m : ℕ) : ℤ)
        ≤ 4 * Λ := by
      have h1 : (0:ℝ) ≤ 2 * (((bb:ℝ) - (aa:ℝ)) / 4) := by linarith only [haabbR]
      have h2 := mul_le_mul_of_nonneg_left hUW h1
      have h3 : (2 * (((bb:ℝ) - (aa:ℝ)) / 4)) * ((ε / r) * Λ) ≤ 4 * Λ := by
        have h4 : (ε / r) * (bb:ℝ) = 8 := hεrbb
        have h5 : (0:ℝ) ≤ (aa:ℝ) := haaR
        have h6 : (0:ℝ) ≤ Λ := hΛ0
        have h7 : (2 * (((bb:ℝ) - (aa:ℝ)) / 4)) * ((ε / r) * Λ)
            = (((ε / r) * (bb:ℝ)) / 2) * Λ - (((ε / r) * (aa:ℝ)) / 2) * Λ := by ring
        rw [h7, h4]
        have h8 : (0:ℝ) ≤ (((ε / r) * (aa:ℝ)) / 2) * Λ := by positivity
        linarith only [h8]
      linarith only [h2, h3]
    simp only [hGd]
    rw [hsumbb] at heq
    linarith only [hstep, heq, hfin]
  -- the portion's logarithmic sum
  obtain ⟨Cuw, hCuw⟩ := hbddg uw
  have hCuw0 : (0:ℝ) ≤ |Cuw| := abs_nonneg Cuw
  have huwsummeas : ∀ n : ℕ, Measurable (fun ω =>
      ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)) := fun n =>
    hrandidx2 (σm) tau' hσmeas htau'meas
      (fun i m ω => ∑ k ∈ Finset.Ico i (min n m), uw (S k ω))
      (fun i m => Finset.measurable_sum _ (fun k _ => hgSmeas uw k))
  have huwsummeas' : Measurable (fun ω =>
      ∑ m ∈ Finset.Ico (σm ω) (tau' ω), uw (S m ω)) :=
    hrandidx2 (σm) tau' hσmeas htau'meas
      (fun i m ω => ∑ k ∈ Finset.Ico i m, uw (S k ω))
      (fun i m => Finset.measurable_sum _ (fun k _ => hgSmeas uw k))
  have huwsumbd : ∀ (n : ℕ) (ω : Ω),
      |∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)| ≤ ((τ ω : ℕ):ℝ) * |Cuw| := by
    intro n ω
    have h1 : |∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)|
        ≤ ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), |uw (S m ω)| :=
      Finset.abs_sum_le_sum_abs _ _
    have h2 : ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), |uw (S m ω)|
        ≤ ∑ _m ∈ Finset.Ico (σm ω) (min n (tau' ω)), |Cuw| := by
      refine Finset.sum_le_sum (fun m _ => ?_)
      obtain ⟨e1, e2⟩ := hSrange m ω
      exact le_trans (hCuw _ e1 e2) (le_abs_self Cuw)
    rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul] at h2
    have h3 : ((min n (tau' ω) - σm ω : ℕ) : ℝ) ≤ ((τ ω : ℕ):ℝ) := by
      have h4 : min n (tau' ω) - σm ω ≤ τ ω := by
        have := htau'τ ω; omega
      exact_mod_cast h4
    calc |∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)|
        ≤ ((min n (tau' ω) - σm ω : ℕ) : ℝ) * |Cuw| := le_trans h1 h2
      _ ≤ ((τ ω : ℕ):ℝ) * |Cuw| := mul_le_mul_of_nonneg_right h3 hCuw0
  have huwsumint : ∀ n : ℕ, Integrable (fun ω =>
      ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)) μ := by
    intro n
    refine Integrable.mono' (hτint.mul_const |Cuw|) (huwsummeas n).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    exact huwsumbd n ω
  have huwsumint' : Integrable (fun ω =>
      ∑ m ∈ Finset.Ico (σm ω) (tau' ω), uw (S m ω)) μ := by
    refine Integrable.mono' (hτint.mul_const |Cuw|) huwsummeas'.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs]
    have h1 := huwsumbd (tau' ω) ω
    have h2 : min (tau' ω) (tau' ω) = tau' ω := by omega
    rw [h2] at h1
    exact h1
  have hlogsum : ∫ ω, (∑ m ∈ Finset.Ico (σm ω) (tau' ω), uw (S m ω)) ∂μ ≤ 4 * Λ := by
    have hcl := claimT hG uw Set.univ huw0 hGpoi MeasurableSet.univ
      (fun n => by
        have he : (Set.univ : Set Ω) ∩ {ω | σm ω ≤ n} = {ω | σm ω ≤ n} := by
          rw [Set.univ_inter]
        rw [he]
        exact hstG (σm) hσst n)
    have hind1 : ∀ ω, Set.indicator (Set.univ : Set Ω) (fun _ => (1:ℝ)) ω = 1 := by
      intro ω
      rw [Set.indicator_of_mem (Set.mem_univ ω)]
    have hpartial : ∀ n : ℕ,
        ∫ ω, (∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)) ∂μ ≤ 4 * Λ := by
      intro n
      have h1 := hcl n
      simp only [hind1, one_mul] at h1
      have hintL : Integrable (fun ω => hG (S (min (max (σm ω) n) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)) μ := by
        have hm1 : Measurable (fun ω => hG (S (min (max (σm ω) n) (tau' ω)) ω)) :=
          hrandidx2 (σm) tau' hσmeas htau'meas
            (fun i m ω => hG (S (min (max i n) m) ω)) (fun i m => hgSmeas _ _)
        obtain ⟨ChG, hChG⟩ := hbddg hG
        refine Integrable.add ?_ (huwsumint n)
        refine Integrable.mono' (integrable_const |ChG|) hm1.aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        obtain ⟨e1, e2⟩ := hSrange (min (max (σm ω) n) (tau' ω)) ω
        rw [Real.norm_eq_abs]
        exact le_trans (hChG _ e1 e2) (le_abs_self ChG)
      have hmono2 : ∫ ω, (∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)) ∂μ
          ≤ ∫ ω, (hG (S (min (max (σm ω) n) (tau' ω)) ω)
            + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uw (S m ω)) ∂μ := by
        refine integral_mono (huwsumint n) hintL (fun ω => ?_)
        have h3 := hGnn (S (min (max (σm ω) n) (tau' ω)) ω)
        linarith only [h3]
      have hRbd : ∫ ω, hG (S (σm ω) ω) ∂μ ≤ 4 * Λ := by
        have hintR : Integrable (fun ω => hG (S (σm ω) ω)) μ := by
          obtain ⟨ChG, hChG⟩ := hbddg hG
          refine Integrable.mono' (integrable_const |ChG|)
            (hrandidx (σm) hσmeas (fun m ω => hG (S m ω))
              (fun m => hgSmeas _ _)).aestronglyMeasurable
            (Filter.Eventually.of_forall (fun ω => ?_))
          obtain ⟨e1, e2⟩ := hSrange (σm ω) ω
          rw [Real.norm_eq_abs]
          exact le_trans (hChG _ e1 e2) (le_abs_self ChG)
        calc ∫ ω, hG (S (σm ω) ω) ∂μ ≤ ∫ _ω, (4 * Λ) ∂μ :=
              integral_mono hintR (integrable_const _) (fun ω => hGbd (S (σm ω) ω))
          _ = 4 * Λ := by rw [integral_const]; simp
      linarith only [hmono2, hRbd, h1]
    refine le_of_tendsto (MeasureTheory.integral_tendsto_of_tendsto_of_monotone
      huwsumint huwsumint' ?_ ?_) (Filter.Eventually.of_forall hpartial)
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      intro a b hab
      show ∑ m ∈ Finset.Ico (σm ω) (min a (tau' ω)), uw (S m ω)
          ≤ ∑ m ∈ Finset.Ico (σm ω) (min b (tau' ω)), uw (S m ω)
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => huw0 _)
      refine Finset.Ico_subset_Ico le_rfl ?_
      omega
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      refine tendsto_atTop_of_eventually_const (i₀ := tau' ω) (fun n hn => ?_)
      have e1 : min n (tau' ω) = tau' ω := by omega
      rw [e1]
  exact ⟨huwsumint', hlogsum⟩
