module

public import InfHarmonic.Preamble

@[expose] public section
open Set Filter Topology MeasureTheory

/-- Step 6(a) of paper Proposition 6.7: the expected number of steps in a
portion of the lattice time walk is at most `bb² / 4`.

The walk itself is abstracted away. What is left is a probability space with an
integer process `S`, three `ℕ`-valued indices `σm ≤ tau' ≤ τ` --- the mark, the
end of the portion and the global stopping time --- and the window bounds
`aa < S n < bb`, valid for the steps `n` of the portion. The supersolution
bound of \noderef{StoppedLatticeSupersolutionBound}, specialized to the whole
space, enters as the hypothesis `hclaim`: for every discrete supersolution
pair `(hf, uf)` on the window it compares the stopped value plus the
accumulated defect with the value at the mark. The generic
random-index measurability lemmas `hrandidx`, `hrandidx2` and `hgSmeas` enter
the same way.

Then the portion length `tau' - σm` is integrable and
\[
  ∫ (tau' - σm) \le bb^2 / 4 .
\]
Both facts are returned, because the application reads the integrability again
when it assembles the time budget.

The proof is the paper's: test `hclaim` with the concave parabola
`hf i = (bb - i)(i - aa)` on `[aa, bb]` and the window indicator
`uf i = 1_{(aa,bb)}(i)`, whose discrete Laplacian is `-1` on the window; the
accumulated defect along the portion is then exactly the number of steps up to
the horizon `n`, and `hf ≤ bb²/4` bounds the boundary term. Letting
`n → ∞` through the monotone truncations `min n (tau')` gives the bound for the
whole portion. Integrability throughout is by domination: the truncated
lengths are at most `τ`, which is integrable by hypothesis. -/
theorem ExpectedPortionLengthBound {Ω : Type*} {m0 : MeasurableSpace Ω}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (S : ℕ → Ω → ℤ)
    (τ σm tau' : Ω → ℕ) (aa bb : ℕ)
    (hσmeas : Measurable σm) (htau'meas : Measurable tau')
    (htau'τ : ∀ ω, tau' ω ≤ τ ω)
    (hτint : Integrable (fun ω => ((τ ω : ℕ) : ℝ)) μ)
    (hrandidx : ∀ (ζ : Ω → ℕ), Measurable ζ → ∀ G : ℕ → Ω → ℝ, (∀ m, Measurable (G m)) →
      Measurable (fun ω => G (ζ ω) ω))
    (hrandidx2 : ∀ (ζ η : Ω → ℕ), Measurable ζ → Measurable η →
      ∀ G : ℕ → ℕ → Ω → ℝ, (∀ n m, Measurable (G n m)) →
      Measurable (fun ω => G (ζ ω) (η ω) ω))
    (hgSmeas : ∀ (g : ℤ → ℝ) (k : ℕ), Measurable (fun ω => g (S k ω)))
    (hSwin : ∀ (n : ℕ) (ω : Ω), σm ω ≤ n → n < tau' ω →
      (aa:ℤ) < S n ω ∧ S n ω < (bb:ℤ))
    (hclaim : ∀ hf uf : ℤ → ℝ, (∀ i : ℤ, 0 ≤ uf i) →
      (∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) →
        (hf (i + 1) + hf (i - 1)) / 2 - hf i ≤ -(uf i)) →
      ∀ n : ℕ,
        ∫ ω, (hf (S (min (max (σm ω) n) (tau' ω)) ω)
            + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), uf (S m ω)) ∂μ
          ≤ ∫ ω, hf (S (σm ω) ω) ∂μ) :
    Integrable (fun ω => ((tau' ω - σm ω : ℕ) : ℝ)) μ ∧
      ∫ ω, ((tau' ω - σm ω : ℕ) : ℝ) ∂μ ≤ (bb:ℝ) ^ 2 / 4 := by
  -- ===== Step 6(a): the number of portion steps. =====
  have haaR : (0:ℝ) ≤ (aa:ℝ) := Nat.cast_nonneg aa
  have hnstmeas : Measurable (fun ω => ((tau' ω - σm ω : ℕ) : ℝ)) :=
    hrandidx2 (σm) tau' hσmeas htau'meas (fun i m _ => ((m - i : ℕ) : ℝ))
      (fun i m => measurable_const)
  have hnstint : Integrable (fun ω => ((tau' ω - σm ω : ℕ) : ℝ)) μ := by
    refine Integrable.mono' hτint hnstmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    have h1 : tau' ω - σm ω ≤ τ ω := by
      have := htau'τ ω; omega
    have h2 : ((tau' ω - σm ω : ℕ) : ℝ) ≤ ((τ ω : ℕ) : ℝ) := by exact_mod_cast h1
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact h2
  have htimebudget : ∫ ω, ((tau' ω - σm ω : ℕ) : ℝ) ∂μ ≤ (bb:ℝ) ^ 2 / 4 := by
    obtain ⟨h1f, h1fd⟩ : ∃ f : ℤ → ℝ, f = fun i =>
        if (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ) then ((bb:ℝ) - (i:ℝ)) * ((i:ℝ) - (aa:ℝ)) else 0 := ⟨_, rfl⟩
    obtain ⟨u1f, u1fd⟩ : ∃ f : ℤ → ℝ, f = fun i =>
        if (aa:ℤ) < i ∧ i < (bb:ℤ) then (1:ℝ) else 0 := ⟨_, rfl⟩
    have hu10 : ∀ i : ℤ, 0 ≤ u1f i := by
      intro i; simp only [u1fd]
      by_cases hc : (aa:ℤ) < i ∧ i < (bb:ℤ)
      · rw [if_pos hc]; norm_num
      · rw [if_neg hc]
    have hh10 : ∀ i : ℤ, 0 ≤ h1f i := by
      intro i; simp only [h1fd]
      by_cases hc : (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ)
      · rw [if_pos hc]
        have e1 : (i:ℝ) ≤ (bb:ℝ) := by exact_mod_cast hc.2
        have e2 : (aa:ℝ) ≤ (i:ℝ) := by exact_mod_cast hc.1
        have e3 : (0:ℝ) ≤ (bb:ℝ) - (i:ℝ) := by linarith only [e1]
        have e4 : (0:ℝ) ≤ (i:ℝ) - (aa:ℝ) := by linarith only [e2]
        positivity
      · rw [if_neg hc]
    have hh1bd : ∀ i : ℤ, h1f i ≤ (bb:ℝ) ^ 2 / 4 := by
      intro i
      simp only [h1fd]
      by_cases hc : (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ)
      · rw [if_pos hc]
        have e1 : (i:ℝ) ≤ (bb:ℝ) := by exact_mod_cast hc.2
        have e2 : (aa:ℝ) ≤ (i:ℝ) := by exact_mod_cast hc.1
        nlinarith only [e1, e2, haaR, sq_nonneg ((bb:ℝ) - 2 * (i:ℝ)), sq_nonneg (i:ℝ)]
      · rw [if_neg hc]
        positivity
    have hpoi1 : ∀ i : ℤ, (aa:ℤ) < i → i < (bb:ℤ) →
        (h1f (i + 1) + h1f (i - 1)) / 2 - h1f i ≤ -(u1f i) := by
      intro i h1 h2
      simp only [h1fd, u1fd]
      rw [if_pos (⟨by omega, by omega⟩ : (aa:ℤ) ≤ i + 1 ∧ i + 1 ≤ (bb:ℤ)),
        if_pos (⟨by omega, by omega⟩ : (aa:ℤ) ≤ i - 1 ∧ i - 1 ≤ (bb:ℤ)),
        if_pos (⟨by omega, by omega⟩ : (aa:ℤ) ≤ i ∧ i ≤ (bb:ℤ)), if_pos ⟨h1, h2⟩]
      push_cast
      ring_nf
      norm_num
    have hcl := hclaim h1f u1f hu10 hpoi1
    have hpartial : ∀ n : ℕ,
        ∫ ω, ((min n (tau' ω) - σm ω : ℕ) : ℝ) ∂μ ≤ (bb:ℝ) ^ 2 / 4 := by
      intro n
      have h1 := hcl n
      have hsum : ∀ ω, ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), u1f (S m ω)
          = ((min n (tau' ω) - σm ω : ℕ) : ℝ) := by
        intro ω
        have he : ∀ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), u1f (S m ω) = 1 := by
          intro m hm
          obtain ⟨hm1, hm2⟩ := Finset.mem_Ico.mp hm
          obtain ⟨e1, e2⟩ := hSwin m ω hm1 (by omega)
          simp only [u1fd]
          rw [if_pos ⟨e1, e2⟩]
        rw [Finset.sum_congr rfl he, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
      have h2 : ∀ ω, h1f (S (min (max (σm ω) n) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), u1f (S m ω)
          ≥ ((min n (tau' ω) - σm ω : ℕ) : ℝ) := by
        intro ω
        rw [hsum ω]
        have h3 := hh10 (S (min (max (σm ω) n) (tau' ω)) ω)
        linarith only [h3]
      have hintL : Integrable (fun ω => h1f (S (min (max (σm ω) n) (tau' ω)) ω)
          + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), u1f (S m ω)) μ := by
        have hm1 : Measurable (fun ω => h1f (S (min (max (σm ω) n) (tau' ω)) ω)) :=
          hrandidx2 (σm) tau' hσmeas htau'meas
            (fun i m ω => h1f (S (min (max i n) m) ω)) (fun i m => hgSmeas _ _)
        have hm2 : Measurable (fun ω =>
            ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), u1f (S m ω)) :=
          hrandidx2 (σm) tau' hσmeas htau'meas
            (fun i m ω => ∑ k ∈ Finset.Ico i (min n m), u1f (S k ω))
            (fun i m => Finset.measurable_sum _ (fun k _ => hgSmeas u1f k))
        refine Integrable.mono' (integrable_const ((bb:ℝ) ^ 2 / 4 + (n:ℝ)))
          (hm1.add hm2).aestronglyMeasurable (Filter.Eventually.of_forall (fun ω => ?_))
        have e1 := hh10 (S (min (max (σm ω) n) (tau' ω)) ω)
        have e2 := hh1bd (S (min (max (σm ω) n) (tau' ω)) ω)
        rw [hsum ω]
        have e3 : ((min n (tau' ω) - σm ω : ℕ) : ℝ) ≤ (n:ℝ) := by
          have e4 : min n (tau' ω) - σm ω ≤ n := by omega
          exact_mod_cast e4
        have e5 : (0:ℝ) ≤ ((min n (tau' ω) - σm ω : ℕ) : ℝ) := by positivity
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith only [e1, e5])]
        linarith only [e2, e3]
      have hmono2 : ∫ ω, ((min n (tau' ω) - σm ω : ℕ) : ℝ) ∂μ
          ≤ ∫ ω, (h1f (S (min (max (σm ω) n) (tau' ω)) ω)
            + ∑ m ∈ Finset.Ico (σm ω) (min n (tau' ω)), u1f (S m ω)) ∂μ := by
        refine integral_mono ?_ hintL (fun ω => h2 ω)
        refine Integrable.mono' hτint
          (hrandidx2 (σm) tau' hσmeas htau'meas (fun i m _ => ((min n m - i : ℕ) : ℝ))
            (fun i m => measurable_const)).aestronglyMeasurable
          (Filter.Eventually.of_forall (fun ω => ?_))
        have e4 : min n (tau' ω) - σm ω ≤ τ ω := by
          have := htau'τ ω; omega
        have e5 : ((min n (tau' ω) - σm ω : ℕ) : ℝ) ≤ ((τ ω : ℕ) : ℝ) := by
          exact_mod_cast e4
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact e5
      have hRbd : ∫ ω, h1f (S (σm ω) ω) ∂μ ≤ (bb:ℝ) ^ 2 / 4 := by
        have hintR : Integrable (fun ω => h1f (S (σm ω) ω)) μ := by
          refine Integrable.mono' (integrable_const ((bb:ℝ) ^ 2 / 4))
            (hrandidx (σm) hσmeas (fun m ω => h1f (S m ω))
              (fun m => hgSmeas _ _)).aestronglyMeasurable
            (Filter.Eventually.of_forall (fun ω => ?_))
          have e1 := hh10 (S (σm ω) ω)
          have e2 := hh1bd (S (σm ω) ω)
          rw [Real.norm_eq_abs, abs_of_nonneg e1]
          exact e2
        calc ∫ ω, h1f (S (σm ω) ω) ∂μ
            ≤ ∫ _ω, ((bb:ℝ) ^ 2 / 4) ∂μ :=
              integral_mono hintR (integrable_const _)
                (fun ω => hh1bd (S (σm ω) ω))
          _ = (bb:ℝ) ^ 2 / 4 := by
              rw [integral_const]
              simp
      linarith only [hmono2, hRbd, h1]
    refine le_of_tendsto (MeasureTheory.integral_tendsto_of_tendsto_of_monotone ?_ hnstint ?_ ?_)
      (Filter.Eventually.of_forall hpartial)
    · intro n
      refine Integrable.mono' hτint
        (hrandidx2 (σm) tau' hσmeas htau'meas (fun i m _ => ((min n m - i : ℕ) : ℝ))
          (fun i m => measurable_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      have e4 : min n (tau' ω) - σm ω ≤ τ ω := by
        have := htau'τ ω; omega
      have e5 : ((min n (tau' ω) - σm ω : ℕ) : ℝ) ≤ ((τ ω : ℕ) : ℝ) := by
        exact_mod_cast e4
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact e5
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      intro a b hab
      show ((min a (tau' ω) - σm ω : ℕ) : ℝ) ≤ ((min b (tau' ω) - σm ω : ℕ) : ℝ)
      have e1 : min a (tau' ω) - σm ω ≤ min b (tau' ω) - σm ω := by omega
      exact_mod_cast e1
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      refine tendsto_atTop_of_eventually_const (i₀ := tau' ω) (fun n hn => ?_)
      have e1 : min n (tau' ω) = tau' ω := by omega
      rw [e1]
  exact ⟨hnstint, htimebudget⟩
