import InfHarmonic.Preamble
open Metric Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 3 of Lemma 5.2: once the slope functional is a maximum over one fixed
ball of positions for every slope in a ball, it is jointly continuous in the slope
and the triple, its infimum over all slopes is attained inside the slope ball, and
that infimum depends continuously on the triple. -/
theorem BaryGammaMinAttained (I : Set ℝ) (f : WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (S : Set (F × ℝ × ℝ)) (hSc : IsCompact S) (hSne : S.Nonempty)
    (hSadm : ∀ p ∈ S, 0 < p.2.2 ∧ p.2.1 ∈ I)
    (Λ₀ M : ℝ) (hΛ₀ : 0 ≤ Λ₀) (hM : 0 < M)
    (hsup : ∀ p ∈ S, ∀ A : F, BddAbove {w : ℝ | ∃ y : F,
      w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)})
    (hslope : ∀ p ∈ S, ∀ A : F,
      sSup {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
        ≤ sSup {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
            - inner ℝ (0 : F) (y - p.1)} + 1 →
      ‖A‖ ≤ Λ₀)
    (hball : ∀ p ∈ S, ∀ A : F, ‖A‖ ≤ Λ₀ + 1 →
      sSup {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
        = sSup ((fun y : F => f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
            - inner ℝ A (y - p.1)) '' closedBall (0 : F) M)) :
    ContinuousOn (fun q : F × (F × ℝ × ℝ) =>
        sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, q.2.2.1)) - ‖y‖ ^ 2 / (2 * q.2.2.2)
          - inner ℝ q.1 (y - q.2.1)}) (closedBall (0 : F) (Λ₀ + 1) ×ˢ S) ∧
    ∃ G : F × ℝ × ℝ → ℝ, ContinuousOn G S ∧
      ∀ p ∈ S,
        (∀ A : F, G p ≤ sSup {w : ℝ | ∃ y : F,
            w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}) ∧
        ∃ A₀ : F, ‖A₀‖ ≤ Λ₀ ∧
          G p = sSup {w : ℝ | ∃ y : F,
            w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A₀ (y - p.1)} := by
  -- Body-only acknowledgements (trap 3): `hSc`, `hSne`, `hM` and `hsup` are part of this
  -- node's protected signature.  The route below reaches both conclusions without consuming
  -- them -- see the burst comments -- so they are named here rather than above `-- BODY`.
  have _ := hSc
  have _ := hSne
  have _ := hM
  have _ := hsup
  have hMc : IsCompact (closedBall (0 : F) M) := isCompact_closedBall _ _
  have hQ0c : IsCompact (closedBall (0 : F) Λ₀) := isCompact_closedBall _ _
  -- `0 ∈ Q₀` needs `0 ≤ Λ₀`; record it rather than letting a tactic hunt for it.
  have hQ0ne : (closedBall (0 : F) Λ₀).Nonempty := ⟨0, mem_closedBall_self hΛ₀⟩
  -- The competitor functional is jointly continuous in (admissible triple, slope, position).
  -- Working over the SUBTYPE `↥S` is what makes this global: both obstructions to continuity
  -- on the whole parameter space -- that the time level lie in `I`, and that `s` not vanish --
  -- are exactly the admissibility of a point of `S`, so they hold at every subtype point.
  have hjoint : Continuous (fun u : (↥S × F) × F =>
      f (toLp 2 (u.2, u.1.1.val.2.1)) - ‖u.2‖ ^ 2 / (2 * u.1.1.val.2.2)
        - inner ℝ u.1.2 (u.2 - u.1.1.val.1)) := by
    have hfpart : Continuous (fun u : (↥S × F) × F =>
        f (toLp 2 (u.2, u.1.1.val.2.1))) :=
      hcont.comp_continuous (by fun_prop) (fun u => (hSadm _ u.1.1.property).2)
    have hdiv : Continuous (fun u : (↥S × F) × F =>
        ‖u.2‖ ^ 2 / (2 * u.1.1.val.2.2)) := by
      have hne : ∀ u : (↥S × F) × F, 2 * u.1.1.val.2.2 ≠ 0 := by
        intro u
        have := (hSadm _ u.1.1.property).1
        exact ne_of_gt (by linarith)
      simp only [div_eq_mul_inv]
      exact (by fun_prop : Continuous (fun u : (↥S × F) × F => ‖u.2‖ ^ 2)).mul
        ((by fun_prop : Continuous (fun u : (↥S × F) × F => 2 * u.1.1.val.2.2)).inv₀ hne)
    have hinn : Continuous (fun u : (↥S × F) × F =>
        (inner ℝ u.1.2 (u.2 - u.1.1.val.1) : ℝ)) := by fun_prop
    exact (hfpart.sub hdiv).sub hinn
  -- STEP 1 lifted from Mathlib: the max over a fixed compact ball is continuous in the
  -- parameter.  This is `IsCompact.continuous_sSup`; the .tex's inline two-sided
  -- subsequence argument stays as the NL proof of record and needs no Lean counterpart.
  have hΨ : Continuous (fun pA : ↥S × F =>
      sSup ((fun y : F => f (toLp 2 (y, pA.1.val.2.1)) - ‖y‖ ^ 2 / (2 * pA.1.val.2.2)
        - inner ℝ pA.2 (y - pA.1.val.1)) '' closedBall (0 : F) M)) :=
    hMc.continuous_sSup (f := fun (pA : ↥S × F) (y : F) =>
      f (toLp 2 (y, pA.1.val.2.1)) - ‖y‖ ^ 2 / (2 * pA.1.val.2.2)
        - inner ℝ pA.2 (y - pA.1.val.1)) hjoint
  -- G, the minimal value over the slope ball, extended by the `sInf` convention off `S`.
  obtain ⟨G, hGdef⟩ : ∃ G : F × ℝ × ℝ → ℝ, G = fun p => sInf ((fun A : F =>
      sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
        - inner ℝ A (y - p.1)}) '' closedBall (0 : F) Λ₀) := ⟨_, rfl⟩
  refine ⟨?_, G, ?_, ?_⟩
  · -- first conclusion: joint continuity of Γ on the slope-ball × S box
    rw [continuousOn_iff_continuous_domRestrict]
    have hmap : Continuous (fun q : ↥(closedBall (0 : F) (Λ₀ + 1) ×ˢ S) =>
        ((⟨q.val.2, q.property.2⟩ : ↥S), q.val.1)) :=
      (Continuous.subtype_mk (by fun_prop) _).prodMk (by fun_prop)
    refine (hΨ.comp hmap).congr ?_
    intro q
    exact (hball q.val.2 q.property.2 q.val.1
      (mem_closedBall_zero_iff.mp q.property.1)).symm
  · -- G is continuous on S
    rw [hGdef, continuousOn_iff_continuous_domRestrict]
    have hG' : Continuous (fun p : ↥S => sInf ((fun A : F =>
        sSup ((fun y : F => f (toLp 2 (y, p.val.2.1)) - ‖y‖ ^ 2 / (2 * p.val.2.2)
          - inner ℝ A (y - p.val.1)) '' closedBall (0 : F) M)) '' closedBall (0 : F) Λ₀)) :=
      hQ0c.continuous_sInf (f := fun (p : ↥S) (A : F) =>
        sSup ((fun y : F => f (toLp 2 (y, p.val.2.1)) - ‖y‖ ^ 2 / (2 * p.val.2.2)
          - inner ℝ A (y - p.val.1)) '' closedBall (0 : F) M)) hΨ
    refine hG'.congr ?_
    intro p
    congr 1
    refine Set.image_congr fun A hA => ?_
    exact (hball p.val p.property A
      (le_trans (mem_closedBall_zero_iff.mp hA) (by linarith))).symm
  · -- the minimum is attained in the slope ball and dominates every slope
    intro p hp
    have hΓA : ContinuousOn (fun A : F => sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)})
        (closedBall (0 : F) Λ₀) := by
      have hc : Continuous (fun A : F => sSup ((fun y : F =>
          f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1))
          '' closedBall (0 : F) M)) :=
        hΨ.comp (by fun_prop : Continuous (fun A : F => ((⟨p, hp⟩ : ↥S), A)))
      refine hc.continuousOn.congr ?_
      intro A hA
      exact hball p hp A (le_trans (mem_closedBall_zero_iff.mp hA) (by linarith))
    obtain ⟨A₀, hA₀ball, hA₀min⟩ := hQ0c.exists_isMinOn hQ0ne hΓA
    have hA₀norm : ‖A₀‖ ≤ Λ₀ := mem_closedBall_zero_iff.mp hA₀ball
    have hGp : G p = sSup {w : ℝ | ∃ y : F,
        w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A₀ (y - p.1)} := by
      rw [hGdef]
      refine IsLeast.csInf_eq ⟨⟨A₀, hA₀ball, rfl⟩, ?_⟩
      rintro b ⟨A, hA, rfl⟩
      exact isMinOn_iff.mp hA₀min A hA
    refine ⟨fun A => ?_, A₀, hA₀norm, hGp⟩
    rw [hGp]
    rcases le_or_gt ‖A‖ Λ₀ with hle | hgt
    · exact isMinOn_iff.mp hA₀min A (mem_closedBall_zero_iff.mpr hle)
    · have h0 := isMinOn_iff.mp hA₀min 0
        (mem_closedBall_zero_iff.mpr (by simpa using hΛ₀))
      have hns : ¬ (sSup {w : ℝ | ∃ y : F,
          w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2) - inner ℝ A (y - p.1)}
          ≤ sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, p.2.1)) - ‖y‖ ^ 2 / (2 * p.2.2)
            - inner ℝ (0 : F) (y - p.1)} + 1) := fun hcon =>
        absurd (hslope p hp A hcon) (not_le.mpr hgt)
      linarith [not_le.mp hns]
