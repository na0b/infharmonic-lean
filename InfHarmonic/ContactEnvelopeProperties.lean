import InfHarmonic.BaryEnvSandwich
import InfHarmonic.BaryEnvDuality
import InfHarmonic.BarycentricSubsolution
import InfHarmonic.ContactEnv
import InfHarmonic.IsFitClass
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 6 of paper Proposition 5.4: the six properties of the contact envelope.

Let `v` be a member of the fit class `A_{m,C₀}` with the horizontal Jensen
bound of constant `κ > 0` at every time and with subquadratic spatial growth on
every compact set of times; the source of those three hypotheses in the
application is the frame construction of \noderef{UniformSubquadratic} and the
earlier steps, which is not re-narrated here. Write
`W z = ContactEnv v κ z = B_{t}v(z) - κ² t/2` for the contact envelope, `t`
being the time coordinate of `z`. Then, on the open positive-time half space:

(a) the sandwich `v z - κ² t/2 ≤ W z ≤ v z` holds, from
\noderef{BaryEnvSandwich} at the time interval `(0,∞)` with the barycentric
radius equal to the time;

(b) `W` is continuous there, and at each positive time `t` the function
`x ↦ W(x,t) - |x|²/(2t)` is concave on the whole space --- both from the joint
continuity and the semiconcavity clauses of \noderef{BaryEnvDuality};

(c) `W` has subquadratic growth on `(0,∞)`, by comparing it with `v` through
the sandwich of (a) and absorbing the bounded correction `κ² t/2` into half of
the growth allowance;

(d) `W` is a subsolution of the limiting equation there, by
\noderef{BarycentricSubsolution} applied to `v` restricted to the half space,
the envelope of that restriction agreeing with `W` after the affine-in-time
shift;

(e) at every contact point, where `W z = v z`, the barycentric gap is exactly
`κ² t/2`, i.e. `(B_t v(z) - v z)/t = κ²/2`.

The six facts are stated in the order they are proved and in the form a
following step consumes them. The ambient space is an arbitrary
finite-dimensional real inner-product space `F`. -/
theorem ContactEnvelopeProperties (C₀ κ : ℝ) (v : WithLp 2 (F × ℝ) → ℝ)
    (hκ0 : 0 < κ) (hvclass : IsFitClass C₀ v)
    (hvJ : HasJensenBound Set.univ v κ)
    (hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v) :
    (∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
        v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z
          ∧ ContactEnv v κ z ≤ v z) ∧
      ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} ∧
      (∀ t : ℝ, 0 < t → ConcaveOn ℝ (Set.univ : Set F)
        (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t))) ∧
      SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ) ∧
      IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} (ContactEnv v κ) ∧
      (∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z = v z →
        (BaryEnv v (ofLp z).2 z - v z) / (ofLp z).2 = κ ^ 2 / 2) := by
  have htimecont : Continuous (fun z : WithLp 2 (F × ℝ) => (ofLp z).2) :=
    continuous_snd.comp (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).continuous
  have hOpenPos : IsOpen {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} :=
    isOpen_Ioi.preimage htimecont
  have hvcontIoi : ContinuousOn v
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.Ioi (0 : ℝ)) :=
    hvclass.1.1.2.1.mono (Set.subset_univ _)
  have hvgrowIoi : SubquadraticGrowth (Set.Ioi (0 : ℝ)) v :=
    fun J _ hJc => hvgrow J (Set.subset_univ J) hJc
  have hvJIoi : HasJensenBound (Set.Ioi (0 : ℝ)) v κ :=
    fun t _ => hvJ t (Set.mem_univ t)
  -- (a) the sandwich and the contact
  have hsand := BaryEnvSandwich (Set.Ioi (0 : ℝ)) v κ hκ0.le hvcontIoi hvJIoi
    hvgrowIoi
  have hWsand : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z
        ∧ ContactEnv v κ z ≤ v z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsand (ofLp z).2 z hz hz
    rw [ContactEnv]
    exact ⟨by linarith, by linarith⟩
  -- (b) continuity and semiconcavity.  `BaryEnvDuality` is stated for a Borel
  -- measurable `F` because one of its clauses speaks about probability measures;
  -- this node's statement carries no measurable structure and needs none, so give
  -- `F` its Borel σ-algebra locally.  Nothing used below depends on the choice.
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  obtain ⟨-, -, hBD3, hBD4, -⟩ :=
    BaryEnvDuality (Set.Ioi (0 : ℝ)) isOpen_Ioi v hvcontIoi hvgrowIoi
  have hWcont : ContinuousOn (ContactEnv v κ)
      {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} := by
    intro z₀ hz₀
    refine ContinuousAt.continuousWithinAt ?_
    have hz₀' : (ofLp z₀).2 ∈ Set.Ioi (0 : ℝ) := hz₀
    have h1 : ContinuousAt (fun p : ℝ × WithLp 2 (F × ℝ) => BaryEnv v p.1 p.2)
        ((ofLp z₀).2, z₀) := hBD3 _ hz₀ z₀ hz₀'
    have h2 : Continuous (fun z : WithLp 2 (F × ℝ) => ((ofLp z).2, z)) :=
      htimecont.prodMk continuous_id
    have h3 : ContinuousAt (fun z : WithLp 2 (F × ℝ) => BaryEnv v (ofLp z).2 z) z₀ := by
      have h := Filter.Tendsto.comp h1 (h2.continuousAt (x := z₀))
      exact h
    have h4 : ContinuousAt (fun z : WithLp 2 (F × ℝ) => κ ^ 2 * (ofLp z).2 / 2) z₀ :=
      (continuousAt_const.mul htimecont.continuousAt).div_const 2
    exact h3.sub h4
  have hWconc : ∀ t : ℝ, 0 < t → ConcaveOn ℝ (Set.univ : Set F)
      (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t)) := by
    intro t ht
    have h := (hBD4 t t ht ht).add_const (-(κ ^ 2 * t / 2))
    have he : (fun x : F => ContactEnv v κ (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t))
        = fun x : F => (BaryEnv v t (toLp 2 (x, t)) - ‖x‖ ^ 2 / (2 * t))
            + -(κ ^ 2 * t / 2) := by
      funext x
      have htc : (ofLp (toLp 2 (x, t) : WithLp 2 (F × ℝ))).2 = t := rfl
      rw [ContactEnv, htc]
      ring
    rw [he]
    exact h
  -- (c) growth
  have hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ) := by
    intro J hJ hJc ε hε
    obtain ⟨T, hT⟩ := hJc.bddAbove
    obtain ⟨M₁, hM₁, hM₁bd⟩ := hvgrowIoi J hJ hJc (ε / 2) (by positivity)
    refine ⟨max M₁ (Real.sqrt (2 * max 0 (κ ^ 2 * T / 2) / ε)), lt_max_iff.mpr (Or.inl hM₁),
      ?_⟩
    intro z hz hzJ
    have hzt : 0 < (ofLp z).2 := hJ hzJ
    have h1 := hM₁bd z (le_trans (le_max_left _ _) hz) hzJ
    obtain ⟨hs1, hs2⟩ := hWsand z hzt
    have hcJ : κ ^ 2 * (ofLp z).2 / 2 ≤ max 0 (κ ^ 2 * T / 2) := by
      refine le_trans ?_ (le_max_right _ _)
      have : (ofLp z).2 ≤ T := hT hzJ
      have hk : (0 : ℝ) ≤ κ ^ 2 := sq_nonneg κ
      nlinarith
    have hsq : 2 * max 0 (κ ^ 2 * T / 2) / ε ≤ ‖(ofLp z).1‖ ^ 2 := by
      have hge : Real.sqrt (2 * max 0 (κ ^ 2 * T / 2) / ε) ≤ ‖(ofLp z).1‖ :=
        le_trans (le_max_right _ _) hz
      have hnn : (0 : ℝ) ≤ 2 * max 0 (κ ^ 2 * T / 2) / ε := by
        have := le_max_left (0 : ℝ) (κ ^ 2 * T / 2)
        positivity
      calc 2 * max 0 (κ ^ 2 * T / 2) / ε
          = Real.sqrt (2 * max 0 (κ ^ 2 * T / 2) / ε) ^ 2 := (Real.sq_sqrt hnn).symm
        _ ≤ ‖(ofLp z).1‖ ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) hge 2

    have hhalf : max 0 (κ ^ 2 * T / 2) ≤ ε / 2 * ‖(ofLp z).1‖ ^ 2 := by
      rw [div_le_iff₀ hε] at hsq
      linarith
    have habs := abs_le.mp h1
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith
  -- (d) the subsolution property
  have hvsubIoi : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} v := by
    refine ⟨hOpenPos, hvclass.1.1.2.1.mono (Set.subset_univ _), ?_⟩
    intro z hz φ hφ hmax
    refine hvclass.1.1.2.2 z (Set.mem_univ _) φ hφ ?_
    have h0 : ∀ᶠ x in nhdsWithin z {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2},
        v x - φ x ≤ v z - φ z := hmax
    show ∀ᶠ x in nhdsWithin z (Set.univ : Set (WithLp 2 (F × ℝ))),
      v x - φ x ≤ v z - φ z
    rwa [nhdsWithin_univ, ← hOpenPos.nhdsWithin_eq hz]
  have hbridge : (fun z : WithLp 2 (F × ℝ) =>
      BaryEnv v (ofLp z).2 z - κ ^ 2 / 2 * (ofLp z).2) = ContactEnv v κ := by
    funext z
    rw [ContactEnv]
    ring
  have hWsub : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} (ContactEnv v κ) := by
    have h := BarycentricSubsolution v hvsubIoi hvgrowIoi (κ ^ 2 / 2)
    rwa [hbridge] at h
  -- (e) the gap at a contact
  have hWgap : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 → ContactEnv v κ z = v z →
      (BaryEnv v (ofLp z).2 z - v z) / (ofLp z).2 = κ ^ 2 / 2 := by
    intro z hz hcon
    rw [ContactEnv] at hcon
    rw [show BaryEnv v (ofLp z).2 z - v z = κ ^ 2 * (ofLp z).2 / 2 from by linarith]
    field_simp
  exact ⟨hWsand, hWcont, hWconc, hWgrow, hWsub, hWgap⟩
