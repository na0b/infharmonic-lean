module

public import InfHarmonic.ContactEnvelopeProperties
public import InfHarmonic.ContactFiniteSlope
public import InfHarmonic.EnvHamiltonianSolution
public import InfHarmonic.EnvelopeSlopeOrder
public import InfHarmonic.EnvelopeCompetitorBounds
public import InfHarmonic.ContactEnv
public import InfHarmonic.IsLimitSubOn

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Step 7 of paper Proposition 5.4: the forward envelope slopes of the contact
envelope converge to the finite envelope Hamiltonian at the contact point.

Let `v` be a member of the fit class `A_{m,C₀}`, centered at `z_* = (0,1)`, with
the horizontal Jensen bound of constant `κ > 0` at every time and subquadratic
spatial growth on every compact set of times, and let the contact envelope
`W = ContactEnv v κ = B_t v - κ² t/2` have the four properties
\noderef{ContactEnvelopeProperties} supplies that this argument reads --- its
continuity and subquadratic growth on positive times, its subsolution property
there, and the sandwich `v - κ² t/2 ≤ W ≤ v` --- together with the contact
`W z_* = 0`. Then the envelope Hamiltonian of `v` at `z_*` is a real number `H`,
and the forward envelope slopes of `W` at `z_*` tend to `H` as the length tends
to `0` from above.

Both conclusions are returned under one existential over `H` because `H` is
produced here: it is `(EnvHamiltonian v z_*).toReal`, which is a real number
only because \noderef{EnvHamiltonianSolution} rules out `⊤` and
\noderef{ContactFiniteSlope} rules out `⊥`. The earlier steps that produce such
a `v` are not re-narrated. The ambient space is an arbitrary finite-dimensional
real inner-product space `F`. -/
theorem ContactEnvelopeSlopeLimit (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀)
    (v : WithLp 2 (F × ℝ) → ℝ) (hκ0 : 0 < κ) (hvclass : IsFitClass C₀ v)
    (hvcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hvJ : HasJensenBound Set.univ v κ)
    (hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v)
    (hcontact : ContactEnv v κ (toLp 2 ((0 : F), (1 : ℝ))) = 0)
    (hWcont : ContinuousOn (ContactEnv v κ) {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2})
    (hWgrow : SubquadraticGrowth (Set.Ioi (0 : ℝ)) (ContactEnv v κ))
    (hWsub : IsLimitSubOn {z : WithLp 2 (F × ℝ) | 0 < (ofLp z).2} (ContactEnv v κ))
    (hWsand : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧ ContactEnv v κ z ≤ v z) :
    ∃ H : ℝ, EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal) ∧
      Tendsto (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
        (𝓝[>] (0 : ℝ)) (𝓝 H) := by
  have hstartime : (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 = 1 := rfl
  have hv0 : v (toLp 2 ((0 : F), (1 : ℝ))) = 0 := hvcent.1
  have hvcont : ContinuousOn v
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) := by
    simpa using hvclass.1.1.2.1
  have hvbary : BaryEnv v 1 (toLp 2 ((0 : F), (1 : ℝ))) = κ ^ 2 / 2 := by
    have h := hcontact
    rw [ContactEnv, hstartime] at h
    linarith only [h]
  have htc2 : ∀ (y : F) (c : ℝ), (ofLp (toLp 2 (y, c) : WithLp 2 (F × ℝ))).2 = c :=
    fun _ _ => rfl
  have hWcontpre : ContinuousOn (ContactEnv v κ)
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.Ioi (0 : ℝ)) := hWcont
  have hWsubpre : IsLimitSubOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.Ioi (0 : ℝ))
      (ContactEnv v κ) := hWsub
  have hvsolpre : IsLimitSolutionOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.univ) v := by
    rw [Set.preimage_univ]
    exact hvclass.1
  obtain ⟨-, hEHS2, hEHS3, -⟩ :=
    EnvHamiltonianSolution Set.univ isOpen_univ v hvcont hvgrow hvsolpre
  have hHtop : EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) ≠ ⊤ := hEHS3 _
  have hHbot : EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) ≠ ⊥ :=
    ContactFiniteSlope C₀ hC₀ κ hκ0 v hvclass hvcent hvJ
      (by rw [hvbary, hv0]; ring)
  obtain ⟨H, hHeq⟩ : ∃ H : ℝ,
      EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) = (H : EReal) :=
    ⟨_, (EReal.coe_toReal hHtop hHbot).symm⟩
  -- the two competitor-bound packages, for `v` on all of time and for `W` on `t > 0`
  obtain ⟨hCBv1, hCBv2, -⟩ :=
    EnvelopeCompetitorBounds (F := F) Set.univ v hvcont hvgrow
  obtain ⟨hCBW1, hCBW2, -⟩ :=
    EnvelopeCompetitorBounds (F := F) (Set.Ioi (0 : ℝ)) (ContactEnv v κ) hWcontpre hWgrow
  -- the forward slopes of `W` are below those of `v`
  have hslopeP : ∀ l : ℝ, 0 < l →
      EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ)))
        ≤ EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro l hl
    have hQ : QuadEnvP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ)))
        ≤ QuadEnvP v l (toLp 2 ((0 : F), (1 : ℝ))) := by
      refine (hCBW1 l (toLp 2 ((0 : F), (1 : ℝ))) hl
        (by rw [hstartime]; exact Set.mem_Ioi.mpr one_pos)
        (by rw [hstartime]; exact Set.mem_Ioi.mpr (by linarith only [hl]))).2 _ ?_
      intro y
      have hdomv := (hCBv1 l (toLp 2 ((0 : F), (1 : ℝ))) hl (Set.mem_univ _)
        (Set.mem_univ _)).1 y
      have hle := (hWsand (toLp 2 (y,
        (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 + l))
        (by rw [htc2, hstartime]; linarith only [hl])).2
      linarith only [hdomv, hle]
    rw [EnvSlopeP, EnvSlopeP, hcontact, hv0, sub_zero, sub_zero,
      div_le_div_iff_of_pos_right hl]
    exact hQ
  -- the backward slopes of `W` are above those of `v`, for short lengths
  have hslopeM : ∀ l : ℝ, 0 < l → l < 1 →
      EnvSlopeM v l (toLp 2 ((0 : F), (1 : ℝ)))
        ≤ EnvSlopeM (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro l hl hl1
    have hQ : QuadEnvM (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ)))
        ≤ QuadEnvM v l (toLp 2 ((0 : F), (1 : ℝ))) := by
      refine (hCBv2 l (toLp 2 ((0 : F), (1 : ℝ))) hl (Set.mem_univ _) (Set.mem_univ _)).2
        _ ?_
      intro y
      have hdomW := (hCBW2 l (toLp 2 ((0 : F), (1 : ℝ))) hl
        (by rw [hstartime]; exact Set.mem_Ioi.mpr one_pos)
        (by rw [hstartime]; exact Set.mem_Ioi.mpr (by linarith only [hl1]))).1 y
      have hle := (hWsand (toLp 2 (y,
        (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).2 - l))
        (by rw [htc2, hstartime]; linarith only [hl1])).2
      linarith only [hdomW, hle]
    rw [EnvSlopeM, EnvSlopeM, hcontact, hv0, zero_sub, zero_sub,
      div_le_div_iff_of_pos_right hl]
    linarith only [hQ]
  -- `H` is a lower bound for the backward slopes of `v`
  have hHleM : ∀ l : ℝ, 0 < l → H ≤ EnvSlopeM v l (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro l hl
    have h1 : (⨅ l' ∈ Set.Ioi (0 : ℝ),
        ((EnvSlopeM v l' (toLp 2 ((0 : F), (1 : ℝ))) : ℝ) : EReal))
        ≤ ((EnvSlopeM v l (toLp 2 ((0 : F), (1 : ℝ))) : ℝ) : EReal) := iInf₂_le l hl
    rw [hEHS2 (toLp 2 ((0 : F), (1 : ℝ))) (fun _ => Set.mem_univ _), hHeq] at h1
    exact EReal.coe_le_coe_iff.mp h1
  -- and the forward slopes of `v` come arbitrarily close to `H`
  have hinfP : ∀ ε : ℝ, 0 < ε → ∃ l : ℝ, 0 < l ∧
      EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ))) < H + ε := by
    intro ε hε
    by_contra hcon
    push Not at hcon
    have h2 : ((H + ε : ℝ) : EReal)
        ≤ EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) := by
      rw [EnvHamiltonian]
      refine le_iInf₂_iff.mpr ?_
      intro l hl
      exact EReal.coe_le_coe_iff.mpr (hcon l hl)
    rw [hHeq] at h2
    have h3 := EReal.coe_le_coe_iff.mp h2
    linarith only [h3, hε]
  obtain ⟨hESO1, hESO2⟩ :=
    EnvelopeSlopeOrder (Set.Ioi (0 : ℝ)) isOpen_Ioi (ContactEnv v κ) hWcontpre hWgrow
      hWsubpre
  have hWmono : ∀ l l' : ℝ, 0 < l → l ≤ l' →
      EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ)))
        ≤ EnvSlopeP (ContactEnv v κ) l' (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro l l' hl hll'
    refine hESO1 _ l l' hl hll' ?_
    intro σ hσ
    rw [hstartime]
    exact Set.mem_Ioi.mpr (by linarith only [hσ.1])
  have hWlow : ∀ h : ℝ, 0 < h → h < 1 →
      H ≤ EnvSlopeP (ContactEnv v κ) h (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro h hh hh1
    by_contra hcon
    push Not at hcon
    obtain ⟨δ, hδ, hδbd⟩ := hESO2 (toLp 2 ((0 : F), (1 : ℝ))) h
      ((H - EnvSlopeP (ContactEnv v κ) h (toLp 2 ((0 : F), (1 : ℝ)))) / 2) hh
      (by linarith only [hcon]) (by
        intro σ hσ
        rw [hstartime]
        exact Set.mem_Ioi.mpr (by linarith only [hσ.1, hh1]))
    obtain ⟨l, hl0, hlδ, hl1⟩ : ∃ l : ℝ, 0 < l ∧ l < δ ∧ l < 1 :=
      ⟨min (δ / 2) (1 / 2), lt_min (by linarith only [hδ]) (by norm_num),
        lt_of_le_of_lt (min_le_left _ _) (by linarith only [hδ]),
        lt_of_le_of_lt (min_le_right _ _) (by norm_num)⟩
    have h1 := hHleM l hl0
    have h2 := hslopeM l hl0 hl1
    have h3 := hδbd l hl0 hlδ
    linarith only [h1, h2, h3, hcon]
  have hWlowAll : ∀ h : ℝ, 0 < h →
      H ≤ EnvSlopeP (ContactEnv v κ) h (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro h hh
    rcases lt_or_ge h 1 with h1 | h1
    · exact hWlow h hh h1
    · exact le_trans (hWlow (1 / 2) (by norm_num) (by norm_num))
        (hWmono (1 / 2) h (by norm_num) (by linarith only [h1]))
  have htend : Tendsto
      (fun l => EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))))
      (𝓝[>] (0 : ℝ)) (𝓝 H) := by
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      refine eventually_nhdsWithin_of_forall ?_
      intro x hx
      exact lt_of_lt_of_le ha (hWlowAll x hx)
    · intro a ha
      obtain ⟨l, hl0, hlb⟩ := hinfP (a - H) (by linarith only [ha])
      have hSl : EnvSlopeP (ContactEnv v κ) l (toLp 2 ((0 : F), (1 : ℝ))) < a := by
        have h := hslopeP l hl0
        linarith only [h, hlb]
      filter_upwards [Ioo_mem_nhdsGT hl0] with x hx
      exact lt_of_le_of_lt (hWmono x l hx.1 (le_of_lt hx.2)) hSl
  exact ⟨H, hHeq, htend⟩
