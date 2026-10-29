import InfHarmonic.IsFitClass
import InfHarmonic.IsCenteredAt
import InfHarmonic.HasJensenBound
import InfHarmonic.BaryEnvDuality
import InfHarmonic.UniformSubquadratic
import InfHarmonic.EnvHamiltonianSolution
import InfHarmonic.QuadEnvPathConvex
import InfHarmonic.EnvelopeCompetitorBounds
import InfHarmonic.QuadEnvAttained
import InfHarmonic.EnvelopeSlopeOrder
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (5.12), finite slope at the contact: at the extremal contact point
the envelope Hamiltonian of `v` is finite. -/
theorem ContactFiniteSlope (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (κ : ℝ) (hκ : 0 < κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (hcontact : BaryEnv v 1 (toLp 2 ((0 : F), (1 : ℝ))) - v (toLp 2 ((0 : F), (1 : ℝ)))
      = κ ^ 2 / 2) :
    EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) ≠ ⊥ := by
  classical
  -- the strict positivity of `κ` is carried by the frozen signature but not needed:
  -- the conclusion asks only for SOME real lower bound on the slopes.
  have _unused_hκ : 0 < κ := hκ
  -- ===== Step 0: standing facts =====
  -- `BaryEnvDuality`'s integral clause mentions a measure on `F`, which carries no
  -- measurable structure here and needs none: give `F` its Borel σ-algebra locally.
  -- The clauses used below mention no measure, so the choice is immaterial.
  let _ : MeasurableSpace F := borel F
  have _ : BorelSpace F := ⟨rfl⟩
  have hIuniv : ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvcont : ContinuousOn v
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc η hη
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc η hη
    exact ⟨M, hM0, fun ξ hξ hξJ => hMb v hv hcent ξ hξ hξJ⟩
  have hvsol : IsLimitSolutionOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ)) v := by
    rw [hIuniv]; exact hv.1
  have hvsub : IsLimitSubOn
      ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' (Set.univ : Set ℝ)) v := hvsol.1
  have hv0 : v (toLp 2 ((0 : F), (1 : ℝ))) = 0 := hcent.1
  have hnormsmul : ∀ (c : ℝ) (u : F), ‖c • u‖ ^ 2 = c ^ 2 * ‖u‖ ^ 2 := by
    intro c u; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  obtain ⟨hdomP, hdomM, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont hvgrow
  obtain ⟨hslopemono, -, -, -⟩ :=
    EnvHamiltonianSolution (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow hvsol
  obtain ⟨-, hESO2⟩ :=
    EnvelopeSlopeOrder (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow hvsub
  obtain ⟨hattP, -, -, -, -, -⟩ :=
    QuadEnvAttained (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow
  obtain ⟨hBEatt, hBEdual, -, -, -⟩ :=
    BaryEnvDuality (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow
  -- ===== Step 1: the attaining configuration is extremal =====
  obtain ⟨n, θ, y, hcfg, hattain⟩ :=
    hBEatt 1 (toLp 2 ((0 : F), (1 : ℝ))) one_pos (Set.mem_univ _)
  obtain ⟨hθpos, hθ1, hθmean0⟩ := hcfg
  have hmean : ∑ i, θ i • y i = (0 : F) := hθmean0
  have hcfg0 : IsBaryConfig n θ y (0 : F) := ⟨hθpos, hθ1, hmean⟩
  obtain ⟨r, hrdef⟩ : ∃ s : ℝ, s = BaryRadius n θ y (0 : F) := ⟨_, rfl⟩
  obtain ⟨D, hDdef⟩ : ∃ s : ℝ, s = ∑ i, θ i * v (toLp 2 (y i, (1 : ℝ))) := ⟨_, rfl⟩
  have hattain' : BaryEnv v 1 (toLp 2 ((0 : F), (1 : ℝ))) = D - r ^ 2 / (2 * 1) := by
    rw [hDdef, hrdef]; exact hattain
  have hrnn : (0 : ℝ) ≤ r := by rw [hrdef, BaryRadius]; exact Real.sqrt_nonneg _
  have hr2 : r ^ 2 = ∑ i, θ i * ‖y i‖ ^ 2 := by
    have hnn : (0 : ℝ) ≤ ∑ i, θ i * ‖y i - (0 : F)‖ ^ 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (hθpos i).le (sq_nonneg _)
    rw [hrdef, BaryRadius, Real.sq_sqrt hnn]
    exact Finset.sum_congr rfl fun i _ => by rw [sub_zero]
  have hcontact' : D - r ^ 2 / (2 * 1) = κ ^ 2 / 2 := by
    have h := hcontact
    rw [hv0, sub_zero] at h
    rw [← hattain']
    exact h
  have hjen : D ≤ κ * r := by
    have h := hJ (1 : ℝ) (Set.mem_univ _) n θ y (0 : F) hcfg0
    rw [hv0, sub_zero] at h
    rw [hDdef, hrdef]
    exact h
  have hrk : r = κ := by
    have hsq : (r - κ) ^ 2 ≤ 0 := by nlinarith only [hcontact', hjen]
    have h0 : (r - κ) ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
    have h1 : r - κ = 0 := by
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h0
    linarith only [h1]
  have hDk : D = κ ^ 2 := by rw [hrk] at hcontact'; linarith only [hcontact']
  -- ===== Step 2: all `y i` are forward optimizers from one point =====
  obtain ⟨A, hAeq, -⟩ := hBEdual 1 (toLp 2 ((0 : F), (1 : ℝ))) one_pos (Set.mem_univ _)
  obtain ⟨b, hbdef⟩ : ∃ u : F, u = -A := ⟨_, rfl⟩
  have hAeq' : BaryEnv v 1 (toLp 2 ((0 : F), (1 : ℝ))) - ‖(0 : F)‖ ^ 2 / (2 * 1)
      = sSup {w : ℝ | ∃ u : F, w = v (toLp 2 (u, (1 : ℝ))) - ‖u‖ ^ 2 / (2 * 1)
          - inner ℝ A (u - (0 : F))} := hAeq
  have hcs : ∀ u : F, v (toLp 2 (u, (1 : ℝ))) - ‖u‖ ^ 2 / (2 * 1) - inner ℝ A (u - (0 : F))
      = (v (toLp 2 (u, (1 : ℝ))) - ‖u - b‖ ^ 2 / (2 * 1)) + ‖A‖ ^ 2 / 2 := by
    intro u
    have h1 : ‖u - b‖ ^ 2 = ‖u‖ ^ 2 + 2 * (inner ℝ A u : ℝ) + ‖A‖ ^ 2 := by
      rw [hbdef, sub_neg_eq_add, norm_add_sq_real, real_inner_comm]
    rw [h1, sub_zero]
    ring
  have hb1 : (ofLp (toLp 2 (b, (0 : ℝ)) : WithLp 2 (F × ℝ))).1 = b := rfl
  have hb2 : (ofLp (toLp 2 (b, (0 : ℝ)) : WithLp 2 (F × ℝ))).2 = (0 : ℝ) := rfl
  obtain ⟨hh, hhdef⟩ : ∃ f : ℝ → ℝ, f = fun σ => QuadEnvP v σ (toLp 2 (b, (0 : ℝ))) :=
    ⟨_, rfl⟩
  have hhval : ∀ σ : ℝ, hh σ = QuadEnvP v σ (toLp 2 (b, (0 : ℝ))) := by
    intro σ; rw [hhdef]
  obtain ⟨hdom1, hleast1⟩ :=
    hdomP 1 (toLp 2 (b, (0 : ℝ))) one_pos (Set.mem_univ _) (Set.mem_univ _)
  have hdom1' : ∀ u : F, v (toLp 2 (u, (1 : ℝ))) - ‖u - b‖ ^ 2 / (2 * 1) ≤ hh 1 := by
    intro u
    have h := hdom1 u
    rw [hb2, hb1, zero_add] at h
    rw [hhval]
    exact h
  have hleast1' : ∀ c : ℝ,
      (∀ u : F, v (toLp 2 (u, (1 : ℝ))) - ‖u - b‖ ^ 2 / (2 * 1) ≤ c) → hh 1 ≤ c := by
    intro c hc
    rw [hhval]
    refine hleast1 c fun u => ?_
    rw [hb2, hb1, zero_add]
    exact hc u
  have hSb : ∀ w ∈ {w : ℝ | ∃ u : F, w = v (toLp 2 (u, (1 : ℝ))) - ‖u‖ ^ 2 / (2 * 1)
      - inner ℝ A (u - (0 : F))}, w ≤ hh 1 + ‖A‖ ^ 2 / 2 := by
    rintro w ⟨u, rfl⟩
    rw [hcs u]
    linarith only [hdom1' u]
  have hSbdd : BddAbove {w : ℝ | ∃ u : F, w = v (toLp 2 (u, (1 : ℝ))) - ‖u‖ ^ 2 / (2 * 1)
      - inner ℝ A (u - (0 : F))} := ⟨hh 1 + ‖A‖ ^ 2 / 2, hSb⟩
  have hSne : ({w : ℝ | ∃ u : F, w = v (toLp 2 (u, (1 : ℝ))) - ‖u‖ ^ 2 / (2 * 1)
      - inner ℝ A (u - (0 : F))}).Nonempty := ⟨_, ⟨(0 : F), rfl⟩⟩
  have hGamma : BaryEnv v 1 (toLp 2 ((0 : F), (1 : ℝ))) = hh 1 + ‖A‖ ^ 2 / 2 := by
    have hz : ‖(0 : F)‖ ^ 2 / (2 * 1) = (0 : ℝ) := by simp
    rw [hz, sub_zero] at hAeq'
    rw [hAeq']
    refine le_antisymm (csSup_le hSne hSb) ?_
    have hb' : hh 1 ≤ sSup {w : ℝ | ∃ u : F, w = v (toLp 2 (u, (1 : ℝ))) - ‖u‖ ^ 2 / (2 * 1)
        - inner ℝ A (u - (0 : F))} - ‖A‖ ^ 2 / 2 := by
      refine hleast1' _ fun u => ?_
      have hm := le_csSup hSbdd (⟨u, rfl⟩ : _ ∈ {w : ℝ | ∃ u' : F,
        w = v (toLp 2 (u', (1 : ℝ))) - ‖u'‖ ^ 2 / (2 * 1) - inner ℝ A (u' - (0 : F))})
      rw [hcs u] at hm
      linarith only [hm]
    linarith only [hb']
  have hinnersum : (inner ℝ A (∑ i, θ i • y i) : ℝ) = ∑ i, θ i * inner ℝ A (y i) := by
    rw [inner_sum]
    exact Finset.sum_congr rfl fun i _ => real_inner_smul_right _ _ _
  have hinner0 : (∑ i, θ i * (inner ℝ A (y i) : ℝ)) = 0 := by
    rw [← hinnersum, hmean, inner_zero_right]
  have havg : (∑ i, θ i * (v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1)
      - inner ℝ A (y i - (0 : F)))) = hh 1 + ‖A‖ ^ 2 / 2 := by
    have hs : ∀ i, θ i * (v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1)
        - inner ℝ A (y i - (0 : F)))
        = θ i * v (toLp 2 (y i, (1 : ℝ))) - (θ i * ‖y i‖ ^ 2) / (2 * 1)
          - θ i * inner ℝ A (y i) := by
      intro i; rw [sub_zero]; ring
    rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← hDdef, hinner0, ← Finset.sum_div, ← hr2]
    have h2 : hh 1 + ‖A‖ ^ 2 / 2 = D - r ^ 2 / (2 * 1) := by rw [← hGamma, hattain']
    rw [h2]
    ring
  have heach : ∀ i, v (toLp 2 (y i, (1 : ℝ))) - ‖y i - b‖ ^ 2 / (2 * 1) = hh 1 := by
    have hle : ∀ i, v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1)
        - inner ℝ A (y i - (0 : F)) ≤ hh 1 + ‖A‖ ^ 2 / 2 := fun i => hSb _ ⟨y i, rfl⟩
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ θ i * ((hh 1 + ‖A‖ ^ 2 / 2)
        - (v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1) - inner ℝ A (y i - (0 : F)))) :=
      fun i _ => mul_nonneg (hθpos i).le (by linarith only [hle i])
    have hsum0 : (∑ i, θ i * ((hh 1 + ‖A‖ ^ 2 / 2)
        - (v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1)
          - inner ℝ A (y i - (0 : F))))) = 0 := by
      have hs : ∀ i, θ i * ((hh 1 + ‖A‖ ^ 2 / 2)
          - (v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1)
            - inner ℝ A (y i - (0 : F))))
          = θ i * (hh 1 + ‖A‖ ^ 2 / 2)
            - θ i * (v (toLp 2 (y i, (1 : ℝ))) - ‖y i‖ ^ 2 / (2 * 1)
              - inner ℝ A (y i - (0 : F))) := by intro i; ring
      rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hθ1, one_mul, havg]
      ring
    intro i
    have h := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 i (Finset.mem_univ i)
    rcases mul_eq_zero.mp h with hc | hc
    · exact absurd hc (ne_of_gt (hθpos i))
    · have hcsi := hcs (y i)
      linarith only [hcsi, hc]
  -- ===== Step 3: `hh` is convex on `[0, 1]` =====
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) hh := by
    obtain ⟨h1, -⟩ :=
      QuadEnvPathConvex (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow 1 one_pos
    have h2 := h1 hvsub b (0 : F) (0 : ℝ) (fun l _ => Set.mem_univ _)
    have hfun : (fun σ : ℝ => QuadEnvP v σ (toLp 2 (b + σ • (0 : F), (0 : ℝ)))
        + ‖(0 : F)‖ ^ 2 * (σ * Real.log σ)) = hh := by
      funext σ
      rw [smul_zero, add_zero, norm_zero, hhval]
      ring
    rw [hfun] at h2
    exact h2
  obtain ⟨β, hβdef⟩ : ∃ s : ℝ, s = hh 1 - hh 0 := ⟨_, rfl⟩
  have hchord : ∀ l : ℝ, 0 < l → l ≤ 1 → β * l ≤ hh 1 - hh (1 - l) := by
    intro l hl hl1
    have hc := hconv.2 (Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩)
      (Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩) hl.le (by linarith only [hl1] : (0 : ℝ) ≤ 1 - l)
      (by ring)
    simp only [smul_eq_mul] at hc
    rw [show l * (0 : ℝ) + (1 - l) * 1 = 1 - l from by ring] at hc
    rw [hβdef]
    linarith only [hc]
  -- ===== Step 4: a lower bound for the slopes at the `y i` =====
  have hM : ∀ (i : Fin n) (l : ℝ), 0 < l → l < 1 →
      β ≤ EnvSlopeM v l (toLp 2 (y i, (1 : ℝ))) := by
    intro i l hl hl1
    have hlne : l ≠ 0 := ne_of_gt hl
    have h1lne : (1 : ℝ) - l ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith only [h, hl1]
    have hyi1 : (ofLp (toLp 2 (y i, (1 : ℝ)) : WithLp 2 (F × ℝ))).1 = y i := rfl
    have hyi2 : (ofLp (toLp 2 (y i, (1 : ℝ)) : WithLp 2 (F × ℝ))).2 = (1 : ℝ) := rfl
    obtain ⟨hdomMi, -⟩ :=
      hdomM l (toLp 2 (y i, (1 : ℝ))) hl (Set.mem_univ _) (Set.mem_univ _)
    have hc1 := hdomMi (b + (1 - l) • (y i - b))
    rw [hyi2, hyi1] at hc1
    have hn1 : ‖b + (1 - l) • (y i - b) - y i‖ ^ 2 / (2 * l)
        = l * ‖y i - b‖ ^ 2 / 2 := by
      rw [show b + (1 - l) • (y i - b) - y i = (-l) • (y i - b) from by module, hnormsmul]
      field_simp
    rw [hn1] at hc1
    obtain ⟨hdomPl, -⟩ :=
      hdomP (1 - l) (toLp 2 (b, (0 : ℝ))) (by linarith only [hl1]) (Set.mem_univ _) (Set.mem_univ _)
    have hc2 := hdomPl (b + (1 - l) • (y i - b))
    rw [hb2, hb1, zero_add] at hc2
    have hn2 : ‖b + (1 - l) • (y i - b) - b‖ ^ 2 / (2 * (1 - l))
        = (1 - l) * ‖y i - b‖ ^ 2 / 2 := by
      rw [show b + (1 - l) • (y i - b) - b = (1 - l) • (y i - b) from by module, hnormsmul]
      field_simp
    rw [hn2, ← hhval (1 - l)] at hc2
    have hval : v (toLp 2 (y i, (1 : ℝ))) = hh 1 + ‖y i - b‖ ^ 2 / 2 := by
      have h := heach i
      linarith only [h]
    have hch := hchord l hl hl1.le
    rw [EnvSlopeM, hval, le_div_iff₀ hl]
    linarith only [hc1, hc2, hch]
  have hMall : ∀ (i : Fin n) (l : ℝ), 0 < l → β ≤ EnvSlopeM v l (toLp 2 (y i, (1 : ℝ))) := by
    intro i l hl
    by_cases h1 : l < 1
    · exact hM i l hl h1
    · have h1' : (1 : ℝ) ≤ l := not_lt.mp h1
      have hmono := (hslopemono (toLp 2 (y i, (1 : ℝ))) (1 / 2) l (by norm_num) (by linarith only [h1'])
        (fun σ _ => Set.mem_univ _)).2
      have hhalf := hM i (1 / 2) (by norm_num) (by norm_num)
      linarith only [hmono, hhalf]
  have hP : ∀ (i : Fin n) (l : ℝ), 0 < l → β ≤ EnvSlopeP v l (toLp 2 (y i, (1 : ℝ))) := by
    intro i l hl
    have key : ∀ ε : ℝ, 0 < ε → β ≤ EnvSlopeP v l (toLp 2 (y i, (1 : ℝ))) + ε := by
      intro ε hε
      obtain ⟨δ, hδ, hbnd⟩ := hESO2 (toLp 2 (y i, (1 : ℝ))) l ε hl hε
        (fun σ _ => Set.mem_univ _)
      have h1 := hbnd (δ / 2) (by linarith only [hδ]) (by linarith only [hδ])
      have h2 := hMall i (δ / 2) (by linarith only [hδ])
      linarith only [h1, h2]
    by_contra hcon
    push Not at hcon
    have h3 := key ((β - EnvSlopeP v l (toLp 2 (y i, (1 : ℝ)))) / 2) (by linarith only [hcon])
    linarith only [h3, hcon]
  -- ===== Step 5: transferring the bound to the barycenter =====
  have hfinal : ∀ l : ℝ, 0 < l →
      β - κ ^ 2 / 2 ≤ EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ))) := by
    intro l hl
    have hlne : l ≠ 0 := ne_of_gt hl
    have hopt : ∀ i : Fin n, ∃ u : F, QuadEnvP v l (toLp 2 (y i, (1 : ℝ)))
        = v (toLp 2 (u, (1 : ℝ) + l)) - ‖u - y i‖ ^ 2 / (2 * l) := by
      intro i
      obtain ⟨u, hu⟩ := hattP l (toLp 2 (y i, (1 : ℝ))) hl (Set.mem_univ _) (Set.mem_univ _)
      exact ⟨u, hu⟩
    choose yh hyh using hopt
    obtain ⟨xh, hxhdef⟩ : ∃ u : F, u = ∑ i, θ i • yh i := ⟨_, rfl⟩
    obtain ⟨rp, hrpdef⟩ : ∃ s : ℝ, s = BaryRadius n θ yh xh := ⟨_, rfl⟩
    have hrpnn : (0 : ℝ) ≤ rp := by rw [hrpdef, BaryRadius]; exact Real.sqrt_nonneg _
    have hrpsq : rp ^ 2 = ∑ i, θ i * ‖yh i - xh‖ ^ 2 := by
      have hnn : (0 : ℝ) ≤ ∑ i, θ i * ‖yh i - xh‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hθpos i).le (sq_nonneg _)
      rw [hrpdef, BaryRadius, Real.sq_sqrt hnn]
    have hrsqrt : r = Real.sqrt (∑ i, θ i * ‖y i‖ ^ 2) := by
      rw [hrdef, BaryRadius]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [sub_zero]
    have hrpsqrt : rp = Real.sqrt (∑ i, θ i * ‖yh i - xh‖ ^ 2) := by
      rw [hrpdef, BaryRadius]
    -- the averaged attainment
    have hPsum : (∑ i, θ i * QuadEnvP v l (toLp 2 (y i, (1 : ℝ))))
        = (∑ i, θ i * v (toLp 2 (yh i, (1 : ℝ) + l)))
          - (∑ i, θ i * ‖yh i - y i‖ ^ 2) / (2 * l) := by
      have hs : ∀ i, θ i * QuadEnvP v l (toLp 2 (y i, (1 : ℝ)))
          = θ i * v (toLp 2 (yh i, (1 : ℝ) + l)) - (θ i * ‖yh i - y i‖ ^ 2) / (2 * l) := by
        intro i; rw [hyh i]; ring
      rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib, ← Finset.sum_div]
    -- the exact orthogonal decomposition
    have hw0 : ∑ i, θ i • ((yh i - xh) - y i) = (0 : F) := by
      have hs : ∀ i, θ i • ((yh i - xh) - y i)
          = θ i • yh i - θ i • xh - θ i • y i := by intro i; module
      rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, ← hxhdef, ← Finset.sum_smul, hθ1, one_smul, hmean]
      abel
    have hortho : (∑ i, θ i * ‖yh i - y i‖ ^ 2)
        = ‖xh‖ ^ 2 + ∑ i, θ i * ‖(yh i - xh) - y i‖ ^ 2 := by
      have hs : ∀ i, θ i * ‖yh i - y i‖ ^ 2
          = θ i * ‖(yh i - xh) - y i‖ ^ 2
            + 2 * (inner ℝ (θ i • ((yh i - xh) - y i)) xh : ℝ) + θ i * ‖xh‖ ^ 2 := by
        intro i
        rw [show yh i - y i = ((yh i - xh) - y i) + xh from by abel, norm_add_sq_real,
          real_inner_smul_left]
        ring
      rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_add_distrib, Finset.sum_add_distrib]
      have hmid : (∑ i, 2 * (inner ℝ (θ i • ((yh i - xh) - y i)) xh : ℝ)) = 0 := by
        rw [← Finset.mul_sum, ← sum_inner, hw0, inner_zero_left]
        ring
      rw [hmid, ← Finset.sum_mul, hθ1, one_mul]
      ring
    -- weighted Cauchy-Schwarz
    have hdot : (∑ i, θ i * (inner ℝ (yh i - xh) (y i) : ℝ)) ≤ rp * r := by
      have h1 : ∀ i : Fin n, (θ i * (inner ℝ (yh i - xh) (y i) : ℝ))
          ≤ Real.sqrt (θ i * ‖yh i - xh‖ ^ 2) * Real.sqrt (θ i * ‖y i‖ ^ 2) := by
        intro i
        have hin := real_inner_le_norm (yh i - xh) (y i)
        rw [Real.sqrt_mul (hθpos i).le, Real.sqrt_mul (hθpos i).le,
          Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
          show Real.sqrt (θ i) * ‖yh i - xh‖ * (Real.sqrt (θ i) * ‖y i‖)
            = Real.sqrt (θ i) * Real.sqrt (θ i) * (‖yh i - xh‖ * ‖y i‖) from by ring,
          Real.mul_self_sqrt (hθpos i).le]
        exact mul_le_mul_of_nonneg_left hin (hθpos i).le
      have h2 := Finset.sum_le_sum
        (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => h1 i)
      have h3 := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin n))
        (f := fun i : Fin n => θ i * ‖yh i - xh‖ ^ 2)
        (g := fun i : Fin n => θ i * ‖y i‖ ^ 2)
        (fun i => mul_nonneg (hθpos i).le (sq_nonneg _))
        (fun i => mul_nonneg (hθpos i).le (sq_nonneg _))
      rw [← hrsqrt, ← hrpsqrt] at h3
      linarith only [h2, h3]
    have hCS : (rp - r) ^ 2 ≤ ∑ i, θ i * ‖(yh i - xh) - y i‖ ^ 2 := by
      have hexp : (∑ i, θ i * ‖(yh i - xh) - y i‖ ^ 2)
          = (∑ i, θ i * ‖yh i - xh‖ ^ 2) + (∑ i, θ i * ‖y i‖ ^ 2)
            - 2 * (∑ i, θ i * (inner ℝ (yh i - xh) (y i) : ℝ)) := by
        have hs : ∀ i, θ i * ‖(yh i - xh) - y i‖ ^ 2
            = θ i * ‖yh i - xh‖ ^ 2 + θ i * ‖y i‖ ^ 2
              - 2 * (θ i * (inner ℝ (yh i - xh) (y i) : ℝ)) := by
          intro i; rw [norm_sub_sq_real]; ring
        rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hexp, ← hrpsq, ← hr2]
      nlinarith only [hdot]
    -- the Jensen bound at the time `1 + l` and the competitor at the barycenter
    have hjen2 := hJ ((1 : ℝ) + l) (Set.mem_univ _) n θ yh xh ⟨hθpos, hθ1, by rw [hxhdef]⟩
    rw [← hrpdef] at hjen2
    obtain ⟨hdomP0, -⟩ :=
      hdomP l (toLp 2 ((0 : F), (1 : ℝ))) hl (Set.mem_univ _) (Set.mem_univ _)
    have hcomp0 : v (toLp 2 (xh, (1 : ℝ) + l)) - ‖xh‖ ^ 2 / (2 * l)
        ≤ QuadEnvP v l (toLp 2 ((0 : F), (1 : ℝ))) := by
      have h := hdomP0 xh
      rw [show (ofLp (toLp 2 ((0 : F), (1 : ℝ)) : WithLp 2 (F × ℝ))).1 = (0 : F) from rfl,
        sub_zero] at h
      exact h
    -- the key inequality
    have hu : κ * (rp - r) - (rp - r) ^ 2 / (2 * l) ≤ κ ^ 2 * l / 2 := by
      have hid : κ * (rp - r) - (rp - r) ^ 2 / (2 * l)
          = κ ^ 2 * l / 2 - ((rp - r) - κ * l) ^ 2 / (2 * l) := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ ((rp - r) - κ * l) ^ 2 / (2 * l) :=
        div_nonneg (sq_nonneg _) (by linarith only [hl])
      linarith only [hid, hnn]
    have hdiv : (‖xh‖ ^ 2 + (rp - r) ^ 2) / (2 * l)
        ≤ (∑ i, θ i * ‖yh i - y i‖ ^ 2) / (2 * l) := by
      refine div_le_div_of_nonneg_right ?_ (by linarith only [hl])
      rw [hortho]
      linarith only [hCS]
    have hsplit : (‖xh‖ ^ 2 + (rp - r) ^ 2) / (2 * l)
        = ‖xh‖ ^ 2 / (2 * l) + (rp - r) ^ 2 / (2 * l) := by ring
    have hrk' : κ * rp = κ ^ 2 + κ * (rp - r) := by rw [hrk]; ring
    have hkey : (∑ i, θ i * QuadEnvP v l (toLp 2 (y i, (1 : ℝ))))
        ≤ QuadEnvP v l (toLp 2 ((0 : F), (1 : ℝ))) + κ ^ 2 + κ ^ 2 * l / 2 := by
      linarith only [hPsum, hjen2, hcomp0, hdiv, hsplit, hrk', hu]
    -- subtract the values and divide by `l`
    have hvalsum : (∑ i, θ i * v (toLp 2 (y i, (1 : ℝ)))) = κ ^ 2 := by
      rw [← hDdef]; exact hDk
    have hslopesum : l * (∑ i, θ i * EnvSlopeP v l (toLp 2 (y i, (1 : ℝ))))
        = (∑ i, θ i * QuadEnvP v l (toLp 2 (y i, (1 : ℝ)))) - κ ^ 2 := by
      have hs : ∀ i, θ i * EnvSlopeP v l (toLp 2 (y i, (1 : ℝ)))
          = (θ i * QuadEnvP v l (toLp 2 (y i, (1 : ℝ)))
            - θ i * v (toLp 2 (y i, (1 : ℝ)))) / l := by
        intro i; rw [EnvSlopeP]; field_simp
      rw [Finset.sum_congr rfl fun i _ => hs i, ← Finset.sum_div, Finset.sum_sub_distrib,
        hvalsum]
      field_simp
    have hslope0 : l * EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ)))
        = QuadEnvP v l (toLp 2 ((0 : F), (1 : ℝ))) := by
      rw [EnvSlopeP, hv0]
      field_simp
      ring
    have hβsum : β ≤ ∑ i, θ i * EnvSlopeP v l (toLp 2 (y i, (1 : ℝ))) := by
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
          θ i * β ≤ θ i * EnvSlopeP v l (toLp 2 (y i, (1 : ℝ))) :=
        fun i _ => mul_le_mul_of_nonneg_left (hP i l hl) (hθpos i).le
      have hsum := Finset.sum_le_sum hterm
      rw [← Finset.sum_mul, hθ1, one_mul] at hsum
      exact hsum
    have hfin2 : l * β ≤ l * (EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ))) + κ ^ 2 / 2) := by
      have h1 : l * β ≤ l * (∑ i, θ i * EnvSlopeP v l (toLp 2 (y i, (1 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hβsum hl.le
      have h2 : l * (EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ))) + κ ^ 2 / 2)
          = l * EnvSlopeP v l (toLp 2 ((0 : F), (1 : ℝ))) + κ ^ 2 * l / 2 := by ring
      rw [h2]
      linarith only [h1, hslopesum, hslope0, hkey]
    have h4 := le_of_mul_le_mul_left hfin2 hl
    linarith only [h4]
  -- ===== Step 6: conclusion =====
  intro hbot
  have hle : ((β - κ ^ 2 / 2 : ℝ) : EReal)
      ≤ EnvHamiltonian v (toLp 2 ((0 : F), (1 : ℝ))) := by
    rw [EnvHamiltonian]
    refine le_iInf₂ fun l hl => ?_
    exact EReal.coe_le_coe_iff.mpr (hfinal l (Set.mem_Ioi.mp hl))
  rw [hbot, le_bot_iff] at hle
  exact EReal.coe_ne_bot _ hle
