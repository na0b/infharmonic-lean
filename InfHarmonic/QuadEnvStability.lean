module

public import InfHarmonic.QuadEnvAttained
public import InfHarmonic.UnifSubquadraticGrowth

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.3, stability: under locally uniform convergence with a common
subquadratic growth control, the quadratic envelopes converge uniformly on
compact sets of admissible centers at each fixed positive length. -/
theorem QuadEnvStability (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (fs : ℕ → WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hconts : ∀ j, ContinuousOn (fs j) ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hconv : ∀ K ⊆ ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I), IsCompact K →
      TendstoUniformlyOn fs f atTop K)
    (hgrow : UnifSubquadraticGrowth I fs) (hgrow0 : SubquadraticGrowth I f)
    (l : ℝ) (hl : 0 < l) :
    (∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K →
        (∀ z ∈ K, (ofLp z).2 ∈ I ∧ (ofLp z).2 + l ∈ I) →
        TendstoUniformlyOn (fun j => QuadEnvP (fs j) l) (QuadEnvP f l) atTop K) ∧
    (∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K →
        (∀ z ∈ K, (ofLp z).2 ∈ I ∧ (ofLp z).2 - l ∈ I) →
        TendstoUniformlyOn (fun j => QuadEnvM (fs j) l) (QuadEnvM f l) atTop K) := by
  have _unused_hI : IsOpen I := hI
  have _unused_hconts := hconts
  have h8l : (0:ℝ) < 8 * l := by positivity
  have h2l : (0:ℝ) < 2 * l := by positivity
  have h32l : (0:ℝ) < 32 * l := by positivity
  -- Step 3 of the NL proof, in the abstract: for two spatial profiles that are close on a
  -- large ball and jointly localized outside it, the competitor suprema are close.
  have half : ∀ (G H : F → ℝ) (x : F) (R Nb Mb Mf ε : ℝ),
      0 ≤ R → 0 ≤ Nb → 0 ≤ ε → ‖x‖ ≤ R → 4 * R ≤ Mb → Mb ≤ Mf →
      Nb * (32 * l) ≤ 5 * Mf ^ 2 →
      (∀ y : F, ‖y‖ ≤ Mb → |G y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |G y| ≤ ‖y‖ ^ 2 / (8 * l)) →
      (∀ y : F, ‖y‖ ≤ Mb → |H y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |H y| ≤ ‖y‖ ^ 2 / (8 * l)) →
      (∀ y : F, ‖y‖ ≤ Mf → |G y - H y| ≤ ε) →
      sSup {w : ℝ | ∃ y : F, w = G y - ‖y - x‖ ^ 2 / (2 * l)}
        ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y - x‖ ^ 2 / (2 * l)} + ε := by
    intro G H x R Nb Mb Mf ε hR hNb hε hx hRMb hMbMf hNMf hGb hGf hHb hHf hGH
    -- the far-field estimate (4.far): past `Mb` every competitor value is very negative
    have hfar : ∀ Q : F → ℝ, (∀ y : F, Mb < ‖y‖ → |Q y| ≤ ‖y‖ ^ 2 / (8 * l)) →
        ∀ y : F, Mb < ‖y‖ → Q y - ‖y - x‖ ^ 2 / (2 * l) ≤ -(5 * ‖y‖ ^ 2 / (32 * l)) := by
      intro Q hQ y hy
      have h1 : ‖y‖ - ‖x‖ ≤ ‖y - x‖ := norm_sub_norm_le y x
      have h4 : 3 / 4 * ‖y‖ ≤ ‖y - x‖ := by linarith
      have h3 : (0:ℝ) ≤ 3 / 4 * ‖y‖ := by positivity
      have h5 : 9 / 16 * ‖y‖ ^ 2 ≤ ‖y - x‖ ^ 2 := by nlinarith
      have h6 : 9 * ‖y‖ ^ 2 / (32 * l) ≤ ‖y - x‖ ^ 2 / (2 * l) := by
        rw [div_le_div_iff₀ h32l h2l]; nlinarith
      have h7 : Q y ≤ ‖y‖ ^ 2 / (8 * l) := le_trans (le_abs_self _) (hQ y hy)
      have h9 : ‖y‖ ^ 2 / (8 * l) - 9 * ‖y‖ ^ 2 / (32 * l) = -(5 * ‖y‖ ^ 2 / (32 * l)) := by
        field_simp; ring
      linarith
    have hRMb' : R ≤ Mb := by linarith
    -- the competitor sets are nonempty (take `y = x`) and bounded above by `Nb`
    have hne : ∀ Q : F → ℝ, {w : ℝ | ∃ y : F, w = Q y - ‖y - x‖ ^ 2 / (2 * l)}.Nonempty :=
      fun Q => ⟨Q x - ‖x - x‖ ^ 2 / (2 * l), x, rfl⟩
    have hbdd : ∀ Q : F → ℝ, (∀ y : F, ‖y‖ ≤ Mb → |Q y| ≤ Nb) →
        (∀ y : F, Mb < ‖y‖ → |Q y| ≤ ‖y‖ ^ 2 / (8 * l)) →
        BddAbove {w : ℝ | ∃ y : F, w = Q y - ‖y - x‖ ^ 2 / (2 * l)} := by
      intro Q hQb hQf
      refine ⟨Nb, ?_⟩
      rintro w ⟨y, rfl⟩
      rcases le_or_gt ‖y‖ Mb with hy | hy
      · have h1 : Q y ≤ Nb := le_trans (le_abs_self _) (hQb y hy)
        have h2 : (0:ℝ) ≤ ‖y - x‖ ^ 2 / (2 * l) := by positivity
        linarith
      · have h1 := hfar Q hQf y hy
        have h2 : (0:ℝ) ≤ 5 * ‖y‖ ^ 2 / (32 * l) := by positivity
        linarith
    refine csSup_le (hne G) ?_
    rintro w ⟨y, rfl⟩
    rcases le_or_gt ‖y‖ Mf with hy | hy
    · -- near field: `G` and `H` are within `ε` of each other
      have h1 : G y - H y ≤ ε := le_trans (le_abs_self _) (hGH y hy)
      have h2 : H y - ‖y - x‖ ^ 2 / (2 * l)
          ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y - x‖ ^ 2 / (2 * l)} :=
        le_csSup (hbdd H hHb hHf) ⟨y, rfl⟩
      linarith
    · -- far field: the competitor `y = x` for `H` already beats this value
      have hMf0 : (0:ℝ) ≤ Mf := by linarith
      have h1 := hfar G hGf y (lt_of_le_of_lt hMbMf hy)
      have h2 : Nb ≤ 5 * ‖y‖ ^ 2 / (32 * l) := by
        rw [le_div_iff₀ h32l]; nlinarith
      have h3 : -Nb ≤ H x := by
        have h := abs_le.mp (hHb x (le_trans hx hRMb'))
        linarith [h.1]
      have h4 : H x - ‖x - x‖ ^ 2 / (2 * l)
          ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y - x‖ ^ 2 / (2 * l)} :=
        le_csSup (hbdd H hHb hHf) ⟨x, rfl⟩
      have h5 : ‖x - x‖ ^ 2 / (2 * l) = 0 := by simp
      linarith
  -- the two-sided form
  have key : ∀ (G H : F → ℝ) (x : F) (R Nb Mb Mf ε : ℝ),
      0 ≤ R → 0 ≤ Nb → 0 ≤ ε → ‖x‖ ≤ R → 4 * R ≤ Mb → Mb ≤ Mf →
      Nb * (32 * l) ≤ 5 * Mf ^ 2 →
      (∀ y : F, ‖y‖ ≤ Mb → |G y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |G y| ≤ ‖y‖ ^ 2 / (8 * l)) →
      (∀ y : F, ‖y‖ ≤ Mb → |H y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |H y| ≤ ‖y‖ ^ 2 / (8 * l)) →
      (∀ y : F, ‖y‖ ≤ Mf → |G y - H y| ≤ ε) →
      |sSup {w : ℝ | ∃ y : F, w = G y - ‖y - x‖ ^ 2 / (2 * l)}
        - sSup {w : ℝ | ∃ y : F, w = H y - ‖y - x‖ ^ 2 / (2 * l)}| ≤ ε := by
    intro G H x R Nb Mb Mf ε hR hNb hε hx hRMb hMbMf hNMf hGb hGf hHb hHf hGH
    rw [abs_sub_le_iff]
    refine ⟨?_, ?_⟩
    · linarith [half G H x R Nb Mb Mf ε hR hNb hε hx hRMb hMbMf hNMf hGb hGf hHb hHf hGH]
    · have hHG : ∀ y : F, ‖y‖ ≤ Mf → |H y - G y| ≤ ε := fun y hy => by
        rw [abs_sub_comm]; exact hGH y hy
      linarith [half H G x R Nb Mb Mf ε hR hNb hε hx hRMb hMbMf hNMf hHb hHf hGb hGf hHG]
  -- Step 1 of the NL proof: the uniform localization data, shared by both envelopes.
  -- `d` is the time offset of the competitor slice: `d = l` forward, `d = -l` backward.
  have setup : ∀ (d : ℝ) (K : Set (WithLp 2 (F × ℝ))), IsCompact K →
      (∀ z ∈ K, (ofLp z).2 ∈ I ∧ (ofLp z).2 + d ∈ I) → ∀ ε : ℝ, 0 < ε →
      ∃ (R Nb Mb Mf : ℝ) (J : Set ℝ),
        0 ≤ R ∧ 0 ≤ Nb ∧ 4 * R ≤ Mb ∧ Mb ≤ Mf ∧ Nb * (32 * l) ≤ 5 * Mf ^ 2 ∧
        (∀ z ∈ K, ‖(ofLp z).1‖ ≤ R) ∧
        (∀ z ∈ K, (ofLp z).2 + d ∈ J) ∧
        (∀ (y : F) (τ : ℝ), τ ∈ J → Mb < ‖y‖ → |f (toLp 2 (y, τ))| ≤ ‖y‖ ^ 2 / (8 * l)) ∧
        (∀ (j : ℕ) (y : F) (τ : ℝ), τ ∈ J → Mb < ‖y‖ →
          |fs j (toLp 2 (y, τ))| ≤ ‖y‖ ^ 2 / (8 * l)) ∧
        (∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb → |f (toLp 2 (y, τ))| ≤ Nb) ∧
        (∀ᶠ j in atTop,
          (∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb → |fs j (toLp 2 (y, τ))| ≤ Nb) ∧
          (∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mf →
            |fs j (toLp 2 (y, τ)) - f (toLp 2 (y, τ))| ≤ ε)) := by
    -- a ball-times-window slab is a compact subset of the domain
    have hslab : ∀ (r : ℝ) (J : Set ℝ), IsCompact J → J ⊆ I →
        IsCompact {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ r ∧ (ofLp z).2 ∈ J} ∧
        {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ r ∧ (ofLp z).2 ∈ J}
          ⊆ ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) := by
      intro r J hJ hJI
      refine ⟨?_, fun z hz => hJI hz.2⟩
      have he : {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ r ∧ (ofLp z).2 ∈ J}
          = (WithLp.homeomorphProd 2 F ℝ) ⁻¹' (Metric.closedBall (0:F) r ×ˢ J) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_prod, mem_closedBall, dist_zero_right,
          WithLp.homeomorphProd]
        rfl
      rw [he, Homeomorph.isCompact_preimage]
      exact (isCompact_closedBall _ _).prod hJ
    intro d K hK hKI ε hε
    -- the compact time window `J` of the NL proof
    set J : Set ℝ := (fun z : WithLp 2 (F × ℝ) => (ofLp z).2) '' K ∪
      (fun z : WithLp 2 (F × ℝ) => (ofLp z).2 + d) '' K with hJdef
    have hJc : IsCompact J := (hK.image (by fun_prop)).union (hK.image (by fun_prop))
    have hJI : J ⊆ I := by
      rintro τ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
      · exact (hKI z hz).1
      · exact (hKI z hz).2
    -- the spatial radius `R₀` of `K`
    obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn
      (f := fun z : WithLp 2 (F × ℝ) => (ofLp z).1) (by fun_prop)
    set R : ℝ := max R₀ 0 with hRdef
    have hR : 0 ≤ R := le_max_right _ _
    have hRK : ∀ z ∈ K, ‖(ofLp z).1‖ ≤ R := fun z hz => le_trans (hR₀ z hz) (le_max_left _ _)
    -- the growth radii `M₁`, `M₂` at tolerance `1/(8ℓ)`, and `M₃ = Mb`
    have hε8 : (0:ℝ) < 1 / (8 * l) := by positivity
    obtain ⟨M₁, -, hM₁⟩ := hgrow J hJI hJc (1 / (8 * l)) hε8
    obtain ⟨M₂, -, hM₂⟩ := hgrow0 J hJI hJc (1 / (8 * l)) hε8
    set Mb : ℝ := max (max M₁ M₂) (max (4 * R) 1) with hMbdef
    have hM₁b : M₁ ≤ Mb := le_trans (le_max_left _ _) (le_max_left _ _)
    have hM₂b : M₂ ≤ Mb := le_trans (le_max_right _ _) (le_max_left _ _)
    have hRMb : 4 * R ≤ Mb := le_trans (le_max_left _ _) (le_max_right _ _)
    have hdiv : ∀ y : F, 1 / (8 * l) * ‖y‖ ^ 2 = ‖y‖ ^ 2 / (8 * l) := by
      intro y; field_simp
    have hfarf : ∀ (y : F) (τ : ℝ), τ ∈ J → Mb < ‖y‖ →
        |f (toLp 2 (y, τ))| ≤ ‖y‖ ^ 2 / (8 * l) := by
      intro y τ hτ hy
      calc |f (toLp 2 (y, τ))| ≤ 1 / (8 * l) * ‖y‖ ^ 2 := by
            simpa using hM₂ (toLp 2 (y, τ))
              (by simpa using le_of_lt (lt_of_le_of_lt hM₂b hy)) (by simpa using hτ)
        _ = ‖y‖ ^ 2 / (8 * l) := hdiv y
    have hfarfs : ∀ (j : ℕ) (y : F) (τ : ℝ), τ ∈ J → Mb < ‖y‖ →
        |fs j (toLp 2 (y, τ))| ≤ ‖y‖ ^ 2 / (8 * l) := by
      intro j y τ hτ hy
      calc |fs j (toLp 2 (y, τ))| ≤ 1 / (8 * l) * ‖y‖ ^ 2 := by
            simpa using hM₁ j (toLp 2 (y, τ))
              (by simpa using le_of_lt (lt_of_le_of_lt hM₁b hy)) (by simpa using hτ)
        _ = ‖y‖ ^ 2 / (8 * l) := hdiv y
    -- the bound `N` on the inner slab `C₃`
    obtain ⟨hC₃c, hC₃I⟩ := hslab Mb J hJc hJI
    obtain ⟨Nf, hNf⟩ := hC₃c.exists_bound_of_continuousOn (hcont.mono hC₃I)
    set Nb : ℝ := max Nf 0 + 1 with hNbdef
    have hmax0 : (0:ℝ) ≤ max Nf 0 := le_max_right _ _
    have hNb : 0 ≤ Nb := by simp only [hNbdef]; linarith
    have hmemb : ∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb →
        (toLp 2 (y, τ) : WithLp 2 (F × ℝ)) ∈
          {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ Mb ∧ (ofLp z).2 ∈ J} := by
      intro y τ hτ hy; exact ⟨by simpa using hy, by simpa using hτ⟩
    have hnearf : ∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb → |f (toLp 2 (y, τ))| ≤ Nb := by
      intro y τ hτ hy
      have h1 := hNf _ (hmemb y τ hτ hy)
      have h2 : Nf ≤ max Nf 0 := le_max_left _ _
      simp only [hNbdef]
      simpa using le_trans h1 (by linarith)
    -- the outer radius `M`
    set Mf : ℝ := max Mb (Real.sqrt (Nb * (32 * l) / 5)) with hMfdef
    have hMbMf : Mb ≤ Mf := le_max_left _ _
    have hNMf : Nb * (32 * l) ≤ 5 * Mf ^ 2 := by
      have hc : (0:ℝ) ≤ Nb * (32 * l) / 5 := by positivity
      have h1 : Real.sqrt (Nb * (32 * l) / 5) ≤ Mf := le_max_right _ _
      nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg (Nb * (32 * l) / 5)]
    obtain ⟨hCc, hCI⟩ := hslab Mf J hJc hJI
    have hev1 := (Metric.tendstoUniformlyOn_iff.mp (hconv _ hC₃I hC₃c)) 1 one_pos
    have hev2 := (Metric.tendstoUniformlyOn_iff.mp (hconv _ hCI hCc)) ε hε
    refine ⟨R, Nb, Mb, Mf, J, hR, hNb, hRMb, hMbMf, hNMf, hRK, ?_, hfarf, hfarfs, hnearf, ?_⟩
    · intro z hz; exact Or.inr ⟨z, hz, rfl⟩
    · filter_upwards [hev1, hev2] with j hj1 hj2
      refine ⟨?_, ?_⟩
      · intro y τ hτ hy
        have h1 := hj1 _ (hmemb y τ hτ hy)
        rw [Real.dist_eq] at h1
        have h5 := abs_le.mp (hNf _ (hmemb y τ hτ hy))
        have h7 := abs_le.mp (show |fs j (toLp 2 (y, τ)) - f (toLp 2 (y, τ))| ≤ 1 by
          rw [abs_sub_comm]; linarith [h1])
        have h3 : Nf ≤ max Nf 0 := le_max_left _ _
        rw [abs_le]
        simp only [hNbdef]
        exact ⟨by linarith [h5.1, h7.1], by linarith [h5.2, h7.2]⟩
      · intro y τ hτ hy
        have h1 := hj2 _ (show (toLp 2 (y, τ) : WithLp 2 (F × ℝ)) ∈
            {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ Mf ∧ (ofLp z).2 ∈ J} from
          ⟨by simpa using hy, by simpa using hτ⟩)
        rw [Real.dist_eq] at h1
        rw [abs_sub_comm]
        linarith
  constructor
  · -- the forward envelope
    intro K hK hKI
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨R, Nb, Mb, Mf, J, hR, hNb, hRMb, hMbMf, hNMf, hRK, hJK, hfarf, hfarfs, hnearf,
      hev⟩ := setup l K hK hKI (ε / 2) (by positivity)
    filter_upwards [hev] with j hj
    obtain ⟨hjb, hjc⟩ := hj
    intro z hz
    have hτJ : (ofLp z).2 + l ∈ J := hJK z hz
    have hQP : ∀ g : WithLp 2 (F × ℝ) → ℝ, QuadEnvP g l z
        = sSup {w : ℝ | ∃ y : F,
            w = g (toLp 2 (y, (ofLp z).2 + l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      intro g; rw [QuadEnvP, if_neg (ne_of_gt hl)]
    rw [Real.dist_eq, hQP f, hQP (fs j), abs_sub_comm]
    refine lt_of_le_of_lt (key (fun y => fs j (toLp 2 (y, (ofLp z).2 + l)))
      (fun y => f (toLp 2 (y, (ofLp z).2 + l))) (ofLp z).1 R Nb Mb Mf (ε / 2)
      hR hNb (by positivity) (hRK z hz) hRMb hMbMf hNMf
      (fun y hy => hjb y _ hτJ hy) (fun y hy => hfarfs j y _ hτJ hy)
      (fun y hy => hnearf y _ hτJ hy) (fun y hy => hfarf y _ hτJ hy)
      (fun y hy => hjc y _ hτJ hy)) (by linarith)
  · -- the backward envelope: the same comparison applied to the negated profiles
    intro K hK hKI
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨R, Nb, Mb, Mf, J, hR, hNb, hRMb, hMbMf, hNMf, hRK, hJK, hfarf, hfarfs, hnearf,
      hev⟩ := setup (-l) K hK (fun z hz => ⟨(hKI z hz).1, by
        simpa [sub_eq_add_neg] using (hKI z hz).2⟩) (ε / 2) (by positivity)
    filter_upwards [hev] with j hj
    obtain ⟨hjb, hjc⟩ := hj
    intro z hz
    have hτJ : (ofLp z).2 - l ∈ J := by simpa [sub_eq_add_neg] using hJK z hz
    have hQM : ∀ g : WithLp 2 (F × ℝ) → ℝ, QuadEnvM g l z
        = -sSup {w : ℝ | ∃ y : F,
            w = -g (toLp 2 (y, (ofLp z).2 - l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
      intro g
      rw [QuadEnvM, if_neg (ne_of_gt hl)]
      have hset : -{w : ℝ | ∃ y : F,
            w = g (toLp 2 (y, (ofLp z).2 - l)) + ‖y - (ofLp z).1‖ ^ 2 / (2 * l)}
          = {w : ℝ | ∃ y : F,
            w = -g (toLp 2 (y, (ofLp z).2 - l)) - ‖y - (ofLp z).1‖ ^ 2 / (2 * l)} := by
        ext w
        simp only [Set.mem_neg]
        exact ⟨fun ⟨y, hy⟩ => ⟨y, by linarith⟩, fun ⟨y, hy⟩ => ⟨y, by linarith⟩⟩
      rw [← hset, Real.sSup_neg, neg_neg]
    rw [Real.dist_eq, hQM f, hQM (fs j), neg_sub_neg]
    refine lt_of_le_of_lt (key (fun y => -fs j (toLp 2 (y, (ofLp z).2 - l)))
      (fun y => -f (toLp 2 (y, (ofLp z).2 - l))) (ofLp z).1 R Nb Mb Mf (ε / 2)
      hR hNb (by positivity) (hRK z hz) hRMb hMbMf hNMf
      (fun y hy => by simpa using hjb y _ hτJ hy)
      (fun y hy => by simpa using hfarfs j y _ hτJ hy)
      (fun y hy => by simpa using hnearf y _ hτJ hy)
      (fun y hy => by simpa using hfarf y _ hτJ hy)
      (fun y hy => by
        have := hjc y _ hτJ hy
        calc |-fs j (toLp 2 (y, (ofLp z).2 - l)) - -f (toLp 2 (y, (ofLp z).2 - l))|
            = |fs j (toLp 2 (y, (ofLp z).2 - l)) - f (toLp 2 (y, (ofLp z).2 - l))| := by
              rw [neg_sub_neg, abs_sub_comm]
          _ ≤ ε / 2 := this)) (by linarith)
