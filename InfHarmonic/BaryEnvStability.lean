module

public import InfHarmonic.BaryEnvDuality
public import InfHarmonic.SubquadraticGrowth
public import InfHarmonic.UnifSubquadraticGrowth

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 5.2, stability: under locally uniform convergence with a common
subquadratic growth control the barycentric envelopes converge uniformly on
compact sets of admissible centers at each fixed positive parameter. -/
theorem BaryEnvStability (I : Set ℝ) (hI : IsOpen I) (f : WithLp 2 (F × ℝ) → ℝ)
    (fs : ℕ → WithLp 2 (F × ℝ) → ℝ)
    (hcont : ContinuousOn f ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hconts : ∀ j, ContinuousOn (fs j) ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I))
    (hconv : ∀ K ⊆ ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I), IsCompact K →
      TendstoUniformlyOn fs f atTop K)
    (hgrow : UnifSubquadraticGrowth I fs) (hgrow0 : SubquadraticGrowth I f)
    (s : ℝ) (hs : 0 < s) :
    ∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K → (∀ z ∈ K, (ofLp z).2 ∈ I) →
      TendstoUniformlyOn (fun j => BaryEnv (fs j) s) (BaryEnv f s) atTop K := by
  classical
  -- `BaryEnvDuality` is stated for a Borel-measurable `F`, because one of its clauses
  -- integrates against a probability measure.  Nothing used below depends on the choice
  -- and the conclusion never mentions it, so give `F` its Borel σ-algebra locally.
  letI : MeasurableSpace F := borel F
  haveI : BorelSpace F := ⟨rfl⟩
  have hs2 : (0 : ℝ) < 2 * s := by linarith
  have hs4 : (0 : ℝ) < 4 * s := by linarith
  have hs8 : (0 : ℝ) < 8 * s := by linarith
  -- each member of the sequence inherits the plain growth condition
  have hgrowj : ∀ j : ℕ, SubquadraticGrowth I (fs j) := by
    intro j J hJI hJc η hη
    obtain ⟨M, hM0, hMb⟩ := hgrow J hJI hJc η hη
    exact ⟨M, hM0, fun z hz hzJ => hMb j z hz hzJ⟩
  obtain ⟨-, hdualf, -, -, -⟩ := BaryEnvDuality I hI f hcont hgrow0
  -- ===================== the slope-shifted competitor sets are bounded above ========
  have hinner : ∀ (A x y : F) (R Λ : ℝ), 0 ≤ R → 0 ≤ Λ → ‖x‖ ≤ R → ‖A‖ ≤ Λ →
      |(inner ℝ A (y - x) : ℝ)| ≤ Λ * (‖y‖ + R) := by
    intro A x y R Λ hR hΛ hx hA
    have h1 : |(inner ℝ A (y - x) : ℝ)| ≤ ‖A‖ * ‖y - x‖ := abs_real_inner_le_norm A (y - x)
    have h2 : ‖y - x‖ ≤ ‖y‖ + R := le_trans (norm_sub_le y x) (by linarith)
    have h3 : ‖A‖ * ‖y - x‖ ≤ Λ * (‖y‖ + R) :=
      mul_le_mul hA h2 (norm_nonneg _) hΛ
    linarith
  have hpar : ∀ (y : F) (Λ : ℝ), 0 ≤ Λ → Λ * ‖y‖ - Λ ^ 2 * s ≤ ‖y‖ ^ 2 / (4 * s) := by
    intro y Λ hΛ
    rw [le_div_iff₀ hs4]
    nlinarith [sq_nonneg (‖y‖ - 2 * s * Λ)]
  have hbdd : ∀ (G : F → ℝ) (x A : F) (R Nb Mb Λ : ℝ),
      0 ≤ R → 0 ≤ Nb → 0 ≤ Λ → ‖x‖ ≤ R → R ≤ Mb → ‖A‖ ≤ Λ →
      (∀ y : F, ‖y‖ ≤ Mb → |G y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |G y| ≤ ‖y‖ ^ 2 / (4 * s)) →
      BddAbove {w : ℝ | ∃ y : F, w = G y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} := by
    intro G x A R Nb Mb Λ hR hNb hΛ hx hRMb hA hGb hGf
    refine ⟨Nb + Λ * (Mb + R) + Λ ^ 2 * s + Λ * R, ?_⟩
    rintro w ⟨y, rfl⟩
    have hi := abs_le.mp (hinner A x y R Λ hR hΛ hx hA)
    have hMb0 : 0 ≤ Mb := le_trans hR hRMb
    rcases le_or_gt ‖y‖ Mb with hy | hy
    · have h1 := (abs_le.mp (hGb y hy)).2
      have h2 : (0 : ℝ) ≤ ‖y‖ ^ 2 / (2 * s) := by positivity
      have h3 : Λ * (‖y‖ + R) ≤ Λ * (Mb + R) := by
        refine mul_le_mul_of_nonneg_left ?_ hΛ
        linarith
      have h4 : (0 : ℝ) ≤ Λ ^ 2 * s := by positivity
      have h5 : (0 : ℝ) ≤ Λ * R := by positivity
      linarith [hi.1]
    · have h1 := (abs_le.mp (hGf y hy)).2
      have h2 : ‖y‖ ^ 2 / (4 * s) + ‖y‖ ^ 2 / (4 * s) = ‖y‖ ^ 2 / (2 * s) := by
        field_simp; ring
      have h3 := hpar y Λ hΛ
      have h4 : (0 : ℝ) ≤ Nb := hNb
      have h5 : (0 : ℝ) ≤ Λ * (Mb + R) := by positivity
      linarith [hi.1]
  -- ===================== the one-sided comparison of the two suprema ===============
  have half : ∀ (G H : F → ℝ) (x A : F) (R Nb Mb Mf Λ η : ℝ),
      0 ≤ R → 0 ≤ Nb → 0 ≤ η → 0 ≤ Λ → ‖x‖ ≤ R → R ≤ Mb → ‖A‖ ≤ Λ →
      Mb ≤ Mf → 8 * s * Λ ≤ Mf → Λ * R + Nb + R ^ 2 / (2 * s) ≤ Mf ^ 2 / (8 * s) →
      (∀ y : F, ‖y‖ ≤ Mb → |G y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |G y| ≤ ‖y‖ ^ 2 / (4 * s)) →
      (∀ y : F, ‖y‖ ≤ Mb → |H y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |H y| ≤ ‖y‖ ^ 2 / (4 * s)) →
      (∀ y : F, ‖y‖ ≤ Mf → |G y - H y| ≤ η) →
      sSup {w : ℝ | ∃ y : F, w = G y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)}
        ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} + η := by
    intro G H x A R Nb Mb Mf Λ η hR hNb hη hΛ hx hRMb hA hMbMf hΛMf hNMf hGb hGf hHb hHf hGH
    have hMb0 : 0 ≤ Mb := le_trans hR hRMb
    have hHbdd := hbdd H x A R Nb Mb Λ hR hNb hΛ hx hRMb hA hHb hHf
    -- the competitor `y = x` for `H`, which beats every far competitor for `G`
    have hxval : -Nb - R ^ 2 / (2 * s)
        ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} := by
      have h1 : H x - ‖x‖ ^ 2 / (2 * s) - (inner ℝ A (x - x) : ℝ)
          ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} :=
        le_csSup hHbdd ⟨x, rfl⟩
      have h2 : (inner ℝ A (x - x) : ℝ) = 0 := by rw [sub_self, inner_zero_right]
      have h3 := (abs_le.mp (hHb x (le_trans hx hRMb))).1
      have h4 : ‖x‖ ^ 2 / (2 * s) ≤ R ^ 2 / (2 * s) := by
        refine div_le_div_of_nonneg_right ?_ hs2.le
        nlinarith [norm_nonneg x]
      rw [h2] at h1
      linarith
    refine csSup_le ⟨G x - ‖x‖ ^ 2 / (2 * s) - (inner ℝ A (x - x) : ℝ), x, rfl⟩ ?_
    rintro w ⟨y, rfl⟩
    rcases le_or_gt ‖y‖ Mf with hy | hy
    · -- near field: `G` and `H` are within `η`
      have h1 := (abs_le.mp (hGH y hy)).2
      have h2 : H y - ‖y‖ ^ 2 / (2 * s) - (inner ℝ A (y - x) : ℝ)
          ≤ sSup {w : ℝ | ∃ y : F, w = H y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} :=
        le_csSup hHbdd ⟨y, rfl⟩
      linarith
    · -- far field: the value is below `-Nb - R²/(2s)`
      have hyMb : Mb < ‖y‖ := lt_of_le_of_lt hMbMf hy
      have hy0 : 0 ≤ ‖y‖ := norm_nonneg y
      have h1 := (abs_le.mp (hGf y hyMb)).2
      have hi := abs_le.mp (hinner A x y R Λ hR hΛ hx hA)
      have h2 : ‖y‖ ^ 2 / (4 * s) + ‖y‖ ^ 2 / (4 * s) = ‖y‖ ^ 2 / (2 * s) := by
        field_simp; ring
      have hsplit : ‖y‖ ^ 2 / (8 * s) + ‖y‖ ^ 2 / (8 * s) = ‖y‖ ^ 2 / (4 * s) := by
        field_simp; ring
      have hq1 : Λ * ‖y‖ ≤ ‖y‖ ^ 2 / (8 * s) := by
        rw [le_div_iff₀ hs8]
        nlinarith [hΛMf, hMbMf, hy, hy0]
      have hq2 : Λ * R + Nb + R ^ 2 / (2 * s) ≤ ‖y‖ ^ 2 / (8 * s) := by
        refine le_trans hNMf ?_
        refine div_le_div_of_nonneg_right ?_ hs8.le
        have hMf0 : 0 ≤ Mf := le_trans hMb0 hMbMf
        nlinarith
      have hη0 : (0 : ℝ) ≤ η := hη
      linarith [hi.1, hxval]
  -- ===================== the slope localization =====================================
  have slopebd : ∀ (G : F → ℝ) (x A : F) (R Nb Mb V : ℝ),
      0 ≤ R → 0 ≤ Nb → ‖x‖ ≤ R → R + 1 ≤ Mb →
      (∀ y : F, ‖y‖ ≤ Mb → |G y| ≤ Nb) →
      (∀ y : F, Mb < ‖y‖ → |G y| ≤ ‖y‖ ^ 2 / (4 * s)) →
      V = sSup {w : ℝ | ∃ y : F, w = G y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} →
      V ≤ sSup {w : ℝ | ∃ y : F, w = G y - ‖y‖ ^ 2 / (2 * s) - inner ℝ (0 : F) (y - x)} →
      ‖A‖ ≤ 2 * Nb + Mb ^ 2 / (2 * s) := by
    intro G x A R Nb Mb V hR hNb hx hRMb hGb hGf hVA hV0
    have hRMb' : R ≤ Mb := by linarith
    have hMb0 : 0 ≤ Mb := le_trans hR hRMb'
    -- the value at the zero slope is at most `Nb`
    have hΓ0 : sSup {w : ℝ | ∃ y : F,
        w = G y - ‖y‖ ^ 2 / (2 * s) - inner ℝ (0 : F) (y - x)} ≤ Nb := by
      refine csSup_le ⟨G x - ‖x‖ ^ 2 / (2 * s) - (inner ℝ (0 : F) (x - x) : ℝ), x, rfl⟩ ?_
      rintro w ⟨y, rfl⟩
      have hz : (inner ℝ (0 : F) (y - x) : ℝ) = 0 := inner_zero_left _
      rw [hz]
      rcases le_or_gt ‖y‖ Mb with hy | hy
      · have h1 := (abs_le.mp (hGb y hy)).2
        have h2 : (0 : ℝ) ≤ ‖y‖ ^ 2 / (2 * s) := by positivity
        linarith
      · have h1 := (abs_le.mp (hGf y hy)).2
        have h2 : ‖y‖ ^ 2 / (4 * s) + ‖y‖ ^ 2 / (4 * s) = ‖y‖ ^ 2 / (2 * s) := by
          field_simp; ring
        have h3 : (0 : ℝ) ≤ ‖y‖ ^ 2 / (4 * s) := by positivity
        linarith
    rcases eq_or_ne A 0 with hA0 | hA0
    · have h1 : (0 : ℝ) ≤ Mb ^ 2 / (2 * s) := by positivity
      rw [hA0]
      simp only [norm_zero]
      linarith
    · -- the competitor `y = x - A/‖A‖` sees the slope
      have hAn : 0 < ‖A‖ := norm_pos_iff.mpr hA0
      obtain ⟨y₀, hy₀d⟩ : ∃ p : F, p = x - (‖A‖)⁻¹ • A := ⟨_, rfl⟩
      have hsub : y₀ - x = -((‖A‖)⁻¹ • A) := by rw [hy₀d]; abel
      have hny : ‖(‖A‖)⁻¹ • A‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (ne_of_gt hAn)]
      have hy₀n : ‖y₀‖ ≤ Mb := by
        have h1 : ‖y₀‖ ≤ ‖x‖ + ‖(‖A‖)⁻¹ • A‖ := by
          rw [hy₀d]; exact norm_sub_le x _
        rw [hny] at h1
        linarith
      have hinnerv : (inner ℝ A (y₀ - x) : ℝ) = -‖A‖ := by
        rw [hsub, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hle : G y₀ - ‖y₀‖ ^ 2 / (2 * s) - (inner ℝ A (y₀ - x) : ℝ)
          ≤ sSup {w : ℝ | ∃ y : F, w = G y - ‖y‖ ^ 2 / (2 * s) - inner ℝ A (y - x)} :=
        le_csSup (hbdd G x A R Nb Mb ‖A‖ hR hNb hAn.le hx hRMb' le_rfl hGb hGf) ⟨y₀, rfl⟩
      have h1 := (abs_le.mp (hGb y₀ hy₀n)).1
      have h2 : ‖y₀‖ ^ 2 / (2 * s) ≤ Mb ^ 2 / (2 * s) := by
        refine div_le_div_of_nonneg_right ?_ hs2.le
        nlinarith [norm_nonneg y₀]
      rw [hinnerv] at hle
      rw [hVA] at hV0
      linarith
  -- ===================== the uniform localization data ==============================
  -- a ball-times-window slab is a compact subset of the domain
  have hslab : ∀ (r : ℝ) (J : Set ℝ), IsCompact J → J ⊆ I →
      IsCompact {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ r ∧ (ofLp z).2 ∈ J} ∧
      {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ r ∧ (ofLp z).2 ∈ J}
        ⊆ ((fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' I) := by
    intro r J hJ hJI
    refine ⟨?_, fun z hz => hJI hz.2⟩
    have he : {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ r ∧ (ofLp z).2 ∈ J}
        = (WithLp.homeomorphProd 2 F ℝ) ⁻¹' (Metric.closedBall (0 : F) r ×ˢ J) := by
      ext z
      simp only [Set.mem_preimage, Set.mem_prod, mem_closedBall, dist_zero_right,
        WithLp.homeomorphProd]
      rfl
    rw [he, Homeomorph.isCompact_preimage]
    exact (isCompact_closedBall _ _).prod hJ
  intro K hK hKI
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  -- the compact time window and the spatial radius of `K`
  obtain ⟨J, hJdef⟩ : ∃ t : Set ℝ, t = (fun z : WithLp 2 (F × ℝ) => (ofLp z).2) '' K :=
    ⟨_, rfl⟩
  have hJc : IsCompact J := by rw [hJdef]; exact hK.image (by fun_prop)
  have hJI : J ⊆ I := by
    rw [hJdef]; rintro τ ⟨z, hz, rfl⟩; exact hKI z hz
  have hJK : ∀ z ∈ K, (ofLp z).2 ∈ J := by
    intro z hz; rw [hJdef]; exact ⟨z, hz, rfl⟩
  obtain ⟨R₀, hR₀⟩ := hK.exists_bound_of_continuousOn
    (f := fun z : WithLp 2 (F × ℝ) => (ofLp z).1) (by fun_prop)
  obtain ⟨R, hRdef⟩ : ∃ t : ℝ, t = max R₀ 0 := ⟨_, rfl⟩
  have hR : 0 ≤ R := by rw [hRdef]; exact le_max_right _ _
  have hRK : ∀ z ∈ K, ‖(ofLp z).1‖ ≤ R := fun z hz => by
    rw [hRdef]; exact le_trans (hR₀ z hz) (le_max_left _ _)
  -- the common far-field radius, at tolerance `1/(4s)`
  have hεs : (0 : ℝ) < 1 / (4 * s) := by positivity
  obtain ⟨M₁, -, hM₁⟩ := hgrow J hJI hJc (1 / (4 * s)) hεs
  obtain ⟨M₂, -, hM₂⟩ := hgrow0 J hJI hJc (1 / (4 * s)) hεs
  obtain ⟨Mb, hMbdef⟩ : ∃ t : ℝ, t = max (max M₁ M₂) (max (R + 1) 1) := ⟨_, rfl⟩
  have hM₁b : M₁ ≤ Mb := by rw [hMbdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hM₂b : M₂ ≤ Mb := by rw [hMbdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hRMb : R + 1 ≤ Mb := by
    rw [hMbdef]; exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hRMb' : R ≤ Mb := by linarith
  have hdiv : ∀ y : F, 1 / (4 * s) * ‖y‖ ^ 2 = ‖y‖ ^ 2 / (4 * s) := by
    intro y; field_simp
  have hfarf : ∀ (y : F) (τ : ℝ), τ ∈ J → Mb < ‖y‖ →
      |f (toLp 2 (y, τ))| ≤ ‖y‖ ^ 2 / (4 * s) := by
    intro y τ hτ hy
    calc |f (toLp 2 (y, τ))| ≤ 1 / (4 * s) * ‖y‖ ^ 2 := by
          simpa using hM₂ (toLp 2 (y, τ))
            (by simpa using le_of_lt (lt_of_le_of_lt hM₂b hy)) (by simpa using hτ)
      _ = ‖y‖ ^ 2 / (4 * s) := hdiv y
  have hfarfs : ∀ (j : ℕ) (y : F) (τ : ℝ), τ ∈ J → Mb < ‖y‖ →
      |fs j (toLp 2 (y, τ))| ≤ ‖y‖ ^ 2 / (4 * s) := by
    intro j y τ hτ hy
    calc |fs j (toLp 2 (y, τ))| ≤ 1 / (4 * s) * ‖y‖ ^ 2 := by
          simpa using hM₁ j (toLp 2 (y, τ))
            (by simpa using le_of_lt (lt_of_le_of_lt hM₁b hy)) (by simpa using hτ)
      _ = ‖y‖ ^ 2 / (4 * s) := hdiv y
  -- the near-field bound on the inner slab
  obtain ⟨hC₃c, hC₃I⟩ := hslab Mb J hJc hJI
  obtain ⟨Nf, hNf⟩ := hC₃c.exists_bound_of_continuousOn (hcont.mono hC₃I)
  obtain ⟨Nb, hNbdef⟩ : ∃ t : ℝ, t = max Nf 0 + 1 := ⟨_, rfl⟩
  have hmax0 : (0 : ℝ) ≤ max Nf 0 := le_max_right _ _
  have hNb : 0 ≤ Nb := by rw [hNbdef]; linarith
  have hmemb : ∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb →
      (toLp 2 (y, τ) : WithLp 2 (F × ℝ)) ∈
        {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ Mb ∧ (ofLp z).2 ∈ J} :=
    fun y τ hτ hy => ⟨by simpa using hy, by simpa using hτ⟩
  have hnearf : ∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb → |f (toLp 2 (y, τ))| ≤ Nb := by
    intro y τ hτ hy
    have h1 := hNf _ (hmemb y τ hτ hy)
    have h2 : Nf ≤ max Nf 0 := le_max_left _ _
    rw [hNbdef]
    simpa using le_trans h1 (by linarith)
  -- the slope radius and the outer radius, both explicit in the data so far
  obtain ⟨Λ, hΛdef⟩ : ∃ t : ℝ, t = 2 * Nb + Mb ^ 2 / (2 * s) := ⟨_, rfl⟩
  have hΛ : 0 ≤ Λ := by rw [hΛdef]; positivity
  obtain ⟨Mf, hMfdef⟩ : ∃ t : ℝ, t = max (max Mb (8 * s * Λ))
      (Real.sqrt (8 * s * (Λ * R + Nb + R ^ 2 / (2 * s)))) := ⟨_, rfl⟩
  have hMbMf : Mb ≤ Mf := by
    rw [hMfdef]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hΛMf : 8 * s * Λ ≤ Mf := by
    rw [hMfdef]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hNMf : Λ * R + Nb + R ^ 2 / (2 * s) ≤ Mf ^ 2 / (8 * s) := by
    have hc : (0 : ℝ) ≤ 8 * s * (Λ * R + Nb + R ^ 2 / (2 * s)) := by positivity
    have h1 : Real.sqrt (8 * s * (Λ * R + Nb + R ^ 2 / (2 * s))) ≤ Mf := by
      rw [hMfdef]; exact le_max_right _ _
    rw [le_div_iff₀ hs8]
    nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg (8 * s * (Λ * R + Nb + R ^ 2 / (2 * s)))]
  -- uniform convergence on the two slabs: tolerance `1` inside, `ε/2` out to `Mf`
  obtain ⟨hCc, hCI⟩ := hslab Mf J hJc hJI
  have hev1 := (Metric.tendstoUniformlyOn_iff.mp (hconv _ hC₃I hC₃c)) 1 one_pos
  have hev2 := (Metric.tendstoUniformlyOn_iff.mp (hconv _ hCI hCc)) (ε / 2) (by positivity)
  filter_upwards [hev1, hev2] with j hj1 hj2
  -- the near bound for `fs j`, from the inner slab, and the `ε/2` closeness out to `Mf`
  have hnearfs : ∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mb → |fs j (toLp 2 (y, τ))| ≤ Nb := by
    intro y τ hτ hy
    have h1 := hj1 _ (hmemb y τ hτ hy)
    rw [Real.dist_eq] at h1
    have h5 := abs_le.mp (hNf _ (hmemb y τ hτ hy))
    have h7 := abs_le.mp (show |fs j (toLp 2 (y, τ)) - f (toLp 2 (y, τ))| ≤ 1 by
      rw [abs_sub_comm]; linarith [h1])
    have h3 : Nf ≤ max Nf 0 := le_max_left _ _
    rw [abs_le, hNbdef]
    exact ⟨by linarith [h5.1, h7.1], by linarith [h5.2, h7.2]⟩
  have hclose : ∀ (y : F) (τ : ℝ), τ ∈ J → ‖y‖ ≤ Mf →
      |fs j (toLp 2 (y, τ)) - f (toLp 2 (y, τ))| ≤ ε / 2 := by
    intro y τ hτ hy
    have h1 := hj2 _ (show (toLp 2 (y, τ) : WithLp 2 (F × ℝ)) ∈
        {z : WithLp 2 (F × ℝ) | ‖(ofLp z).1‖ ≤ Mf ∧ (ofLp z).2 ∈ J} from
      ⟨by simpa using hy, by simpa using hτ⟩)
    rw [Real.dist_eq] at h1
    rw [abs_sub_comm]
    linarith
  obtain ⟨-, hdualj, -, -, -⟩ := BaryEnvDuality I hI (fs j) (hconts j) (hgrowj j)
  intro z hz
  obtain ⟨A₀, hA₀eq, hA₀le⟩ := hdualf s z hs (hKI z hz)
  obtain ⟨B₀, hB₀eq, hB₀le⟩ := hdualj s z hs (hKI z hz)
  have hτJ : (ofLp z).2 ∈ J := hJK z hz
  have hxR : ‖(ofLp z).1‖ ≤ R := hRK z hz
  -- both duality minimizers have norm at most `Λ`
  have hA₀n : ‖A₀‖ ≤ Λ := by
    rw [hΛdef]
    exact slopebd (fun y : F => f (toLp 2 (y, (ofLp z).2))) (ofLp z).1 A₀ R Nb Mb _
      hR hNb hxR hRMb (fun y hy => hnearf y _ hτJ hy) (fun y hy => hfarf y _ hτJ hy)
      hA₀eq (hA₀le 0)
  have hB₀n : ‖B₀‖ ≤ Λ := by
    rw [hΛdef]
    exact slopebd (fun y : F => fs j (toLp 2 (y, (ofLp z).2))) (ofLp z).1 B₀ R Nb Mb _
      hR hNb hxR hRMb (fun y hy => hnearfs y _ hτJ hy) (fun y hy => hfarfs j y _ hτJ hy)
      hB₀eq (hB₀le 0)
  -- the two comparisons, at `A₀` for the upper bound and at `B₀` for the lower
  have hcmp1 : sSup {w : ℝ | ∃ y : F, w = fs j (toLp 2 (y, (ofLp z).2))
          - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - (ofLp z).1)}
      ≤ sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
          - ‖y‖ ^ 2 / (2 * s) - inner ℝ A₀ (y - (ofLp z).1)} + ε / 2 :=
    half (fun y : F => fs j (toLp 2 (y, (ofLp z).2)))
      (fun y : F => f (toLp 2 (y, (ofLp z).2))) (ofLp z).1 A₀ R Nb Mb Mf Λ (ε / 2)
      hR hNb (by positivity) hΛ hxR hRMb' hA₀n hMbMf hΛMf hNMf
      (fun y hy => hnearfs y _ hτJ hy) (fun y hy => hfarfs j y _ hτJ hy)
      (fun y hy => hnearf y _ hτJ hy) (fun y hy => hfarf y _ hτJ hy)
      (fun y hy => hclose y _ hτJ hy)
  have hcmp2 : sSup {w : ℝ | ∃ y : F, w = f (toLp 2 (y, (ofLp z).2))
          - ‖y‖ ^ 2 / (2 * s) - inner ℝ B₀ (y - (ofLp z).1)}
      ≤ sSup {w : ℝ | ∃ y : F, w = fs j (toLp 2 (y, (ofLp z).2))
          - ‖y‖ ^ 2 / (2 * s) - inner ℝ B₀ (y - (ofLp z).1)} + ε / 2 :=
    half (fun y : F => f (toLp 2 (y, (ofLp z).2)))
      (fun y : F => fs j (toLp 2 (y, (ofLp z).2))) (ofLp z).1 B₀ R Nb Mb Mf Λ (ε / 2)
      hR hNb (by positivity) hΛ hxR hRMb' hB₀n hMbMf hΛMf hNMf
      (fun y hy => hnearf y _ hτJ hy) (fun y hy => hfarf y _ hτJ hy)
      (fun y hy => hnearfs y _ hτJ hy) (fun y hy => hfarfs j y _ hτJ hy)
      (fun y hy => by rw [abs_sub_comm]; exact hclose y _ hτJ hy)
  rw [Real.dist_eq, abs_sub_lt_iff]
  have hu := hB₀le A₀
  have hl := hA₀le B₀
  constructor
  · linarith [hA₀eq, hcmp2, hB₀eq]
  · linarith [hB₀eq, hcmp1, hA₀eq]
