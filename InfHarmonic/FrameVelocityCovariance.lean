module

public import InfHarmonic.FrameGapCovariance
public import InfHarmonic.IsStepPair
public import InfHarmonic.DPSpatialRegularity
public import InfHarmonic.BaryEnvSandwich
public import InfHarmonic.BaryEnvDuality
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.EnvelopeCompetitorBounds
public import InfHarmonic.ContactEnvPositiveTimeRegularity

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 6.5, velocity part, equation (6.13): the images of an optimizing step
pair under the contact frame based at a fit at `(x₀, r)` of radius `r` are
optimizing steps of size `ε / r` for the transformed pair, and the three
velocities transform by subtraction of `p₀`, so that the discrepancies from the
reference velocity are unchanged. -/
theorem FrameVelocityCovariance (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (r : ℝ) (hr : 0 < r) (x₀ p₀ : F) (a₀ : ℝ)
    (hfit : IsFit C₀ v (toLp 2 (x₀, r)) r p₀ a₀)
    (vbar : WithLp 2 (F × ℝ) → ℝ)
    (hvbar : vbar = fun ξ => FrameChange v (toLp 2 (x₀, r)) r p₀ a₀
      (ξ - toLp 2 ((0 : F), (1 : ℝ))))
    (ε : ℝ) (hε : 0 < ε) (z zp zm : WithLp 2 (F × ℝ)) (hz : ε < (ofLp z).2)
    (hstep : IsStepPair v κ ε z zp zm)
    (Q₀ : F)
    (hQ₀ : HasGradientAt
      (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp z).2)))
      Q₀ (ofLp z).1)
    (ζ ζp ζm : WithLp 2 (F × ℝ))
    (hζ : ζ = toLp 2 (r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀),
      (ofLp z).2 / r))
    (hζp : ζp = toLp 2 (r⁻¹ • ((ofLp zp).1 - x₀ - ((ofLp zp).2 - r) • p₀),
      (ofLp zp).2 / r))
    (hζm : ζm = toLp 2 (r⁻¹ • ((ofLp zm).1 - x₀ - ((ofLp zm).2 - r) • p₀),
      (ofLp zm).2 / r)) :
    IsStepPair vbar κ (ε / r) ζ ζp ζm ∧
    (ε / r)⁻¹ • ((ofLp ζp).1 - (ofLp ζ).1)
        = ε⁻¹ • ((ofLp zp).1 - (ofLp z).1) - p₀ ∧
    (ε / r)⁻¹ • ((ofLp ζ).1 - (ofLp ζm).1)
        = ε⁻¹ • ((ofLp z).1 - (ofLp zm).1) - p₀ ∧
    HasGradientAt
      (fun y' : F => QuadEnvP (ContactEnv vbar κ) (ε / r) (toLp 2 (y', (ofLp ζ).2)))
      (Q₀ - p₀) (ofLp ζ).1 ∧
    (ε / r)⁻¹ • ((ofLp ζp).1 - (ofLp ζ).1) - (Q₀ - p₀)
        = ε⁻¹ • ((ofLp zp).1 - (ofLp z).1) - Q₀ ∧
    (ε / r)⁻¹ • ((ofLp ζ).1 - (ofLp ζm).1) - (Q₀ - p₀)
        = ε⁻¹ • ((ofLp z).1 - (ofLp zm).1) - Q₀ := by
  classical
  -- ===== Step 0: the standing numerical facts =====
  have hrne : r ≠ 0 := ne_of_gt hr
  have hεne : ε ≠ 0 := ne_of_gt hε
  have ht0 : (0 : ℝ) < (ofLp z).2 := by linarith
  have hεr : (0 : ℝ) < ε / r := div_pos hε hr
  have hεrne : ε / r ≠ 0 := ne_of_gt hεr
  have hrcanL : ∀ X : ℝ, r * (X / r) = X := by intro X; field_simp
  have hrcanR : ∀ X : ℝ, (r * X) / r = X := by intro X; field_simp
  have hnormsmul : ∀ (cs : ℝ) (u : F), ‖cs • u‖ ^ 2 = cs ^ 2 * ‖u‖ ^ 2 := by
    intro cs u; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hPdef : ∀ (f : WithLp 2 (F × ℝ) → ℝ) (L : ℝ) (w : WithLp 2 (F × ℝ)), L ≠ 0 →
      QuadEnvP f L w = sSup {u : ℝ | ∃ y : F,
        u = f (toLp 2 (y, (ofLp w).2 + L)) - ‖y - (ofLp w).1‖ ^ 2 / (2 * L)} := by
    intro f L w hL; rw [QuadEnvP, if_neg hL]
  have hMdef : ∀ (f : WithLp 2 (F × ℝ) → ℝ) (L : ℝ) (w : WithLp 2 (F × ℝ)), L ≠ 0 →
      QuadEnvM f L w = sInf {u : ℝ | ∃ y : F,
        u = f (toLp 2 (y, (ofLp w).2 - L)) + ‖y - (ofLp w).1‖ ^ 2 / (2 * L)} := by
    intro f L w hL; rw [QuadEnvM, if_neg hL]
  -- ===== Step 1: the frame map, the affine correction, and the corresponding states =====
  obtain ⟨Θ, hΘ⟩ : ∃ S : WithLp 2 (F × ℝ) → WithLp 2 (F × ℝ), S = fun ξ =>
      toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ a : WithLp 2 (F × ℝ) → ℝ, a = fun ξ =>
      v (toLp 2 (x₀, r)) / r + inner ℝ p₀ (ofLp ξ).1
        + (a₀ + ‖p₀‖ ^ 2 / 2) * ((ofLp ξ).2 - 1) := ⟨_, rfl⟩
  have hΘval : ∀ ξ : WithLp 2 (F × ℝ),
      Θ ξ = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
    intro ξ; rw [hΘ]
  have hΘfst : ∀ ξ : WithLp 2 (F × ℝ),
      (ofLp (Θ ξ)).1 = x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀) := by
    intro ξ; rw [hΘval]
  have hΘsnd : ∀ ξ : WithLp 2 (F × ℝ), (ofLp (Θ ξ)).2 = r * (ofLp ξ).2 := by
    intro ξ; rw [hΘval]
  have hAlp : ∀ (u : F) (σ : ℝ), A (toLp 2 (u, σ))
      = v (toLp 2 (x₀, r)) / r + inner ℝ p₀ u + (a₀ + ‖p₀‖ ^ 2 / 2) * (σ - 1) := by
    intro u σ; rw [hA]
  have hAval : ∀ ξ : WithLp 2 (F × ℝ), A ξ
      = v (toLp 2 (x₀, r)) / r + inner ℝ p₀ (ofLp ξ).1
        + (a₀ + ‖p₀‖ ^ 2 / 2) * ((ofLp ξ).2 - 1) := by
    intro ξ; rw [hA]
  have hvbarval : ∀ ξ : WithLp 2 (F × ℝ),
      vbar ξ = FrameChange v (toLp 2 (x₀, r)) r p₀ a₀ (ξ - toLp 2 ((0 : F), (1 : ℝ))) := by
    intro ξ; rw [hvbar]
  have hofs1 : ∀ ξ : WithLp 2 (F × ℝ),
      (ofLp (ξ - toLp 2 ((0 : F), (1 : ℝ)))).1 = (ofLp ξ).1 := by intro ξ; simp
  have hofs2 : ∀ ξ : WithLp 2 (F × ℝ),
      (ofLp (ξ - toLp 2 ((0 : F), (1 : ℝ)))).2 = (ofLp ξ).2 - 1 := by intro ξ; simp
  -- the inverse frame map is a genuine inverse: every `X''` is in the image of `T_c`
  have hsurj : ∀ (cf : ℝ) (X : F), ∃ y' : F, X = x₀ + r • (y' + cf • p₀) := by
    intro cf X
    refine ⟨r⁻¹ • (X - x₀) - cf • p₀, ?_⟩
    rw [show r⁻¹ • (X - x₀) - cf • p₀ + cf • p₀ = r⁻¹ • (X - x₀) from by abel,
      smul_smul, mul_inv_cancel₀ hrne, one_smul]
    abel
  -- ===== eq:fvc-vbar : `v` at the corresponding point splits as `r (v̄ + A)` =====
  have hsplitv : ∀ ξ : WithLp 2 (F × ℝ), v (Θ ξ) = r * (vbar ξ + A ξ) := by
    intro ξ
    have hpt : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
        + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
        = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * (ofLp ξ).2) := by
      have h1 : (toLp 2 (x₀, r) : WithLp 2 (F × ℝ))
          + toLp 2 (r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀), r * ((ofLp ξ).2 - 1))
          = toLp 2 (x₀ + r • ((ofLp ξ).1 + ((ofLp ξ).2 - 1) • p₀),
              r + r * ((ofLp ξ).2 - 1)) := rfl
      rw [h1, show r + r * ((ofLp ξ).2 - 1) = r * (ofLp ξ).2 from by ring]
    rw [hΘval, hvbarval, hAval]
    simp only [FrameChange]
    rw [hofs1, hofs2, hpt]
    field_simp
    ring
  -- ===== Step 2: `W̄` is the same frame change applied to `W` -- a citation, not a proof =====
  obtain ⟨-, hFGcontact⟩ :=
    FrameGapCovariance C₀ κ hC₀ hκ v hv hJ r hr x₀ p₀ a₀ hfit
  have hsplitW : ∀ ξ : WithLp 2 (F × ℝ), 0 < (ofLp ξ).2 →
      ContactEnv v κ (Θ ξ) = r * (ContactEnv vbar κ ξ + A ξ) := by
    intro ξ hξ
    have h1 := hFGcontact ξ hξ
    rw [← hvbar, ← hvbarval ξ, ← hΘval ξ, hsplitv ξ] at h1
    rw [eq_div_iff hrne] at h1
    linarith [h1]
  -- ===== Step 0 (continued): admissibility of `W` on `(0,∞)` and of `v` on `ℝ` =====
  obtain ⟨hWcont, hWgrow, -⟩ :=
    ContactEnvPositiveTimeRegularity C₀ κ hC₀ hκ v hv hcent hJ
  have hIuniv : ((fun ξ : WithLp 2 (F × ℝ) => (ofLp ξ).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvcont : ContinuousOn v
      ((fun ξ : WithLp 2 (F × ℝ) => (ofLp ξ).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc η hη
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc η hη
    exact ⟨M, hM0, fun ξ hξ hξJ => hMb v hv hcent ξ hξ hξJ⟩
  obtain ⟨hdomWP, -, -⟩ :=
    EnvelopeCompetitorBounds (Set.Ioi (0 : ℝ)) (ContactEnv v κ) hWcont hWgrow
  obtain ⟨-, hdomvM, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont hvgrow
  -- ===== Step 3: the competitor correspondences =====
  have hcorrP : ∀ (ξ : WithLp 2 (F × ℝ)) (σ l : ℝ), 0 < (ofLp ξ).2 → 0 < σ → l = r * σ →
      ∀ y' : F,
      ContactEnv vbar κ (toLp 2 (y', (ofLp ξ).2 + σ)) - ‖y' - (ofLp ξ).1‖ ^ 2 / (2 * σ)
        = (ContactEnv v κ (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀),
              (ofLp (Θ ξ)).2 + l))
            - ‖x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀) - (ofLp (Θ ξ)).1‖ ^ 2 / (2 * l)) / r
          + (-(A ξ) - a₀ * σ) := by
    intro ξ σ l hξ hσ hl y'
    have hσne : σ ≠ 0 := ne_of_gt hσ
    have hpt : (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀), (ofLp (Θ ξ)).2 + l)
        : WithLp 2 (F × ℝ)) = Θ (toLp 2 (y', (ofLp ξ).2 + σ)) := by
      rw [hΘsnd ξ, hΘval (toLp 2 (y', (ofLp ξ).2 + σ))]
      show (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀), r * (ofLp ξ).2 + l)
          : WithLp 2 (F × ℝ))
        = toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀), r * ((ofLp ξ).2 + σ))
      rw [show r * (ofLp ξ).2 + l = r * ((ofLp ξ).2 + σ) from by rw [hl]; ring]
    have hdisp : x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀) - (ofLp (Θ ξ)).1
        = r • (y' - (ofLp ξ).1 + σ • p₀) := by rw [hΘfst]; module
    have hnorm : ‖r • (y' - (ofLp ξ).1 + σ • p₀)‖ ^ 2
        = r ^ 2 * (‖y' - (ofLp ξ).1‖ ^ 2
            + 2 * (σ * (inner ℝ p₀ y' - inner ℝ p₀ (ofLp ξ).1)) + σ ^ 2 * ‖p₀‖ ^ 2) := by
      rw [hnormsmul]
      congr 1
      rw [norm_add_sq_real (y' - (ofLp ξ).1) (σ • p₀), real_inner_smul_right,
        real_inner_comm, inner_sub_right, hnormsmul]
    rw [hpt, hsplitW (toLp 2 (y', (ofLp ξ).2 + σ))
        (show (0 : ℝ) < (ofLp ξ).2 + σ by linarith), hdisp, hnorm, hAlp, hAval, hl]
    field_simp
    ring
  have hcorrM : ∀ (ξ : WithLp 2 (F × ℝ)) (σ l : ℝ), 0 < σ → l = r * σ → ∀ y' : F,
      vbar (toLp 2 (y', (ofLp ξ).2 - σ)) + ‖y' - (ofLp ξ).1‖ ^ 2 / (2 * σ)
        = (v (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀), (ofLp (Θ ξ)).2 - l))
            + ‖x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀) - (ofLp (Θ ξ)).1‖ ^ 2 / (2 * l)) / r
          + (-(A ξ) + a₀ * σ) := by
    intro ξ σ l hσ hl y'
    have hσne : σ ≠ 0 := ne_of_gt hσ
    have hpt : (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀), (ofLp (Θ ξ)).2 - l)
        : WithLp 2 (F × ℝ)) = Θ (toLp 2 (y', (ofLp ξ).2 - σ)) := by
      rw [hΘsnd ξ, hΘval (toLp 2 (y', (ofLp ξ).2 - σ))]
      show (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀), r * (ofLp ξ).2 - l)
          : WithLp 2 (F × ℝ))
        = toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀), r * ((ofLp ξ).2 - σ))
      rw [show r * (ofLp ξ).2 - l = r * ((ofLp ξ).2 - σ) from by rw [hl]; ring]
    have hdisp : x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀) - (ofLp (Θ ξ)).1
        = r • (y' - (ofLp ξ).1 - σ • p₀) := by rw [hΘfst]; module
    have hnorm : ‖r • (y' - (ofLp ξ).1 - σ • p₀)‖ ^ 2
        = r ^ 2 * (‖y' - (ofLp ξ).1‖ ^ 2
            - 2 * (σ * (inner ℝ p₀ y' - inner ℝ p₀ (ofLp ξ).1)) + σ ^ 2 * ‖p₀‖ ^ 2) := by
      rw [hnormsmul]
      congr 1
      rw [norm_sub_sq_real (y' - (ofLp ξ).1) (σ • p₀), real_inner_smul_right,
        real_inner_comm, inner_sub_right, hnormsmul]
    rw [hpt, hsplitv (toLp 2 (y', (ofLp ξ).2 - σ)), hdisp, hnorm, hAlp, hAval, hl]
    field_simp
    ring
  -- ===== Step 3: the two envelope laws =====
  have hlawP : ∀ (ξ : WithLp 2 (F × ℝ)) (σ l : ℝ), 0 < (ofLp ξ).2 → 0 < σ → l = r * σ →
      QuadEnvP (ContactEnv vbar κ) σ ξ
        = QuadEnvP (ContactEnv v κ) l (Θ ξ) / r + (-(A ξ) - a₀ * σ) := by
    intro ξ σ l hξ hσ hl
    have hσne : σ ≠ 0 := ne_of_gt hσ
    have hlpos : 0 < l := by rw [hl]; positivity
    have hlne : l ≠ 0 := ne_of_gt hlpos
    have hΘ2 : (ofLp (Θ ξ)).2 = r * (ofLp ξ).2 := hΘsnd ξ
    obtain ⟨hdom, hleast⟩ := hdomWP l (Θ ξ) hlpos
      (Set.mem_Ioi.mpr (by rw [hΘ2]; positivity))
      (Set.mem_Ioi.mpr (by rw [hΘ2]; have : (0:ℝ) < r * (ofLp ξ).2 := by positivity
                           linarith))
    have hbar : ∀ y' : F,
        ContactEnv vbar κ (toLp 2 (y', (ofLp ξ).2 + σ)) - ‖y' - (ofLp ξ).1‖ ^ 2 / (2 * σ)
          ≤ QuadEnvP (ContactEnv v κ) l (Θ ξ) / r + (-(A ξ) - a₀ * σ) := by
      intro y'
      rw [hcorrP ξ σ l hξ hσ hl y']
      have hd := div_le_div_of_nonneg_right (hdom (x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀)))
        hr.le
      linarith [hd]
    have hne : ({u : ℝ | ∃ y : F,
        u = ContactEnv vbar κ (toLp 2 (y, (ofLp ξ).2 + σ))
          - ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)}).Nonempty := ⟨_, ⟨(ofLp ξ).1, rfl⟩⟩
    have hbdd : BddAbove {u : ℝ | ∃ y : F,
        u = ContactEnv vbar κ (toLp 2 (y, (ofLp ξ).2 + σ))
          - ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)} :=
      ⟨QuadEnvP (ContactEnv v κ) l (Θ ξ) / r + (-(A ξ) - a₀ * σ), by
        rintro u ⟨y, rfl⟩; exact hbar y⟩
    rw [hPdef (ContactEnv vbar κ) σ ξ hσne]
    refine le_antisymm (csSup_le hne (by rintro u ⟨y, rfl⟩; exact hbar y)) ?_
    have hb : QuadEnvP (ContactEnv v κ) l (Θ ξ)
        ≤ r * (sSup {u : ℝ | ∃ y : F,
            u = ContactEnv vbar κ (toLp 2 (y, (ofLp ξ).2 + σ))
              - ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)} - (-(A ξ) - a₀ * σ)) := by
      refine hleast _ fun X => ?_
      obtain ⟨y', rfl⟩ := hsurj ((ofLp ξ).2 + σ - 1) X
      have hmem := le_csSup hbdd (⟨y', rfl⟩ : _ ∈ {u : ℝ | ∃ y : F,
        u = ContactEnv vbar κ (toLp 2 (y, (ofLp ξ).2 + σ))
          - ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)})
      rw [hcorrP ξ σ l hξ hσ hl y'] at hmem
      have h3 := mul_le_mul_of_nonneg_left (by linarith [hmem] :
        (ContactEnv v κ (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀),
              (ofLp (Θ ξ)).2 + l))
            - ‖x₀ + r • (y' + ((ofLp ξ).2 + σ - 1) • p₀) - (ofLp (Θ ξ)).1‖ ^ 2 / (2 * l)) / r
          ≤ sSup {u : ℝ | ∃ y : F,
            u = ContactEnv vbar κ (toLp 2 (y, (ofLp ξ).2 + σ))
              - ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)} - (-(A ξ) - a₀ * σ)) hr.le
      rw [hrcanL] at h3
      exact h3
    have hd2 := div_le_div_of_nonneg_right hb hr.le
    rw [hrcanR] at hd2
    linarith [hd2]
  have hlawM : ∀ (ξ : WithLp 2 (F × ℝ)) (σ l : ℝ), 0 < σ → l = r * σ →
      QuadEnvM vbar σ ξ = QuadEnvM v l (Θ ξ) / r + (-(A ξ) + a₀ * σ) := by
    intro ξ σ l hσ hl
    have hσne : σ ≠ 0 := ne_of_gt hσ
    have hlpos : 0 < l := by rw [hl]; positivity
    have hlne : l ≠ 0 := ne_of_gt hlpos
    obtain ⟨hdom, hgreat⟩ := hdomvM l (Θ ξ) hlpos (Set.mem_univ _) (Set.mem_univ _)
    have hbar : ∀ y' : F,
        QuadEnvM v l (Θ ξ) / r + (-(A ξ) + a₀ * σ)
          ≤ vbar (toLp 2 (y', (ofLp ξ).2 - σ)) + ‖y' - (ofLp ξ).1‖ ^ 2 / (2 * σ) := by
      intro y'
      rw [hcorrM ξ σ l hσ hl y']
      have hd := div_le_div_of_nonneg_right (hdom (x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀)))
        hr.le
      linarith [hd]
    have hne : ({u : ℝ | ∃ y : F,
        u = vbar (toLp 2 (y, (ofLp ξ).2 - σ))
          + ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)}).Nonempty := ⟨_, ⟨(ofLp ξ).1, rfl⟩⟩
    have hbdd : BddBelow {u : ℝ | ∃ y : F,
        u = vbar (toLp 2 (y, (ofLp ξ).2 - σ))
          + ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)} :=
      ⟨QuadEnvM v l (Θ ξ) / r + (-(A ξ) + a₀ * σ), by
        rintro u ⟨y, rfl⟩; exact hbar y⟩
    rw [hMdef vbar σ ξ hσne]
    refine le_antisymm ?_ (le_csInf hne (by rintro u ⟨y, rfl⟩; exact hbar y))
    have hb : r * (sInf {u : ℝ | ∃ y : F,
          u = vbar (toLp 2 (y, (ofLp ξ).2 - σ))
            + ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)} - (-(A ξ) + a₀ * σ))
        ≤ QuadEnvM v l (Θ ξ) := by
      refine hgreat _ fun X => ?_
      obtain ⟨y', rfl⟩ := hsurj ((ofLp ξ).2 - σ - 1) X
      have hmem := csInf_le hbdd (⟨y', rfl⟩ : _ ∈ {u : ℝ | ∃ y : F,
        u = vbar (toLp 2 (y, (ofLp ξ).2 - σ))
          + ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)})
      rw [hcorrM ξ σ l hσ hl y'] at hmem
      have h3 := mul_le_mul_of_nonneg_left (by linarith [hmem] :
        sInf {u : ℝ | ∃ y : F,
            u = vbar (toLp 2 (y, (ofLp ξ).2 - σ))
              + ‖y - (ofLp ξ).1‖ ^ 2 / (2 * σ)} - (-(A ξ) + a₀ * σ)
          ≤ (v (toLp 2 (x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀), (ofLp (Θ ξ)).2 - l))
              + ‖x₀ + r • (y' + ((ofLp ξ).2 - σ - 1) • p₀)
                - (ofLp (Θ ξ)).1‖ ^ 2 / (2 * l)) / r) hr.le
      rw [hrcanL] at h3
      exact h3
    have hd2 := div_le_div_of_nonneg_right hb hr.le
    rw [hrcanR] at hd2
    linarith [hd2]
  -- ===== Step 1: the corresponding states =====
  have hζ1 : (ofLp ζ).1 = r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀) := by rw [hζ]
  have hζ2 : (ofLp ζ).2 = (ofLp z).2 / r := by rw [hζ]
  have hζp1 : (ofLp ζp).1 = r⁻¹ • ((ofLp zp).1 - x₀ - ((ofLp zp).2 - r) • p₀) := by rw [hζp]
  have hζp2 : (ofLp ζp).2 = (ofLp zp).2 / r := by rw [hζp]
  have hζm1 : (ofLp ζm).1 = r⁻¹ • ((ofLp zm).1 - x₀ - ((ofLp zm).2 - r) • p₀) := by rw [hζm]
  have hζm2 : (ofLp ζm).2 = (ofLp zm).2 / r := by rw [hζm]
  have hs0 : (0 : ℝ) < (ofLp ζ).2 := by rw [hζ2]; positivity
  have hsz : r * (ofLp ζ).2 = (ofLp z).2 := by rw [hζ2]; exact hrcanL _
  have hΘζ : Θ ζ = z := by
    rw [hΘval, hζ1, hζ2]
    show (toLp 2 (x₀ + r • (r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
        + ((ofLp z).2 / r - 1) • p₀), r * ((ofLp z).2 / r)) : WithLp 2 (F × ℝ)) = z
    rw [smul_add, smul_smul, mul_inv_cancel₀ hrne, one_smul, smul_smul,
      show r * ((ofLp z).2 / r - 1) = (ofLp z).2 - r from by field_simp,
      show x₀ + (((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀) + ((ofLp z).2 - r) • p₀)
        = (ofLp z).1 from by abel, hrcanL]
  -- the step pair data
  obtain ⟨Yp, Ym, hYp, hYm, hzpd, hzmd⟩ := hstep
  have hzp1 : (ofLp zp).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 + Yp) := by rw [hzpd]
  have hzp2 : (ofLp zp).2 = (ofLp z).2 + ε := by rw [hzpd]
  have hzm1 : (ofLp zm).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 + Ym) := by rw [hzmd]
  have hzm2 : (ofLp zm).2 = (ofLp z).2 - ε := by rw [hzmd]
  -- the framed optimizers
  obtain ⟨Yp', hYp'⟩ : ∃ u : F,
      u = r⁻¹ • (Yp - x₀ - ((ofLp z).2 + 2 * ε - r) • p₀) := ⟨_, rfl⟩
  obtain ⟨Ym', hYm'⟩ : ∃ u : F,
      u = r⁻¹ • (Ym - x₀ - ((ofLp z).2 - 2 * ε - r) • p₀) := ⟨_, rfl⟩
  have hl2 : (2 : ℝ) * ε = r * (2 * (ε / r)) := by field_simp
  have h2σ : (0 : ℝ) < 2 * (ε / r) := by positivity
  have hXp : x₀ + r • (Yp' + ((ofLp ζ).2 + 2 * (ε / r) - 1) • p₀) = Yp := by
    rw [hYp', hζ2, smul_add, smul_smul, mul_inv_cancel₀ hrne, one_smul, smul_smul,
      show r * ((ofLp z).2 / r + 2 * (ε / r) - 1) = (ofLp z).2 + 2 * ε - r from by field_simp]
    abel
  have hXm : x₀ + r • (Ym' + ((ofLp ζ).2 - 2 * (ε / r) - 1) • p₀) = Ym := by
    rw [hYm', hζ2, smul_add, smul_smul, mul_inv_cancel₀ hrne, one_smul, smul_smul,
      show r * ((ofLp z).2 / r - 2 * (ε / r) - 1) = (ofLp z).2 - 2 * ε - r from by field_simp]
    abel
  -- ===== Step 4: the images are an optimizing step pair of size `ε / r` =====
  have hstepP : QuadEnvP (ContactEnv vbar κ) (2 * (ε / r)) ζ
      = ContactEnv vbar κ (toLp 2 (Yp', (ofLp ζ).2 + 2 * (ε / r)))
        - ‖Yp' - (ofLp ζ).1‖ ^ 2 / (2 * (2 * (ε / r))) := by
    have h1 := hlawP ζ (2 * (ε / r)) (2 * ε) hs0 h2σ hl2
    have h2 := hcorrP ζ (2 * (ε / r)) (2 * ε) hs0 h2σ hl2 Yp'
    rw [hΘζ] at h1 h2
    rw [hXp] at h2
    rw [h1, hYp]
    linarith [h2]
  have hstepM : QuadEnvM vbar (2 * (ε / r)) ζ
      = vbar (toLp 2 (Ym', (ofLp ζ).2 - 2 * (ε / r)))
        + ‖Ym' - (ofLp ζ).1‖ ^ 2 / (2 * (2 * (ε / r))) := by
    have h1 := hlawM ζ (2 * (ε / r)) (2 * ε) h2σ hl2
    have h2 := hcorrM ζ (2 * (ε / r)) (2 * ε) h2σ hl2 Ym'
    rw [hΘζ] at h1 h2
    rw [hXm] at h2
    rw [h1, hYm]
    linarith [h2]
  have hmidp : ζp = toLp 2 ((2 : ℝ)⁻¹ • ((ofLp ζ).1 + Yp'), (ofLp ζ).2 + ε / r) := by
    rw [hζp, hzp1, hzp2, hζ1, hζ2, hYp']
    show (toLp 2 (r⁻¹ • ((2 : ℝ)⁻¹ • ((ofLp z).1 + Yp) - x₀ - ((ofLp z).2 + ε - r) • p₀),
        ((ofLp z).2 + ε) / r) : WithLp 2 (F × ℝ))
      = toLp 2 ((2 : ℝ)⁻¹ • (r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
          + r⁻¹ • (Yp - x₀ - ((ofLp z).2 + 2 * ε - r) • p₀)), (ofLp z).2 / r + ε / r)
    rw [show ((ofLp z).2 + ε) / r = (ofLp z).2 / r + ε / r from by ring,
      show r⁻¹ • ((2 : ℝ)⁻¹ • ((ofLp z).1 + Yp) - x₀ - ((ofLp z).2 + ε - r) • p₀)
        = (2 : ℝ)⁻¹ • (r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
          + r⁻¹ • (Yp - x₀ - ((ofLp z).2 + 2 * ε - r) • p₀)) from by module]
  have hmidm : ζm = toLp 2 ((2 : ℝ)⁻¹ • ((ofLp ζ).1 + Ym'), (ofLp ζ).2 - ε / r) := by
    rw [hζm, hzm1, hzm2, hζ1, hζ2, hYm']
    show (toLp 2 (r⁻¹ • ((2 : ℝ)⁻¹ • ((ofLp z).1 + Ym) - x₀ - ((ofLp z).2 - ε - r) • p₀),
        ((ofLp z).2 - ε) / r) : WithLp 2 (F × ℝ))
      = toLp 2 ((2 : ℝ)⁻¹ • (r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
          + r⁻¹ • (Ym - x₀ - ((ofLp z).2 - 2 * ε - r) • p₀)), (ofLp z).2 / r - ε / r)
    rw [show ((ofLp z).2 - ε) / r = (ofLp z).2 / r - ε / r from by ring,
      show r⁻¹ • ((2 : ℝ)⁻¹ • ((ofLp z).1 + Ym) - x₀ - ((ofLp z).2 - ε - r) • p₀)
        = (2 : ℝ)⁻¹ • (r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
          + r⁻¹ • (Ym - x₀ - ((ofLp z).2 - 2 * ε - r) • p₀)) from by module]
  have hc1 : IsStepPair vbar κ (ε / r) ζ ζp ζm :=
    ⟨Yp', Ym', hstepP, hstepM, hmidp, hmidm⟩
  -- ===== Step 5: the two step velocities =====
  have hscal : (ε / r)⁻¹ * r⁻¹ = ε⁻¹ := by field_simp
  have hvp : (ε / r)⁻¹ • ((ofLp ζp).1 - (ofLp ζ).1)
      = ε⁻¹ • ((ofLp zp).1 - (ofLp z).1) - p₀ := by
    rw [hζp1, hζ1, hzp2,
      show r⁻¹ • ((ofLp zp).1 - x₀ - ((ofLp z).2 + ε - r) • p₀)
          - r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
        = r⁻¹ • ((ofLp zp).1 - (ofLp z).1 - ε • p₀) from by module,
      smul_smul, hscal, smul_sub, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  have hvm : (ε / r)⁻¹ • ((ofLp ζ).1 - (ofLp ζm).1)
      = ε⁻¹ • ((ofLp z).1 - (ofLp zm).1) - p₀ := by
    rw [hζm1, hζ1, hzm2,
      show r⁻¹ • ((ofLp z).1 - x₀ - ((ofLp z).2 - r) • p₀)
          - r⁻¹ • ((ofLp zm).1 - x₀ - ((ofLp z).2 - ε - r) • p₀)
        = r⁻¹ • ((ofLp z).1 - (ofLp zm).1 - ε • p₀) from by module,
      smul_smul, hscal, smul_sub, smul_smul, inv_mul_cancel₀ hεne, one_smul]
  -- ===== Step 5: the reference velocity =====
  have hc4 : HasGradientAt
      (fun y' : F => QuadEnvP (ContactEnv vbar κ) (ε / r) (toLp 2 (y', (ofLp ζ).2)))
      (Q₀ - p₀) (ofLp ζ).1 := by
    obtain ⟨cf, hcf⟩ : ∃ u : F, u = x₀ + (r * ((ofLp ζ).2 - 1)) • p₀ := ⟨_, rfl⟩
    obtain ⟨Cst, hCst⟩ : ∃ d : ℝ, d = -(v (toLp 2 (x₀, r)) / r)
        - (a₀ + ‖p₀‖ ^ 2 / 2) * ((ofLp ζ).2 - 1) - a₀ * (ε / r) := ⟨_, rfl⟩
    have hεrl : ε = r * (ε / r) := by field_simp
    have hfun : (fun y' : F => QuadEnvP (ContactEnv vbar κ) (ε / r) (toLp 2 (y', (ofLp ζ).2)))
        = fun y' : F => r⁻¹ * QuadEnvP (ContactEnv v κ) ε
            (toLp 2 (cf + r • y', (ofLp z).2)) - inner ℝ p₀ y' + Cst := by
      funext y'
      have h1 := hlawP (toLp 2 (y', (ofLp ζ).2)) (ε / r) ε
        (show (0 : ℝ) < (ofLp ζ).2 from hs0) hεr hεrl
      have hpt : Θ (toLp 2 (y', (ofLp ζ).2)) = toLp 2 (cf + r • y', (ofLp z).2) := by
        rw [hΘval]
        show (toLp 2 (x₀ + r • (y' + ((ofLp ζ).2 - 1) • p₀), r * (ofLp ζ).2)
            : WithLp 2 (F × ℝ)) = toLp 2 (cf + r • y', (ofLp z).2)
        rw [hcf, show x₀ + r • (y' + ((ofLp ζ).2 - 1) • p₀)
              = x₀ + (r * ((ofLp ζ).2 - 1)) • p₀ + r • y' from by module, hsz]
      rw [h1, hpt, hAlp, hCst]
      ring
    have hcrz : cf + r • (ofLp ζ).1 = (ofLp z).1 := by
      have h0 : (ofLp (Θ ζ)).1 = (ofLp z).1 := by rw [hΘζ]
      rw [hΘfst] at h0
      rw [hcf, show x₀ + (r * ((ofLp ζ).2 - 1)) • p₀ + r • (ofLp ζ).1
            = x₀ + r • ((ofLp ζ).1 + ((ofLp ζ).2 - 1) • p₀) from by module]
      exact h0
    have hG' : HasFDerivAt
        (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp z).2)))
        ((InnerProductSpace.toDual ℝ F) Q₀) (cf + r • (ofLp ζ).1) := by
      rw [hcrz]; exact hQ₀
    have hLin : HasFDerivAt (fun y' : F => cf + r • y')
        (r • ContinuousLinearMap.id ℝ F) ((ofLp ζ).1) := by
      have h0 : HasFDerivAt (fun y' : F => r • y') (r • ContinuousLinearMap.id ℝ F)
          ((ofLp ζ).1) := (r • ContinuousLinearMap.id ℝ F).hasFDerivAt
      exact h0.const_add cf
    have hcomp0 : HasFDerivAt
        ((fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp z).2)))
          ∘ (fun y' : F => cf + r • y'))
        (((InnerProductSpace.toDual ℝ F) Q₀).comp (r • ContinuousLinearMap.id ℝ F))
        ((ofLp ζ).1) := HasFDerivAt.comp ((ofLp ζ).1) hG' hLin
    have hcompf : HasFDerivAt
        (fun y' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (cf + r • y', (ofLp z).2)))
        (((InnerProductSpace.toDual ℝ F) Q₀).comp (r • ContinuousLinearMap.id ℝ F))
        ((ofLp ζ).1) := hcomp0
    have hinn : HasFDerivAt (fun y' : F => (inner ℝ p₀ y' : ℝ))
        ((InnerProductSpace.toDual ℝ F) p₀) ((ofLp ζ).1) :=
      ((InnerProductSpace.toDual ℝ F) p₀).hasFDerivAt
    have hall : HasFDerivAt
        (fun y' : F => r⁻¹ * QuadEnvP (ContactEnv v κ) ε
            (toLp 2 (cf + r • y', (ofLp z).2)) - inner ℝ p₀ y' + Cst)
        (r⁻¹ • (((InnerProductSpace.toDual ℝ F) Q₀).comp
            (r • ContinuousLinearMap.id ℝ F)) - (InnerProductSpace.toDual ℝ F) p₀)
        ((ofLp ζ).1) := ((hcompf.const_mul r⁻¹).sub hinn).add_const Cst
    have hCLM : (r⁻¹ • (((InnerProductSpace.toDual ℝ F) Q₀).comp
          (r • ContinuousLinearMap.id ℝ F)) - (InnerProductSpace.toDual ℝ F) p₀)
        = (InnerProductSpace.toDual ℝ F) (Q₀ - p₀) := by
      refine ContinuousLinearMap.ext fun w => ?_
      show r⁻¹ * (inner ℝ Q₀ (r • w) : ℝ) - inner ℝ p₀ w = inner ℝ (Q₀ - p₀) w
      rw [real_inner_smul_right, inner_sub_left]
      field_simp
    rw [hCLM] at hall
    rw [hfun]
    exact hall
  -- ===== Step 6: the discrepancies =====
  refine ⟨hc1, hvp, hvm, hc4, ?_, ?_⟩
  · rw [hvp]; abel
  · rw [hvm]; abel
