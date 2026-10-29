import InfHarmonic.IsStepPair
import InfHarmonic.JGap
import InfHarmonic.DPSpatialRegularity
import InfHarmonic.QuadEnvComposition
import InfHarmonic.QuadEnvAttained
import InfHarmonic.EnvelopeCompetitorBounds
import InfHarmonic.ContactEnvPositiveTimeRegularity
import InfHarmonic.UniformSubquadratic
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (6.5): for an optimizing step pair the half-step envelope
identities hold, and the forward velocity is the gradient of the full forward
envelope. -/
theorem DPStepIdentities (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (ε : ℝ) (hε : 0 < ε) (z zp zm : WithLp 2 (F × ℝ)) (hz : ε < (ofLp z).2)
    (hstep : IsStepPair v κ ε z zp zm) :
    QuadEnvP (ContactEnv v κ) (2 * ε) z
        = QuadEnvP (ContactEnv v κ) ε zp
          - (ε / 2) * ‖ε⁻¹ • ((ofLp zp).1 - (ofLp z).1)‖ ^ 2 ∧
    QuadEnvM v (2 * ε) z
        = QuadEnvM v ε zm
          + (ε / 2) * ‖ε⁻¹ • ((ofLp z).1 - (ofLp zm).1)‖ ^ 2 ∧
    HasGradientAt
      (fun x' : F => QuadEnvP (ContactEnv v κ) (2 * ε) (toLp 2 (x', (ofLp z).2)))
      (ε⁻¹ • ((ofLp zp).1 - (ofLp z).1)) (ofLp z).1 := by
  classical
  have hε2 : (0 : ℝ) < 2 * ε := by linarith
  have hεne : ε ≠ 0 := ne_of_gt hε
  have ht0 : (0 : ℝ) < (ofLp z).2 := by linarith
  -- ===== Step 0: admissibility.  `W = ContactEnv v κ` on `(0, ∞)` is the single obtain
  -- from ContactEnvPositiveTimeRegularity; `v` on `ℝ` is the standard preamble. =====
  obtain ⟨hWcont, hWgrow, -⟩ :=
    ContactEnvPositiveTimeRegularity C₀ κ hC₀ hκ v hv hcent hJ
  have hIuniv : ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ))
      = (Set.univ : Set (WithLp 2 (F × ℝ))) := Set.preimage_univ
  have hvcont : ContinuousOn v
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ)) := by
    rw [hIuniv]; exact hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc η hη
    obtain ⟨M, hM0, hMb⟩ :=
      UniformSubquadratic (F := F) C₀ hC₀ (toLp 2 ((0 : F), (1 : ℝ))) (Or.inr rfl) J hJc η hη
    exact ⟨M, hM0, fun ζ hζ hζJ => hMb v hv hcent ζ hζ hζJ⟩
  -- attainment for both envelopes, and the domination licences.  Attainment does NOT
  -- give the domination: the envelope is an `sSup`/`sInf` carrying the preamble's junk
  -- value, so each competitor comparison is taken from EnvelopeCompetitorBounds.
  obtain ⟨hattW, -, -, -, -, -⟩ :=
    QuadEnvAttained (Set.Ioi (0 : ℝ)) isOpen_Ioi (ContactEnv v κ) hWcont hWgrow
  obtain ⟨hdomW, -, -⟩ :=
    EnvelopeCompetitorBounds (Set.Ioi (0 : ℝ)) (ContactEnv v κ) hWcont hWgrow
  obtain ⟨-, hattMv, -, -, -, -⟩ :=
    QuadEnvAttained (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow
  obtain ⟨-, hdomMv, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont hvgrow
  -- ===== the splitting inequality: the `ℓ = h = ε` case of cost additivity =====
  -- `2|a|² + 2|b|² - |a+b|² = |a-b|² ≥ 0`, with slack exactly `|a-b|²/(4ε)`.
  have hsplit : ∀ a b : F,
      ‖a + b‖ ^ 2 / (4 * ε) ≤ ‖a‖ ^ 2 / (2 * ε) + ‖b‖ ^ 2 / (2 * ε) := by
    intro a b
    have hkey : ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
      have h1 := norm_add_sq_real a b
      have h3 := norm_sub_sq_real a b
      have h2 : (0 : ℝ) ≤ ‖a - b‖ ^ 2 := by positivity
      linarith
    have h4 : ‖a‖ ^ 2 / (2 * ε) + ‖b‖ ^ 2 / (2 * ε)
        = (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) / (4 * ε) := by field_simp; ring
    rw [h4]
    exact div_le_div_of_nonneg_right hkey (by linarith)
  -- ===== Step 1: the optimizers, the midpoints, and the even cost split =====
  obtain ⟨Yp, Ym, hYp, hYm, hzpd, hzmd⟩ := hstep
  have hzp1 : (ofLp zp).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 + Yp) := by rw [hzpd]
  have hzp2 : (ofLp zp).2 = (ofLp z).2 + ε := by rw [hzpd]
  have hzm1 : (ofLp zm).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 + Ym) := by rw [hzmd]
  have hzm2 : (ofLp zm).2 = (ofLp z).2 - ε := by rw [hzmd]
  -- each half of a straight path carries the same displacement
  have hdp : (ofLp zp).1 - (ofLp z).1 = (2 : ℝ)⁻¹ • (Yp - (ofLp z).1) := by
    rw [hzp1]; module
  have hdp' : Yp - (ofLp zp).1 = (2 : ℝ)⁻¹ • (Yp - (ofLp z).1) := by
    rw [hzp1]; module
  have hdm : (ofLp z).1 - (ofLp zm).1 = (2 : ℝ)⁻¹ • ((ofLp z).1 - Ym) := by
    rw [hzm1]; module
  have hdm' : Ym - (ofLp zm).1 = (2 : ℝ)⁻¹ • (Ym - (ofLp z).1) := by
    rw [hzm1]; module
  have hdm'' : (ofLp zm).1 - (ofLp z).1 = (2 : ℝ)⁻¹ • (Ym - (ofLp z).1) := by
    rw [hzm1]; module
  -- the half-displacement norm, and the two cost identities it yields
  have hhalfnorm : ∀ u : F, ‖(2 : ℝ)⁻¹ • u‖ = ‖u‖ / 2 := by
    intro u
    rw [norm_smul, Real.norm_eq_abs]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
    ring
  have hvelp : ‖ε⁻¹ • ((ofLp zp).1 - (ofLp z).1)‖ = ‖Yp - (ofLp z).1‖ / (2 * ε) := by
    rw [hdp, norm_smul, hhalfnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hε)]
    field_simp
  have hvelm : ‖ε⁻¹ • ((ofLp z).1 - (ofLp zm).1)‖ = ‖Ym - (ofLp z).1‖ / (2 * ε) := by
    rw [hdm, norm_smul, hhalfnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε),
      norm_sub_rev]
    field_simp
  have hcostp : (ε / 2) * ‖ε⁻¹ • ((ofLp zp).1 - (ofLp z).1)‖ ^ 2
      = ‖Yp - (ofLp z).1‖ ^ 2 / (8 * ε) := by
    rw [hvelp]; field_simp; ring
  have hcostm : (ε / 2) * ‖ε⁻¹ • ((ofLp z).1 - (ofLp zm).1)‖ ^ 2
      = ‖Ym - (ofLp z).1‖ ^ 2 / (8 * ε) := by
    rw [hvelm]; field_simp; ring
  have hhp : ‖Yp - (ofLp zp).1‖ ^ 2 / (2 * ε) = ‖Yp - (ofLp z).1‖ ^ 2 / (8 * ε) := by
    rw [hdp', hhalfnorm]; field_simp; ring
  have hhp' : ‖(ofLp zp).1 - (ofLp z).1‖ ^ 2 / (2 * ε)
      = ‖Yp - (ofLp z).1‖ ^ 2 / (8 * ε) := by
    rw [hdp, hhalfnorm]; field_simp; ring
  have hhm : ‖Ym - (ofLp zm).1‖ ^ 2 / (2 * ε) = ‖Ym - (ofLp z).1‖ ^ 2 / (8 * ε) := by
    rw [hdm', hhalfnorm]; field_simp; ring
  have hhm' : ‖(ofLp zm).1 - (ofLp z).1‖ ^ 2 / (2 * ε)
      = ‖Ym - (ofLp z).1‖ ^ 2 / (8 * ε) := by
    rw [hdm'', hhalfnorm]; field_simp; ring
  -- the time arguments
  have htp : (ofLp zp).2 + ε = (ofLp z).2 + 2 * ε := by rw [hzp2]; ring
  have htm : (ofLp zm).2 - ε = (ofLp z).2 - 2 * ε := by rw [hzm2]; ring
  have hzpI : (ofLp zp).2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by rw [hzp2]; linarith)
  have hzpI' : (ofLp zp).2 + ε ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by rw [htp]; linarith)
  have hzI : (ofLp z).2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr ht0
  have hzI' : (ofLp z).2 + 2 * ε ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by linarith)
  refine ⟨?_, ?_, ?_⟩
  -- ===================== Step 2: the forward identity ==============================
  · obtain ⟨y₁, hy₁⟩ : ∃ y : F, QuadEnvP (ContactEnv v κ) ε zp
        = ContactEnv v κ (toLp 2 (y, (ofLp zp).2 + ε)) - ‖y - (ofLp zp).1‖ ^ 2 / (2 * ε) :=
      hattW ε zp hε hzpI hzpI'
    -- the competitor `Y⁺` at the half step, dominated by the half-step envelope
    have hge := (hdomW ε zp hε hzpI hzpI').1 Yp
    -- the competitor `y₁` at the full step, dominated by the full-step envelope
    have hle := (hdomW (2 * ε) z hε2 hzI hzI').1 y₁
    -- the splitting inequality at `a = y₁ - x⁺`, `b = x⁺ - x`
    have hsum : (y₁ - (ofLp zp).1) + ((ofLp zp).1 - (ofLp z).1) = y₁ - (ofLp z).1 := by
      abel
    have hsp := hsplit (y₁ - (ofLp zp).1) ((ofLp zp).1 - (ofLp z).1)
    rw [hsum] at hsp
    have h4e : (2 : ℝ) * (2 * ε) = 4 * ε := by ring
    rw [htp] at hy₁ hge
    rw [h4e] at hle
    rw [h4e] at hYp
    rw [hhp] at hge
    rw [hhp'] at hsp
    -- every cost over the common denominator `8ε`, so that `linarith` sees one monomial
    have hc1 : ‖Yp - (ofLp z).1‖ ^ 2 / (4 * ε)
        = 2 * (‖Yp - (ofLp z).1‖ ^ 2 / (8 * ε)) := by field_simp; ring
    have hc2 : ‖y₁ - (ofLp z).1‖ ^ 2 / (4 * ε)
        = 2 * (‖y₁ - (ofLp z).1‖ ^ 2 / (8 * ε)) := by field_simp; ring
    have hc3 : ‖y₁ - (ofLp zp).1‖ ^ 2 / (2 * ε)
        = 4 * (‖y₁ - (ofLp zp).1‖ ^ 2 / (8 * ε)) := by field_simp; ring
    rw [hcostp]
    linarith
  -- ===================== Step 3: the backward identity =============================
  · obtain ⟨w₀, hw₀⟩ : ∃ y : F, QuadEnvM v ε zm
        = v (toLp 2 (y, (ofLp zm).2 - ε)) + ‖y - (ofLp zm).1‖ ^ 2 / (2 * ε) :=
      hattMv ε zm hε (Set.mem_univ _) (Set.mem_univ _)
    have hle := (hdomMv ε zm hε (Set.mem_univ _) (Set.mem_univ _)).1 Ym
    have hge := (hdomMv (2 * ε) z hε2 (Set.mem_univ _) (Set.mem_univ _)).1 w₀
    have hsum : (w₀ - (ofLp zm).1) + ((ofLp zm).1 - (ofLp z).1) = w₀ - (ofLp z).1 := by
      abel
    have hsp := hsplit (w₀ - (ofLp zm).1) ((ofLp zm).1 - (ofLp z).1)
    rw [hsum] at hsp
    have h4e : (2 : ℝ) * (2 * ε) = 4 * ε := by ring
    rw [htm] at hw₀ hle
    rw [h4e] at hge
    rw [h4e] at hYm
    rw [hhm] at hle
    rw [hhm'] at hsp
    have hc1 : ‖Ym - (ofLp z).1‖ ^ 2 / (4 * ε)
        = 2 * (‖Ym - (ofLp z).1‖ ^ 2 / (8 * ε)) := by field_simp; ring
    have hc2 : ‖w₀ - (ofLp z).1‖ ^ 2 / (4 * ε)
        = 2 * (‖w₀ - (ofLp z).1‖ ^ 2 / (8 * ε)) := by field_simp; ring
    have hc3 : ‖w₀ - (ofLp zm).1‖ ^ 2 / (2 * ε)
        = 4 * (‖w₀ - (ofLp zm).1‖ ^ 2 / (8 * ε)) := by field_simp; ring
    rw [hcostm]
    linarith
  -- ===================== Step 4: the forward velocity is the gradient ==============
  · obtain ⟨y, hyatt, hyuniq, hygrad, -⟩ :=
      DPSpatialRegularity C₀ κ hC₀ hκ v hv hcent hJ (ofLp z).2 (2 * ε) ht0 hε2 (ofLp z).1
    have hzeq : (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := rfl
    have hYpy : Yp = y := by
      refine hyuniq Yp ?_
      rw [hzeq]
      exact hYp
    have hgrad : ε⁻¹ • ((ofLp zp).1 - (ofLp z).1) = (2 * ε)⁻¹ • (y - (ofLp z).1) := by
      rw [hdp, smul_smul, hYpy, show ε⁻¹ * (2 : ℝ)⁻¹ = (2 * ε)⁻¹ from by field_simp]
    rw [hgrad]
    exact hygrad
