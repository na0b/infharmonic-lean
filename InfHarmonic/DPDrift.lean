import InfHarmonic.DPStepIdentities
import InfHarmonic.DPSpatialRegularity
import InfHarmonic.QuadEnvPathConvex
import InfHarmonic.JGap
import InfHarmonic.BarycentricSubsolution
import InfHarmonic.BaryEnvSandwich
import InfHarmonic.BaryEnvDuality
import InfHarmonic.UniformSubquadratic
import InfHarmonic.EnvelopeCompetitorBounds
import InfHarmonic.ContactEnvPositiveTimeRegularity
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 6.3, the one-step drift: at an optimizing step pair the four gaps
`D`, `e`, `D̃`, `ẽ` are nonnegative, the mean change of `J_ε` equals their sum
divided by `4ε`, and it dominates `c (‖Q₊ - Q₀‖² + ‖Q₋ - Q₀‖²)` with
`c = 1 / (16 (1 + log 2))`. -/
theorem DPDrift (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ)
    (ε : ℝ) (hε : 0 < ε) (z zp zm : WithLp 2 (F × ℝ)) (hz : ε < (ofLp z).2)
    (hstep : IsStepPair v κ ε z zp zm)
    (Q₀ : F)
    (hQ₀ : HasGradientAt
      (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', (ofLp z).2)))
      Q₀ (ofLp z).1)
    (D e D' e' : ℝ)
    (hD : D = ContactEnv v κ z + QuadEnvP (ContactEnv v κ) (2 * ε) z
            - 2 * QuadEnvP (ContactEnv v κ) ε z)
    (he : e = QuadEnvP (ContactEnv v κ) ε zm
            + (ε / 2) * ‖ε⁻¹ • ((ofLp z).1 - (ofLp zm).1)‖ ^ 2 - ContactEnv v κ z)
    (hD' : D' = 2 * QuadEnvM v ε z - v z - QuadEnvM v (2 * ε) z)
    (he' : e' = v z + (ε / 2) * ‖ε⁻¹ • ((ofLp zp).1 - (ofLp z).1)‖ ^ 2
            - QuadEnvM v ε zp) :
    0 ≤ D ∧ 0 ≤ e ∧ 0 ≤ D' ∧ 0 ≤ e' ∧
    (JGap v κ ε zp + JGap v κ ε zm) / 2 - JGap v κ ε z
        = (D + e + D' + e') / (4 * ε) ∧
    (D + e) / (4 * ε)
        ≤ (JGap v κ ε zp + JGap v κ ε zm) / 2 - JGap v κ ε z ∧
    (1 / (16 * (1 + Real.log 2))) *
        (‖ε⁻¹ • ((ofLp zp).1 - (ofLp z).1) - Q₀‖ ^ 2
          + ‖ε⁻¹ • ((ofLp z).1 - (ofLp zm).1) - Q₀‖ ^ 2)
      ≤ (D + e) / (4 * ε) := by
  classical
  -- ===== Step 0: the standing numerical facts =====
  have hε2 : (0 : ℝ) < 2 * ε := by linarith
  have hεne : ε ≠ 0 := ne_of_gt hε
  have ht0 : (0 : ℝ) < (ofLp z).2 := by linarith
  have htne : (ofLp z).2 ≠ 0 := ne_of_gt ht0
  have hLpos : (0 : ℝ) < 1 + Real.log 2 := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2); linarith
  have hLne : (1 : ℝ) + Real.log 2 ≠ 0 := ne_of_gt hLpos
  have hzz : (toLp 2 ((ofLp z).1, (ofLp z).2) : WithLp 2 (F × ℝ)) = z := rfl
  -- the two step velocities, named once
  obtain ⟨Qp, hQpd⟩ : ∃ u : F, u = ε⁻¹ • ((ofLp zp).1 - (ofLp z).1) := ⟨_, rfl⟩
  obtain ⟨Qm, hQmd⟩ : ∃ u : F, u = ε⁻¹ • ((ofLp z).1 - (ofLp zm).1) := ⟨_, rfl⟩
  have he2 : e = QuadEnvP (ContactEnv v κ) ε zm + (ε / 2) * ‖Qm‖ ^ 2
      - ContactEnv v κ z := by rw [hQmd]; exact he
  have he'2 : e' = v z + (ε / 2) * ‖Qp‖ ^ 2 - QuadEnvM v ε zp := by
    rw [hQpd]; exact he'
  -- ===== Step 0: admissibility of `W = ContactEnv v κ` on `(0,∞)` and of `v` on `ℝ` =====
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
  have hvgrowIoi : SubquadraticGrowth (Set.Ioi (0 : ℝ)) v :=
    fun J _ hJc η hη => hvgrow J (Set.subset_univ J) hJc η hη
  have hvsuper : IsLimitSuperOn
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' (Set.univ : Set ℝ)) v := by
    rw [hIuniv]; exact hv.1.2
  -- `v` is a subsolution on the open set of positive times: restrict the entire one.
  have hOpos : IsOpen {ζ : WithLp 2 (F × ℝ) | 0 < (ofLp ζ).2} :=
    isOpen_Ioi.preimage (continuous_snd.comp (WithLp.prod_continuous_ofLp 2 F ℝ))
  have hvsubIoi : IsLimitSubOn {ζ : WithLp 2 (F × ℝ) | 0 < (ofLp ζ).2} v := by
    refine ⟨hOpos, hv.1.1.2.1.mono (Set.subset_univ _), ?_⟩
    intro ζ hζ φ hφ hmax
    rw [IsLocalMaxOn, IsMaxFilter, hOpos.nhdsWithin_eq hζ] at hmax
    refine hv.1.1.2.2 ζ (Set.mem_univ _) φ hφ ?_
    rw [IsLocalMaxOn, IsMaxFilter, nhdsWithin_univ]
    exact hmax
  -- and therefore so is `W`, by the barycentric subsolution node with `c = κ²/2`.
  have hWsub : IsLimitSubOn
      ((fun ζ : WithLp 2 (F × ℝ) => (ofLp ζ).2) ⁻¹' Set.Ioi (0 : ℝ)) (ContactEnv v κ) := by
    have hbs := BarycentricSubsolution v hvsubIoi hvgrowIoi (κ ^ 2 / 2)
    have hfun : (fun ζ : WithLp 2 (F × ℝ) =>
          BaryEnv v (ofLp ζ).2 ζ - κ ^ 2 / 2 * (ofLp ζ).2) = ContactEnv v κ := by
      funext ζ; simp only [ContactEnv]; ring
    rw [hfun] at hbs
    exact hbs
  -- ===== the two envelope-value conventions at length zero =====
  have hP0gen : ∀ ζ : WithLp 2 (F × ℝ), QuadEnvP (ContactEnv v κ) 0 ζ = ContactEnv v κ ζ := by
    intro ζ; simp [QuadEnvP]
  have hM0gen : ∀ ζ : WithLp 2 (F × ℝ), QuadEnvM v 0 ζ = v ζ := by
    intro ζ; simp [QuadEnvM]
  -- ===== the midpoint inequality, once for convex and once for concave =====
  have hmid3 : ∀ (g : ℝ → ℝ) (T : ℝ), 0 < T → ConvexOn ℝ (Set.Icc (0 : ℝ) T) g →
      ∀ p q r : ℝ, g 0 = p → g (T / 2) = q → g T = r → 2 * q ≤ p + r := by
    intro g T hT hg p q r hp hq hr
    have h := hg.2 (Set.mem_Icc.mpr ⟨le_rfl, hT.le⟩) (Set.mem_Icc.mpr ⟨hT.le, le_rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have harg : (1 / 2 : ℝ) • (0 : ℝ) + (1 / 2 : ℝ) • T = T / 2 := by
      simp only [smul_eq_mul]; ring
    rw [harg, hp, hq, hr] at h
    simp only [smul_eq_mul] at h
    linarith
  have hmid3C : ∀ (g : ℝ → ℝ) (T : ℝ), 0 < T → ConcaveOn ℝ (Set.Icc (0 : ℝ) T) g →
      ∀ p q r : ℝ, g 0 = p → g (T / 2) = q → g T = r → p + r ≤ 2 * q := by
    intro g T hT hg p q r hp hq hr
    have h := hg.2 (Set.mem_Icc.mpr ⟨le_rfl, hT.le⟩) (Set.mem_Icc.mpr ⟨hT.le, le_rfl⟩)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
    have harg : (1 / 2 : ℝ) • (0 : ℝ) + (1 / 2 : ℝ) • T = T / 2 := by
      simp only [smul_eq_mul]; ring
    rw [harg, hp, hq, hr] at h
    simp only [smul_eq_mul] at h
    linarith
  -- ===== the scaling identities for the two half-step costs =====
  have hscale : ∀ u : F, (ε / 2) * ‖ε⁻¹ • u‖ ^ 2 = ‖u‖ ^ 2 / (2 * ε) := by
    intro u
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε)]
    field_simp
  have hscalep : (ε / 2) * ‖Qp‖ ^ 2 = ‖(ofLp zp).1 - (ofLp z).1‖ ^ 2 / (2 * ε) := by
    rw [hQpd]; exact hscale _
  have hscalem : (ε / 2) * ‖Qm‖ ^ 2 = ‖(ofLp z).1 - (ofLp zm).1‖ ^ 2 / (2 * ε) := by
    rw [hQmd]; exact hscale _
  -- the completed square of a displaced competitor, over the common denominator `2ε`
  have hexp : ∀ u w : F, ‖u + ε • w‖ ^ 2 / (2 * ε)
      = ‖u‖ ^ 2 / (2 * ε) + inner ℝ w u + (ε / 2) * ‖w‖ ^ 2 := by
    intro u w
    have h1 : ‖u + ε • w‖ ^ 2 = ‖u‖ ^ 2 + 2 * (inner ℝ u (ε • w) : ℝ) + ‖ε • w‖ ^ 2 :=
      norm_add_sq_real u (ε • w)
    have h2 : (inner ℝ u (ε • w) : ℝ) = ε * inner ℝ w u := by
      rw [real_inner_smul_right, real_inner_comm]
    have h3 : ‖ε • w‖ ^ 2 = ε ^ 2 * ‖w‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]; ring
    rw [h1, h2, h3]
    field_simp
  -- ===== the step pair's two time coordinates =====
  obtain ⟨Yp, Ym, hYp, hYm, hzpd, hzmd⟩ := hstep
  have hzp2 : (ofLp zp).2 = (ofLp z).2 + ε := by rw [hzpd]
  have hzm2 : (ofLp zm).2 = (ofLp z).2 - ε := by rw [hzmd]
  have hzmt : (ofLp zm).2 + ε = (ofLp z).2 := by rw [hzm2]; ring
  have hzpt : (ofLp zp).2 - ε = (ofLp z).2 := by rw [hzp2]; ring
  have hzmI : (ofLp zm).2 ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by rw [hzm2]; linarith)
  have hzmI' : (ofLp zm).2 + ε ∈ Set.Ioi (0 : ℝ) := Set.mem_Ioi.mpr (by rw [hzmt]; linarith)
  -- ===== the imported facts =====
  obtain ⟨hhalfP, hhalfM, hgradP2⟩ :=
    DPStepIdentities C₀ κ hC₀ hκ v hv hcent hJ ε hε z zp zm hz
      ⟨Yp, Ym, hYp, hYm, hzpd, hzmd⟩
  have hhalfP2 : QuadEnvP (ContactEnv v κ) (2 * ε) z
      = QuadEnvP (ContactEnv v κ) ε zp - (ε / 2) * ‖Qp‖ ^ 2 := by rw [hQpd]; exact hhalfP
  have hhalfM2 : QuadEnvM v (2 * ε) z
      = QuadEnvM v ε zm + (ε / 2) * ‖Qm‖ ^ 2 := by rw [hQmd]; exact hhalfM
  obtain ⟨hdomW, -, -⟩ :=
    EnvelopeCompetitorBounds (Set.Ioi (0 : ℝ)) (ContactEnv v κ) hWcont hWgrow
  obtain ⟨-, hdomMv, -⟩ := EnvelopeCompetitorBounds (Set.univ : Set ℝ) v hvcont hvgrow
  obtain ⟨hpathP, -⟩ :=
    QuadEnvPathConvex (Set.Ioi (0 : ℝ)) isOpen_Ioi (ContactEnv v κ) hWcont hWgrow (2 * ε) hε2
  obtain ⟨-, hpathMv⟩ :=
    QuadEnvPathConvex (Set.univ : Set ℝ) isOpen_univ v hvcont hvgrow (2 * ε) hε2
  have hadm : ∀ l ∈ Set.Icc (0 : ℝ) (2 * ε), (ofLp z).2 + l ∈ Set.Ioi (0 : ℝ) := by
    intro l hl; exact Set.mem_Ioi.mpr (by linarith [hl.1])
  -- ===== Step 1: `D ≥ 0`, the convexity of the forward envelope in the length =====
  have hc1 : 0 ≤ D := by
    have hconv := hpathP hWsub ((ofLp z).1) (0 : F) ((ofLp z).2) hadm
    have hv0 : (fun l : ℝ => QuadEnvP (ContactEnv v κ) l
          (toLp 2 ((ofLp z).1 + l • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * (l * Real.log l)) 0 = ContactEnv v κ z := by
      show QuadEnvP (ContactEnv v κ) 0
          (toLp 2 ((ofLp z).1 + (0 : ℝ) • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * ((0 : ℝ) * Real.log 0) = _
      rw [smul_zero, add_zero, hzz, hP0gen, norm_zero]; ring
    have hvm : (fun l : ℝ => QuadEnvP (ContactEnv v κ) l
          (toLp 2 ((ofLp z).1 + l • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * (l * Real.log l)) (2 * ε / 2)
        = QuadEnvP (ContactEnv v κ) ε z := by
      rw [show 2 * ε / 2 = ε from by ring]
      show QuadEnvP (ContactEnv v κ) ε
          (toLp 2 ((ofLp z).1 + ε • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * (ε * Real.log ε) = _
      rw [smul_zero, add_zero, hzz, norm_zero]; ring
    have hvT : (fun l : ℝ => QuadEnvP (ContactEnv v κ) l
          (toLp 2 ((ofLp z).1 + l • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * (l * Real.log l)) (2 * ε)
        = QuadEnvP (ContactEnv v κ) (2 * ε) z := by
      show QuadEnvP (ContactEnv v κ) (2 * ε)
          (toLp 2 ((ofLp z).1 + (2 * ε) • (0 : F), (ofLp z).2))
          + ‖(0 : F)‖ ^ 2 * (2 * ε * Real.log (2 * ε)) = _
      rw [smul_zero, add_zero, hzz, norm_zero]; ring
    have hmm := hmid3 _ (2 * ε) hε2 hconv _ _ _ hv0 hvm hvT
    rw [hD]; linarith
  -- ===== Step 2: `e ≥ 0`, `z` as a forward competitor from `z⁻` =====
  have hc2 : 0 ≤ e := by
    have hcomp := (hdomW ε zm hε hzmI hzmI').1 ((ofLp z).1)
    rw [hzmt, hzz] at hcomp
    rw [he2]; linarith [hscalem]
  -- ===== Step 3: `D̃ ≥ 0`, the concavity of the backward envelope in the length =====
  have hc3 : 0 ≤ D' := by
    have hconc := hpathMv hvsuper ((ofLp z).1) ((ofLp z).2) (fun l _ => Set.mem_univ _)
    have hw0 : (fun l : ℝ => QuadEnvM v l (toLp 2 ((ofLp z).1, (ofLp z).2))) 0 = v z := by
      show QuadEnvM v 0 (toLp 2 ((ofLp z).1, (ofLp z).2)) = _
      rw [hzz, hM0gen]
    have hwm : (fun l : ℝ => QuadEnvM v l (toLp 2 ((ofLp z).1, (ofLp z).2))) (2 * ε / 2)
        = QuadEnvM v ε z := by
      rw [show 2 * ε / 2 = ε from by ring]
    have hwT : (fun l : ℝ => QuadEnvM v l (toLp 2 ((ofLp z).1, (ofLp z).2))) (2 * ε)
        = QuadEnvM v (2 * ε) z := by
      show QuadEnvM v (2 * ε) (toLp 2 ((ofLp z).1, (ofLp z).2)) = _
      rw [hzz]
    have hmm := hmid3C _ (2 * ε) hε2 hconc _ _ _ hw0 hwm hwT
    rw [hD']; linarith
  -- ===== Step 4: `ẽ ≥ 0`, `z` as a backward competitor from `z⁺` =====
  have hc4 : 0 ≤ e' := by
    have hcomp := (hdomMv ε zp hε (Set.mem_univ _) (Set.mem_univ _)).1 ((ofLp z).1)
    rw [hzpt, hzz, norm_sub_rev] at hcomp
    rw [he'2]; linarith [hscalep]
  -- ===== Step 5: the drift identity =====
  have hmain : (QuadEnvP (ContactEnv v κ) ε zp - QuadEnvM v ε zp)
      + (QuadEnvP (ContactEnv v κ) ε zm - QuadEnvM v ε zm)
      - 2 * (QuadEnvP (ContactEnv v κ) ε z - QuadEnvM v ε z) = D + e + D' + e' := by
    rw [hD, he2, hD', he'2]; linarith [hhalfP2, hhalfM2]
  have hstruct : (JGap v κ ε zp + JGap v κ ε zm) / 2 - JGap v κ ε z
      = ((QuadEnvP (ContactEnv v κ) ε zp - QuadEnvM v ε zp)
          + (QuadEnvP (ContactEnv v κ) ε zm - QuadEnvM v ε zm)
          - 2 * (QuadEnvP (ContactEnv v κ) ε z - QuadEnvM v ε z)) / (4 * ε) := by
    simp only [JGap]; field_simp; ring
  have hid : (JGap v κ ε zp + JGap v κ ε zm) / 2 - JGap v κ ε z
      = (D + e + D' + e') / (4 * ε) := by rw [hstruct, hmain]
  have hc6 : (D + e) / (4 * ε)
      ≤ (JGap v κ ε zp + JGap v κ ε zm) / 2 - JGap v κ ε z := by
    rw [hid]; exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  -- ===== Step 6: the velocity estimate =====
  obtain ⟨y2, -, -, hy2grad, hy2supp⟩ :=
    DPSpatialRegularity C₀ κ hC₀ hκ v hv hcent hJ ((ofLp z).2) (2 * ε) ht0 hε2 ((ofLp z).1)
  obtain ⟨y1, -, -, hy1grad, hy1supp⟩ :=
    DPSpatialRegularity C₀ κ hC₀ hκ v hv hcent hJ ((ofLp z).2) ε ht0 hε ((ofLp z).1)
  have hQpeq : (2 * ε)⁻¹ • (y2 - (ofLp z).1) = Qp := by
    rw [hQpd]; exact hy2grad.unique hgradP2
  have hQ0eq : ε⁻¹ • (y1 - (ofLp z).1) = Q₀ := hy1grad.unique hQ₀
  have hfree : ∀ b d : F, (inner ℝ (Q₀ - Qp) b : ℝ) + inner ℝ (Q₀ - Qm) d
      - (1 + Real.log 2) / ε * (‖b‖ ^ 2 + ‖d‖ ^ 2) ≤ D + e := by
    intro b d
    -- the three points of the straight path from `x + d` to `x + b`
    have hhalfsmul : ε • ((2 * ε)⁻¹ • (b - d)) = (2 : ℝ)⁻¹ • (b - d) := by
      rw [smul_smul]; congr 1; field_simp
    have hmidpt : (ofLp z).1 + d + ε • ((2 * ε)⁻¹ • (b - d))
        = (ofLp z).1 + (2 : ℝ)⁻¹ • (b + d) := by rw [hhalfsmul]; module
    have hendpt : (ofLp z).1 + d + (2 * ε) • ((2 * ε)⁻¹ • (b - d)) = (ofLp z).1 + b := by
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hε2), one_smul]; abel
    have hpath := hpathP hWsub ((ofLp z).1 + d) ((2 * ε)⁻¹ • (b - d)) ((ofLp z).2) hadm
    have hΦ0 : (fun l : ℝ => QuadEnvP (ContactEnv v κ) l
          (toLp 2 ((ofLp z).1 + d + l • ((2 * ε)⁻¹ • (b - d)), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (l * Real.log l)) 0
        = ContactEnv v κ (toLp 2 ((ofLp z).1 + d, (ofLp z).2)) := by
      show QuadEnvP (ContactEnv v κ) 0
          (toLp 2 ((ofLp z).1 + d + (0 : ℝ) • ((2 * ε)⁻¹ • (b - d)), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * ((0 : ℝ) * Real.log 0) = _
      rw [zero_smul, add_zero, hP0gen]; ring
    have hΦm : (fun l : ℝ => QuadEnvP (ContactEnv v κ) l
          (toLp 2 ((ofLp z).1 + d + l • ((2 * ε)⁻¹ • (b - d)), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (l * Real.log l)) (2 * ε / 2)
        = QuadEnvP (ContactEnv v κ) ε
            (toLp 2 ((ofLp z).1 + (2 : ℝ)⁻¹ • (b + d), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (ε * Real.log ε) := by
      rw [show 2 * ε / 2 = ε from by ring]
      show QuadEnvP (ContactEnv v κ) ε
          (toLp 2 ((ofLp z).1 + d + ε • ((2 * ε)⁻¹ • (b - d)), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (ε * Real.log ε) = _
      rw [hmidpt]
    have hΦT : (fun l : ℝ => QuadEnvP (ContactEnv v κ) l
          (toLp 2 ((ofLp z).1 + d + l • ((2 * ε)⁻¹ • (b - d)), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (l * Real.log l)) (2 * ε)
        = QuadEnvP (ContactEnv v κ) (2 * ε) (toLp 2 ((ofLp z).1 + b, (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (2 * ε * Real.log (2 * ε)) := by
      show QuadEnvP (ContactEnv v κ) (2 * ε)
          (toLp 2 ((ofLp z).1 + d + (2 * ε) • ((2 * ε)⁻¹ • (b - d)), (ofLp z).2))
          + ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (2 * ε * Real.log (2 * ε)) = _
      rw [hendpt]
    have hmm := hmid3 _ (2 * ε) hε2 hpath _ _ _ hΦ0 hΦm hΦT
    -- the `l log l` correction contributes exactly `log 2`
    have hNval : ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 = ‖b - d‖ ^ 2 / (4 * ε ^ 2) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hε2)]
      field_simp; ring
    have hlogexp : Real.log (2 * ε) = Real.log 2 + Real.log ε :=
      Real.log_mul (by norm_num) hεne
    have hIcost : 2 * (‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (ε * Real.log ε))
        - ‖(2 * ε)⁻¹ • (b - d)‖ ^ 2 * (2 * ε * Real.log (2 * ε))
        = -((Real.log 2 / (2 * ε)) * ‖b - d‖ ^ 2) := by
      rw [hNval, hlogexp]; field_simp; ring
    -- the first of the three upper bounds: `x + d` as a forward competitor from `z⁻`
    have hcompd := (hdomW ε zm hε hzmI hzmI').1 ((ofLp z).1 + d)
    rw [hzmt] at hcompd
    have hdiffm : (ofLp z).1 + d - (ofLp zm).1 = d + ε • Qm := by
      rw [hQmd, smul_smul, mul_inv_cancel₀ hεne, one_smul]; abel
    rw [hdiffm, hexp] at hcompd
    -- the second: the upper supporting inequality of the `2ε` envelope at `x + b`
    have hIII := (hy2supp b).2
    rw [hQpeq, hzz] at hIII
    -- the third: the lower supporting inequality of the `ε` envelope at the midpoint
    have hIV := (hy1supp ((2 : ℝ)⁻¹ • (b + d))).1
    rw [hQ0eq, hzz] at hIV
    have hinn0 : (inner ℝ Q₀ ((2 : ℝ)⁻¹ • (b + d)) : ℝ)
        = (2 : ℝ)⁻¹ * inner ℝ Q₀ (b + d) := real_inner_smul_right _ _ _
    have hnrm0 : ‖(2 : ℝ)⁻¹ • (b + d)‖ ^ 2 / (2 * ε) = ‖b + d‖ ^ 2 / (8 * ε) := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹)]
      field_simp; ring
    rw [hinn0, hnrm0] at hIV
    have hconv8 : 2 * (‖b + d‖ ^ 2 / (8 * ε)) = ‖b + d‖ ^ 2 / (4 * ε) := by
      field_simp; ring
    have hinnbd : (inner ℝ Q₀ (b + d) : ℝ) = inner ℝ Q₀ b + inner ℝ Q₀ d :=
      inner_add_right _ _ _
    -- the four quadratic costs, all put over the denominator `4ε` before `linarith`
    have hkey : ‖b + d‖ ^ 2 ≤ 2 * (‖b‖ ^ 2 + ‖d‖ ^ 2) := by
      have h1 := norm_add_sq_real b d
      have h3 := norm_sub_sq_real b d
      have h2 : (0 : ℝ) ≤ ‖b - d‖ ^ 2 := sq_nonneg _
      linarith
    have hkey2 : ‖b - d‖ ^ 2 ≤ 2 * (‖b‖ ^ 2 + ‖d‖ ^ 2) := by
      have h1 := norm_add_sq_real b d
      have h3 := norm_sub_sq_real b d
      have h2 : (0 : ℝ) ≤ ‖b + d‖ ^ 2 := sq_nonneg _
      linarith
    have hcost : ‖b‖ ^ 2 / (2 * (ofLp z).2) + ‖d‖ ^ 2 / (2 * ε) + ‖b + d‖ ^ 2 / (4 * ε)
        + (Real.log 2 / (2 * ε)) * ‖b - d‖ ^ 2
        ≤ (1 + Real.log 2) / ε * (‖b‖ ^ 2 + ‖d‖ ^ 2) := by
      have c1 : ‖b‖ ^ 2 / (2 * (ofLp z).2) ≤ (2 * ‖b‖ ^ 2) / (4 * ε) := by
        have hdiff : (2 * ‖b‖ ^ 2) / (4 * ε) - ‖b‖ ^ 2 / (2 * (ofLp z).2)
            = ‖b‖ ^ 2 * ((ofLp z).2 - ε) / (2 * ε * (ofLp z).2) := by
          field_simp; ring
        have hp : (0 : ℝ) ≤ ‖b‖ ^ 2 * ((ofLp z).2 - ε) / (2 * ε * (ofLp z).2) :=
          div_nonneg (mul_nonneg (sq_nonneg _) (by linarith))
            (le_of_lt (mul_pos (by linarith : (0 : ℝ) < 2 * ε) ht0))
        linarith
      have c2 : ‖d‖ ^ 2 / (2 * ε) = (2 * ‖d‖ ^ 2) / (4 * ε) := by field_simp; ring
      have c3 : ‖b + d‖ ^ 2 / (4 * ε) ≤ (2 * (‖b‖ ^ 2 + ‖d‖ ^ 2)) / (4 * ε) :=
        div_le_div_of_nonneg_right hkey (by linarith)
      have c4 : (Real.log 2 / (2 * ε)) * ‖b - d‖ ^ 2
          ≤ (4 * Real.log 2 * (‖b‖ ^ 2 + ‖d‖ ^ 2)) / (4 * ε) := by
        have h1 : (Real.log 2 / (2 * ε)) * ‖b - d‖ ^ 2
            ≤ (Real.log 2 / (2 * ε)) * (2 * (‖b‖ ^ 2 + ‖d‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hkey2
            (div_nonneg (Real.log_nonneg (by norm_num)) (by linarith))
        have h2 : (Real.log 2 / (2 * ε)) * (2 * (‖b‖ ^ 2 + ‖d‖ ^ 2))
            = (4 * Real.log 2 * (‖b‖ ^ 2 + ‖d‖ ^ 2)) / (4 * ε) := by field_simp
        linarith
      have c5 : (2 * ‖b‖ ^ 2) / (4 * ε) + (2 * ‖d‖ ^ 2) / (4 * ε)
          + (2 * (‖b‖ ^ 2 + ‖d‖ ^ 2)) / (4 * ε)
          + (4 * Real.log 2 * (‖b‖ ^ 2 + ‖d‖ ^ 2)) / (4 * ε)
          = (1 + Real.log 2) / ε * (‖b‖ ^ 2 + ‖d‖ ^ 2) := by field_simp; ring
      linarith
    rw [inner_sub_left, inner_sub_left]
    linarith [hmm, hIcost, hcompd, hIII, hIV, hcost, hconv8, hinnbd, he2, hD]
  -- ===== the optimal choice `b = μ(Q₀ - Q₊)`, `d = μ(Q₀ - Q₋)` =====
  obtain ⟨μ, hμd⟩ : ∃ m : ℝ, m = ε / (2 * (1 + Real.log 2)) := ⟨_, rfl⟩
  have hμpos : 0 < μ := by rw [hμd]; exact div_pos hε (by linarith)
  have hμkey : (1 + Real.log 2) / ε * μ ^ 2 = μ / 2 := by rw [hμd]; field_simp
  have hspec := hfree (μ • (Q₀ - Qp)) (μ • (Q₀ - Qm))
  have hiA : (inner ℝ (Q₀ - Qp) (μ • (Q₀ - Qp)) : ℝ) = μ * ‖Q₀ - Qp‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hiB : (inner ℝ (Q₀ - Qm) (μ • (Q₀ - Qm)) : ℝ) = μ * ‖Q₀ - Qm‖ ^ 2 := by
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hnA : ‖μ • (Q₀ - Qp)‖ ^ 2 = μ ^ 2 * ‖Q₀ - Qp‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]; ring
  have hnB : ‖μ • (Q₀ - Qm)‖ ^ 2 = μ ^ 2 * ‖Q₀ - Qm‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμpos]; ring
  rw [hiA, hiB, hnA, hnB] at hspec
  have hmulA : (1 + Real.log 2) / ε * (μ ^ 2 * ‖Q₀ - Qp‖ ^ 2 + μ ^ 2 * ‖Q₀ - Qm‖ ^ 2)
      = (μ / 2) * (‖Q₀ - Qp‖ ^ 2 + ‖Q₀ - Qm‖ ^ 2) := by rw [← hμkey]; ring
  rw [hmulA] at hspec
  have hc7 : (1 / (16 * (1 + Real.log 2))) * (‖Qp - Q₀‖ ^ 2 + ‖Qm - Q₀‖ ^ 2)
      ≤ (D + e) / (4 * ε) := by
    rw [norm_sub_rev Qp Q₀, norm_sub_rev Qm Q₀]
    have hfin : (1 / (16 * (1 + Real.log 2))) * (‖Q₀ - Qp‖ ^ 2 + ‖Q₀ - Qm‖ ^ 2)
        = ((μ / 2) * (‖Q₀ - Qp‖ ^ 2 + ‖Q₀ - Qm‖ ^ 2)) / (4 * ε) := by
      rw [hμd]; field_simp; ring
    rw [hfin]
    exact div_le_div_of_nonneg_right (by linarith) (by linarith)
  rw [hQpd, hQmd] at hc7
  exact ⟨hc1, hc2, hc3, hc4, hid, hc6, hc7⟩
