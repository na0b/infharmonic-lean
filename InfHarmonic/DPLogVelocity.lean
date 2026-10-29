module

public import InfHarmonic.DPSpatialRegularity
public import InfHarmonic.SpatialFitModulus
public import InfHarmonic.BaryEnvSandwich
public import InfHarmonic.UniformSubquadratic
public import InfHarmonic.BaryEnvDuality
public import InfHarmonic.ContactEnvPositiveTimeRegularity
public import InfHarmonic.ConvexSubgradientExists

@[expose] public section
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 6.6: a logarithmic bound for the reference velocity
`Q₀ = ∇_x P_ε W` on the box of size `K`. -/
theorem DPLogVelocity (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v →
      IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))) → HasJensenBound Set.univ v κ →
      ∀ K : ℝ, 2 ≤ K → ∀ (x : F) (t ε : ℝ),
        ‖x‖ ≤ K → |t| ≤ K → 0 < ε → ε ≤ 1 → ε < t →
        ∀ Q₀ : F,
          HasGradientAt (fun x' : F => QuadEnvP (ContactEnv v κ) ε (toLp 2 (x', t)))
            Q₀ x →
          ‖Q₀‖ ≤ C * ((1 + Real.log K) + |Real.log t|) := by
  classical
  obtain ⟨Cs, hCs0, hCsb⟩ := SpatialFitModulus (F := F) C₀ hC₀
  obtain ⟨C', hC'd⟩ : ∃ r : ℝ,
      r = 1 / 2 + κ ^ 2 / 2 + Cs * (1 + Real.log 4) + Cs * Real.log 2 := ⟨_, rfl⟩
  have hl4 : (0:ℝ) ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hl2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hC'0 : 0 < C' := by
    rw [hC'd]
    have h1 : (0:ℝ) ≤ Cs * (1 + Real.log 4) := by positivity
    have h2 : (0:ℝ) ≤ Cs * Real.log 2 := by positivity
    have h3 : (0:ℝ) ≤ κ ^ 2 / 2 := by positivity
    linarith
  refine ⟨4 * C', by linarith, ?_⟩
  intro v hv hcent hJ K hK x t ε hxK htK hε hε1 hεt Q₀ hQ₀
  -- ===================== Step 0: standing facts =====================================
  have hvcont : ContinuousOn v Set.univ := hv.1.1.2.1
  have hvgrow : SubquadraticGrowth (Set.univ : Set ℝ) v := by
    intro J _ hJc e he
    obtain ⟨M, hM, hMb⟩ := UniformSubquadratic C₀ hC₀ (toLp 2 ((0:F), (1:ℝ)))
      (Or.inr rfl) J hJc e he
    exact ⟨M, hM, fun z hz hzJ => hMb v hv hcent z hz hzJ⟩
  have hsand := BaryEnvSandwich (Set.univ : Set ℝ) v κ hκ hvcont hJ hvgrow
  have hfs : ∀ z : WithLp 2 (F × ℝ), 0 < (ofLp z).2 →
      v z - κ ^ 2 * (ofLp z).2 / 2 ≤ ContactEnv v κ z ∧ ContactEnv v κ z ≤ v z := by
    intro z hz
    obtain ⟨h1, h2⟩ := hsand (ofLp z).2 z hz (Set.mem_univ _)
    rw [ContactEnv]
    constructor <;> linarith
  obtain ⟨_, _, hfconc⟩ :=
    ContactEnvPositiveTimeRegularity C₀ κ hC₀ hκ v hv hcent hJ
  obtain ⟨s, hsd⟩ : ∃ r : ℝ, r = t + ε := ⟨_, rfl⟩
  have ht0 : 0 < t := lt_trans hε hεt
  have hs0 : 0 < s := by rw [hsd]; linarith
  have h2eps : 2 * ε < s := by rw [hsd]; linarith
  have hts : t < s := by rw [hsd]; linarith
  have hst2 : s < 2 * t := by rw [hsd]; linarith
  -- ===================== Step 1: an upper supporting slope ==========================
  obtain ⟨p, hp⟩ : ∃ p : F, ∀ h : F,
      ContactEnv v κ (toLp 2 (x + h, s))
        ≤ ContactEnv v κ (toLp 2 (x, s)) + inner ℝ p h + ‖h‖ ^ 2 / (2 * s) := by
    have hpsi : ConvexOn ℝ (Set.univ : Set F)
        (fun y : F => -(ContactEnv v κ (toLp 2 (y, s)) - ‖y‖ ^ 2 / (2 * s))) := by
      refine ⟨convex_univ, fun u₀ _ u₁ _ α β hα hβ hαβ => ?_⟩
      have h := (hfconc s hs0).2 (Set.mem_univ u₀) (Set.mem_univ u₁) hα hβ hαβ
      simp only [smul_eq_mul] at h ⊢
      linarith
    obtain ⟨q₀, hq₀⟩ := ConvexSubgradientExists (Set.univ : Set F) isOpen_univ _ hpsi x
      (Set.mem_univ _)
    refine ⟨-q₀ + s⁻¹ • x, fun h => ?_⟩
    have h1 := hq₀ (x + h) (Set.mem_univ _)
    have hxh : x + h - x = h := by abel
    simp only [hxh] at h1
    have hnx : ‖x + h‖ ^ 2 = ‖x‖ ^ 2 + 2 * (inner ℝ x h : ℝ) + ‖h‖ ^ 2 :=
      norm_add_sq_real x h
    have hpinner : (inner ℝ (-q₀ + s⁻¹ • x) h : ℝ)
        = -(inner ℝ q₀ h : ℝ) + 2 * (inner ℝ x h : ℝ) / (2 * s) := by
      rw [inner_add_left, inner_neg_left, real_inner_smul_left]
      field_simp
    rw [hpinner]
    have hsplit : (‖x‖ ^ 2 + 2 * (inner ℝ x h : ℝ) + ‖h‖ ^ 2) / (2 * s)
        = ‖x‖ ^ 2 / (2 * s) + 2 * (inner ℝ x h : ℝ) / (2 * s) + ‖h‖ ^ 2 / (2 * s) := by
      ring
    rw [hnx, hsplit] at h1
    linarith [h1]
  -- ===================== Step 2: a bound for ‖p‖ ====================================
  obtain ⟨K₁, hK₁d⟩ : ∃ r : ℝ, r = 2 * K + 1 := ⟨_, rfl⟩
  have hK₁2 : 2 ≤ K₁ := by rw [hK₁d]; linarith
  have hxK₁ : ‖x‖ ≤ K₁ := by rw [hK₁d]; linarith
  have htleK : t ≤ K := le_trans (le_abs_self t) htK
  have hsK₁ : |s| ≤ K₁ := by rw [abs_of_pos hs0, hK₁d, hsd]; linarith
  have hmod : ∀ h : F, ‖h‖ ≤ s →
      |v (toLp 2 (x + h, s)) - v (toLp 2 (x, s))|
        ≤ Cs * s * ((1 + Real.log K₁) + |Real.log s|) := by
    intro h hh
    have hz := hCsb v hv (Or.inr hcent) K₁ hK₁2 (toLp 2 (x, s)) hxK₁ hsK₁ s hs0 h hh
    have hadd : (toLp 2 (x, s) : WithLp 2 (F × ℝ)) + toLp 2 (h, (0:ℝ))
        = toLp 2 (x + h, s) := by
      rw [← WithLp.toLp_add]
      congr 1
      refine Prod.ext rfl ?_
      show s + (0:ℝ) = s
      ring
    rw [hadd] at hz
    exact hz
  -- the two logarithm comparisons the paper records
  have hlogs : |Real.log s| ≤ |Real.log t| + Real.log 2 := by
    rcases le_or_gt 0 (Real.log s) with hls | hls
    · rw [abs_of_nonneg hls]
      have h1 : Real.log s < Real.log (2 * t) := Real.log_lt_log hs0 hst2
      rw [Real.log_mul (by norm_num) (ne_of_gt ht0)] at h1
      have h2 : Real.log t ≤ |Real.log t| := le_abs_self _
      linarith
    · rw [abs_of_neg hls]
      have h1 : Real.log t < Real.log s := Real.log_lt_log ht0 hts
      have h2 : -Real.log t ≤ |Real.log t| := neg_le_abs _
      linarith
  have hlK0 : (0:ℝ) ≤ Real.log K := Real.log_nonneg (by linarith)
  have hLK1 : (1:ℝ) ≤ 1 + Real.log K := by linarith
  have habs0 : (0:ℝ) ≤ |Real.log t| := abs_nonneg _
  have hlogK₁ : 1 + Real.log K₁ ≤ (1 + Real.log 4) * (1 + Real.log K) := by
    have hK0 : (0:ℝ) < K := by linarith
    have h1 : Real.log K₁ ≤ Real.log (4 * K) := by
      refine Real.log_le_log (by rw [hK₁d]; linarith) ?_
      rw [hK₁d]; linarith
    rw [Real.log_mul (by norm_num) (ne_of_gt hK0)] at h1
    nlinarith [h1, mul_nonneg hl4 hlK0]
  have hpbound : ‖p‖ ≤ C' * ((1 + Real.log K) + |Real.log t|) := by
    rcases eq_or_ne p 0 with hp0 | hp0
    · -- the paper's first degenerate branch: the estimate also holds when p = 0
      rw [hp0, norm_zero]
      have hpos : (0:ℝ) < C' * ((1 + Real.log K) + |Real.log t|) :=
        mul_pos hC'0 (by linarith)
      linarith
    · have hpn : 0 < ‖p‖ := norm_pos_iff.mpr hp0
      obtain ⟨h, hhd⟩ : ∃ u : F, u = -(s / ‖p‖) • p := ⟨_, rfl⟩
      have hhn : ‖h‖ = s := by
        rw [hhd, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
        field_simp
      have hph : (inner ℝ p h : ℝ) = -(s * ‖p‖) := by
        rw [hhd, real_inner_smul_right, real_inner_self_eq_norm_sq]
        field_simp
      have hup := hp h
      rw [hph, hhn] at hup
      have hsq : s ^ 2 / (2 * s) = s / 2 := by field_simp
      rw [hsq] at hup
      obtain ⟨hl1, -⟩ := hfs (toLp 2 (x + h, s)) hs0
      obtain ⟨-, hu2⟩ := hfs (toLp 2 (x, s)) hs0
      have hmd := hmod h (le_of_eq hhn)
      have hmd' : -(Cs * s * ((1 + Real.log K₁) + |Real.log s|))
          ≤ v (toLp 2 (x + h, s)) - v (toLp 2 (x, s)) := by
        have h3 := (abs_le.mp hmd).1
        linarith
      have hdiv : ‖p‖ ≤ 1 / 2 + κ ^ 2 / 2
          + Cs * ((1 + Real.log K₁) + |Real.log s|) := by
        have hsp : s * ‖p‖ ≤ s * (1 / 2 + κ ^ 2 / 2
            + Cs * ((1 + Real.log K₁) + |Real.log s|)) := by
          linarith [hup, hl1, hu2, hmd']
        exact le_of_mul_le_mul_left hsp hs0
      have hfinal : 1 / 2 + κ ^ 2 / 2 + Cs * ((1 + Real.log K₁) + |Real.log s|)
          ≤ C' * ((1 + Real.log K) + |Real.log t|) := by
        have hLA : (1:ℝ) ≤ (1 + Real.log K) + |Real.log t| := by linarith
        have ha : Cs * ((1 + Real.log K₁) + |Real.log s|)
            ≤ Cs * ((1 + Real.log 4) * (1 + Real.log K)
                + (|Real.log t| + Real.log 2)) := by
          refine mul_le_mul_of_nonneg_left ?_ hCs0.le
          linarith [hlogK₁, hlogs]
        have hb : Cs * ((1 + Real.log 4) * (1 + Real.log K)
              + (|Real.log t| + Real.log 2)) + (1 / 2 + κ ^ 2 / 2)
            ≤ C' * ((1 + Real.log K) + |Real.log t|) := by
          have hd0 : (0:ℝ) ≤ (1 + Real.log K) + |Real.log t| - 1 := by linarith
          have e1 : (0:ℝ) ≤ Cs * Real.log 4 * |Real.log t| :=
            mul_nonneg (mul_nonneg hCs0.le hl4) (abs_nonneg _)
          have e2 : (0:ℝ) ≤ Cs * Real.log 2 * ((1 + Real.log K) + |Real.log t| - 1) :=
            mul_nonneg (mul_nonneg hCs0.le hl2) hd0
          have e3 : (0:ℝ)
              ≤ (1 / 2 + κ ^ 2 / 2) * ((1 + Real.log K) + |Real.log t| - 1) :=
            mul_nonneg (by positivity) hd0
          have hid : C' * ((1 + Real.log K) + |Real.log t|)
              - (Cs * ((1 + Real.log 4) * (1 + Real.log K)
                  + (|Real.log t| + Real.log 2)) + (1 / 2 + κ ^ 2 / 2))
              = (1 / 2 + κ ^ 2 / 2) * ((1 + Real.log K) + |Real.log t| - 1)
                + Cs * Real.log 4 * |Real.log t|
                + Cs * Real.log 2 * ((1 + Real.log K) + |Real.log t| - 1) := by
            rw [hC'd]; ring
          linarith [e1, e2, e3, hid]
        linarith [ha, hb]
      linarith [hdiv, hfinal]
  -- ============ Step 3: the optimizing displacement and the gradient ============
  obtain ⟨y, hyattain, -, hygrad, -⟩ :=
    DPSpatialRegularity C₀ κ hC₀ hκ v hv hcent hJ t ε ht0 hε x
  have hQ0eq : Q₀ = ε⁻¹ • (y - x) := hQ₀.unique hygrad
  obtain ⟨h, hhd⟩ : ∃ u : F, u = y - x := ⟨_, rfl⟩
  -- The h = 0 competitor.  In Lean the attainment clause of `DPSpatialRegularity` is an
  -- equality with one competitor's value, and `QuadEnvP` is an `sSup` carrying the
  -- preamble's junk value on an unbounded set, so the domination must come from
  -- boundedness.  Here Step 1's own support inequality supplies it: it bounds every
  -- competitor value by a downward parabola in the displacement, because `ε < s`.
  obtain ⟨a, had⟩ : ∃ r : ℝ, r = 1 / (2 * ε) - 1 / (2 * s) := ⟨_, rfl⟩
  have ha0 : 0 < a := by
    rw [had, sub_pos]
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  have hbdd : BddAbove {w : ℝ | ∃ u : F,
      w = ContactEnv v κ (toLp 2 (u, t + ε)) - ‖u - x‖ ^ 2 / (2 * ε)} := by
    refine ⟨ContactEnv v κ (toLp 2 (x, s)) + ‖p‖ ^ 2 / (4 * a), ?_⟩
    rintro w ⟨u, rfl⟩
    have hu : x + (u - x) = u := by abel
    have hsup := hp (u - x)
    rw [hu] at hsup
    rw [← hsd]
    have hinner : (inner ℝ p (u - x) : ℝ) ≤ ‖p‖ * ‖u - x‖ := real_inner_le_norm p (u - x)
    have hpar : ‖p‖ * ‖u - x‖ - a * ‖u - x‖ ^ 2 ≤ ‖p‖ ^ 2 / (4 * a) := by
      have hd4 : (0:ℝ) < 4 * a := by linarith
      rw [le_div_iff₀ hd4]
      nlinarith [sq_nonneg (‖p‖ - 2 * a * ‖u - x‖)]
    have hsplit : ‖u - x‖ ^ 2 / (2 * s) - ‖u - x‖ ^ 2 / (2 * ε)
        = -(a * ‖u - x‖ ^ 2) := by rw [had]; ring
    linarith [hsup, hinner, hpar, hsplit]
  have hcompet : ContactEnv v κ (toLp 2 (x, s))
      ≤ QuadEnvP (ContactEnv v κ) ε (toLp 2 (x, t)) := by
    have hQ : QuadEnvP (ContactEnv v κ) ε (toLp 2 (x, t))
        = sSup {w : ℝ | ∃ u : F,
            w = ContactEnv v κ (toLp 2 (u, t + ε)) - ‖u - x‖ ^ 2 / (2 * ε)} := by
      rw [QuadEnvP, if_neg (ne_of_gt hε)]
    rw [hQ]
    refine le_csSup hbdd ⟨x, ?_⟩
    rw [hsd]
    simp
  -- the inequality the paper extracts from the comparison
  have hkey : ‖h‖ ^ 2 / (2 * ε) ≤ (inner ℝ p h : ℝ) + ‖h‖ ^ 2 / (2 * s) := by
    have hyx : x + h = y := by rw [hhd]; abel
    have hsup := hp h
    rw [hyx] at hsup
    have hatt : QuadEnvP (ContactEnv v κ) ε (toLp 2 (x, t))
        = ContactEnv v κ (toLp 2 (y, s)) - ‖h‖ ^ 2 / (2 * ε) := by
      rw [hhd, hsd]; exact hyattain
    linarith [hcompet, hsup, hatt]
  have hQ0norm : ‖Q₀‖ = ‖h‖ / ε := by
    rw [hQ0eq, ← hhd, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < ε⁻¹)]
    field_simp
  rcases eq_or_ne h 0 with hh0 | hh0
  · -- the paper's second degenerate branch: immediate when the displacement vanishes
    rw [hQ0norm, hh0, norm_zero]
    have hpos : (0:ℝ) < C' * ((1 + Real.log K) + |Real.log t|) :=
      mul_pos hC'0 (by linarith)
    rw [zero_div]
    linarith [hpos]
  · have hhn : 0 < ‖h‖ := norm_pos_iff.mpr hh0
    have hcoef : 1 / (4 * ε) ≤ 1 / (2 * ε) - 1 / (2 * s) := by
      have key : 1 / (2 * ε) - 1 / (2 * s) - 1 / (4 * ε)
          = (2 * s - 4 * ε) / (8 * ε * s) := by
        field_simp
        ring
      have hnum : (0:ℝ) < 2 * s - 4 * ε := by linarith
      have hden : (0:ℝ) < 8 * ε * s := by positivity
      have hq : (0:ℝ) < (2 * s - 4 * ε) / (8 * ε * s) := div_pos hnum hden
      linarith [key, hq]
    have hgap : ‖h‖ ^ 2 / (4 * ε) ≤ (inner ℝ p h : ℝ) := by
      have hsq : (0:ℝ) ≤ ‖h‖ ^ 2 := sq_nonneg _
      have e : ‖h‖ ^ 2 / (2 * ε) - ‖h‖ ^ 2 / (2 * s)
          = (1 / (2 * ε) - 1 / (2 * s)) * ‖h‖ ^ 2 := by ring
      have e2 : ‖h‖ ^ 2 / (4 * ε) = (1 / (4 * ε)) * ‖h‖ ^ 2 := by ring
      have h1 : (1 / (4 * ε)) * ‖h‖ ^ 2
          ≤ (1 / (2 * ε) - 1 / (2 * s)) * ‖h‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hcoef hsq
      rw [e2]
      linarith [hkey, e, h1]
    have hle := real_inner_le_norm p h
    have hdiv : ‖h‖ / ε ≤ 4 * ‖p‖ := by
      have h2 : ‖h‖ ^ 2 / (4 * ε) ≤ ‖p‖ * ‖h‖ := le_trans hgap hle
      have h3 : ‖h‖ * (‖h‖ / (4 * ε)) ≤ ‖h‖ * ‖p‖ := by
        have e : ‖h‖ * (‖h‖ / (4 * ε)) = ‖h‖ ^ 2 / (4 * ε) := by ring
        rw [e]; linarith [h2]
      have h4 : ‖h‖ / (4 * ε) ≤ ‖p‖ := le_of_mul_le_mul_left h3 hhn
      have e2 : ‖h‖ / ε = 4 * (‖h‖ / (4 * ε)) := by field_simp
      rw [e2]; linarith [h4]
    rw [hQ0norm]
    calc ‖h‖ / ε ≤ 4 * ‖p‖ := hdiv
      _ ≤ 4 * (C' * ((1 + Real.log K) + |Real.log t|)) := by linarith [hpbound]
      _ = 4 * C' * ((1 + Real.log K) + |Real.log t|) := by ring
