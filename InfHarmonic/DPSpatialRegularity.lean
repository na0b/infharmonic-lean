import InfHarmonic.ContactEnv
import InfHarmonic.QuadEnvP
import InfHarmonic.IsFitClass
import InfHarmonic.IsCenteredAt
import InfHarmonic.HasJensenBound
import InfHarmonic.QuadEnvAttained
import InfHarmonic.ConvexSubgradientExists
import InfHarmonic.ContactEnvPositiveTimeRegularity
import InfHarmonic.QuadEnvPConcaveCorrection
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 6.2: the forward envelope of the contact envelope has a unique
spatial maximizer, is differentiable in the center with gradient
`(y - x)/ℓ`, and obeys the two supporting inequalities (6.4). -/
theorem DPSpatialRegularity (C₀ κ : ℝ) (hC₀ : 1 ≤ C₀) (hκ : 0 ≤ κ)
    (v : WithLp 2 (F × ℝ) → ℝ) (hv : IsFitClass C₀ v)
    (hcent : IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))))
    (hJ : HasJensenBound Set.univ v κ) :
    ∀ (t l : ℝ), 0 < t → 0 < l → ∀ x : F, ∃ y : F,
      (QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t))
          = ContactEnv v κ (toLp 2 (y, t + l)) - ‖y - x‖ ^ 2 / (2 * l)) ∧
      (∀ y' : F, QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t))
          = ContactEnv v κ (toLp 2 (y', t + l)) - ‖y' - x‖ ^ 2 / (2 * l) → y' = y) ∧
      HasGradientAt (fun x' : F => QuadEnvP (ContactEnv v κ) l (toLp 2 (x', t)))
        (l⁻¹ • (y - x)) x ∧
      (∀ h : F,
        QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t))
            + inner ℝ (l⁻¹ • (y - x)) h - ‖h‖ ^ 2 / (2 * l)
          ≤ QuadEnvP (ContactEnv v κ) l (toLp 2 (x + h, t)) ∧
        QuadEnvP (ContactEnv v κ) l (toLp 2 (x + h, t))
          ≤ QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t))
              + inner ℝ (l⁻¹ • (y - x)) h + ‖h‖ ^ 2 / (2 * t)) := by
  classical
  -- ===================== Steps 0 and 1: regularity of the integrand ==================
  obtain ⟨hfcont, hfgrow, hfconc⟩ :=
    ContactEnvPositiveTimeRegularity C₀ κ hC₀ hκ v hv hcent hJ
  obtain ⟨hatt, _, _, _, _, _⟩ :=
    QuadEnvAttained (Set.Ioi (0:ℝ)) isOpen_Ioi (ContactEnv v κ) hfcont hfgrow
  intro t l ht hl x
  have hs : (0:ℝ) < t + l := by linarith
  have hlne : l ≠ 0 := ne_of_gt hl
  -- ===================== Step 3: attainment at every centre =========================
  have hatx : ∀ x' : F, ∃ y : F, QuadEnvP (ContactEnv v κ) l (toLp 2 (x', t))
      = ContactEnv v κ (toLp 2 (y, t + l)) - ‖y - x'‖ ^ 2 / (2 * l) :=
    fun x' => hatt l (toLp 2 (x', t)) hl ht hs
  -- The .tex reads the domination off the attainment, because in natural language a
  -- supremum that is attained is a genuine least upper bound.  In Lean the attainment
  -- clause of `QuadEnvAttained` is only an equality with one competitor's value, and
  -- `QuadEnvP` is an `sSup` carrying the preamble's junk value when the competitor set
  -- is unbounded, so the domination has to be re-derived here from boundedness.
  have hub : ∀ x' y : F, ContactEnv v κ (toLp 2 (y, t + l)) - ‖y - x'‖ ^ 2 / (2 * l)
      ≤ QuadEnvP (ContactEnv v κ) l (toLp 2 (x', t)) := by
    intro x' y
    have hQ : QuadEnvP (ContactEnv v κ) l (toLp 2 (x', t))
        = sSup {w : ℝ | ∃ u : F, w = ContactEnv v κ (toLp 2 (u, t + l))
            - ‖u - x'‖ ^ 2 / (2 * l)} := by
      rw [QuadEnvP, if_neg hlne]
    rw [hQ]
    -- the single-variable objective at this centre
    obtain ⟨g, hg⟩ : ∃ g : F → ℝ, g = fun u : F =>
        ContactEnv v κ (toLp 2 (u, t + l)) - ‖u - x'‖ ^ 2 / (2 * l) := ⟨_, rfl⟩
    -- it is continuous, because the integrand is continuous on positive times
    have hmap : Continuous (fun u : F => (toLp 2 (u, t + l) : WithLp 2 (F × ℝ))) :=
      (WithLp.prodContinuousLinearEquiv 2 ℝ F ℝ).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    have hmaps : ∀ u : F, (toLp 2 (u, t + l) : WithLp 2 (F × ℝ))
        ∈ (fun z : WithLp 2 (F × ℝ) => (ofLp z).2) ⁻¹' Set.Ioi (0:ℝ) := fun u => hs
    have hgc : ContinuousOn g Set.univ := by
      rw [hg]
      refine (ContinuousOn.comp hfcont hmap.continuousOn (fun u _ => hmaps u)).sub ?_
      exact (((continuous_id.sub continuous_const).norm.pow 2).div_const _).continuousOn
    -- far from the origin it is nonpositive, by subquadratic growth
    obtain ⟨M, hM0, hMb⟩ := hfgrow {t + l} (by simpa using hs) isCompact_singleton
      (1 / (16 * l)) (by positivity)
    obtain ⟨M', hM'⟩ : ∃ r : ℝ, r = max M (2 * ‖x'‖) := ⟨_, rfl⟩
    have hM'0 : 0 < M' := by rw [hM']; exact lt_max_of_lt_left hM0
    have hfar : ∀ u : F, M' ≤ ‖u‖ → g u ≤ 0 := by
      intro u hu
      have huM : M ≤ ‖u‖ := le_trans (by rw [hM']; exact le_max_left _ _) hu
      have hx2 : 2 * ‖x'‖ ≤ ‖u‖ := le_trans (by rw [hM']; exact le_max_right _ _) hu
      have hb : |ContactEnv v κ (toLp 2 (u, t + l))| ≤ 1 / (16 * l) * ‖u‖ ^ 2 :=
        hMb (toLp 2 (u, t + l)) huM (by simp)
      have hb' : ContactEnv v κ (toLp 2 (u, t + l)) ≤ 1 / (16 * l) * ‖u‖ ^ 2 :=
        (abs_le.mp hb).2
      have h16 : (0:ℝ) < 16 * l := by linarith
      have hb2 : ContactEnv v κ (toLp 2 (u, t + l)) * (16 * l) ≤ ‖u‖ ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hb' h16.le
        calc ContactEnv v κ (toLp 2 (u, t + l)) * (16 * l)
            ≤ 1 / (16 * l) * ‖u‖ ^ 2 * (16 * l) := hmul
          _ = ‖u‖ ^ 2 := by field_simp
      have hd : ‖u‖ / 2 ≤ ‖u - x'‖ := by
        have h1 : ‖u‖ - ‖x'‖ ≤ ‖u - x'‖ := by simpa using norm_sub_norm_le u x'
        linarith
      have hd2 : ‖u‖ ^ 2 / 4 ≤ ‖u - x'‖ ^ 2 := by
        have hy0 : (0:ℝ) ≤ ‖u‖ / 2 := by positivity
        have hmm := mul_le_mul hd hd hy0 (norm_nonneg (u - x'))
        nlinarith [hmm]
      rw [hg]
      have h2l : (0:ℝ) < 2 * l := by linarith
      show ContactEnv v κ (toLp 2 (u, t + l)) - ‖u - x'‖ ^ 2 / (2 * l) ≤ 0
      rw [sub_nonpos, le_div_iff₀ h2l]
      linarith [hb2, hd2, sq_nonneg ‖u‖]
    -- near the origin it is bounded above by compactness
    obtain ⟨u₁, hu₁mem, hu₁max⟩ := (isCompact_closedBall (0:F) M').exists_isMaxOn
      ⟨0, by simpa using hM'0.le⟩ (hgc.mono (Set.subset_univ _))
    obtain ⟨C, hCd⟩ : ∃ C : ℝ, C = max 0 (g u₁) := ⟨_, rfl⟩
    have hC : ∀ u : F, g u ≤ C := by
      intro u
      rcases le_or_gt M' ‖u‖ with hu | hu
      · exact le_trans (hfar u hu) (by rw [hCd]; exact le_max_left _ _)
      · exact le_trans (hu₁max (by simpa using hu.le)) (by rw [hCd]; exact le_max_right _ _)
    refine le_csSup ⟨C, ?_⟩ ⟨y, rfl⟩
    rintro w ⟨u, rfl⟩
    have := hC u
    rw [hg] at this
    exact this
  -- ===================== Step 5: the corrected envelope is concave ==================
  have hLam : ConcaveOn ℝ (Set.univ : Set F)
      (fun x' : F => QuadEnvP (ContactEnv v κ) l (toLp 2 (x', t)) - ‖x'‖ ^ 2 / (2 * t)) :=
    QuadEnvPConcaveCorrection (ContactEnv v κ) t l ht hl (hfconc (t + l) hs) hatx hub
  -- ===================== Step 2: strict concavity of the objective ==================
  -- the convex-combination identity for the squared norm
  have hquad : ∀ (u₀ u₁ : F) (α β : ℝ), α + β = 1 →
      ‖α • u₀ + β • u₁‖ ^ 2
        = α * ‖u₀‖ ^ 2 + β * ‖u₁‖ ^ 2 - α * β * ‖u₀ - u₁‖ ^ 2 := by
    intro u₀ u₁ α β hαβ
    have hβe : β = 1 - α := by linarith
    subst hβe
    rw [norm_add_sq_real, norm_smul, norm_smul, norm_sub_sq_real,
      real_inner_smul_left, real_inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs]
    ring
  obtain ⟨a, had⟩ : ∃ a : ℝ, a = 1 / (2 * (t + l)) := ⟨_, rfl⟩
  obtain ⟨b, hbd⟩ : ∃ b : ℝ, b = 1 / (2 * l) := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [had]; positivity
  have hab : a < b := by
    rw [had, hbd]
    exact one_div_lt_one_div_of_lt (by linarith) (by linarith)
  obtain ⟨Xi, hXid⟩ : ∃ G : F → ℝ, G = fun w : F =>
      ContactEnv v κ (toLp 2 (w, t + l)) - ‖w - x‖ ^ 2 / (2 * l) := ⟨_, rfl⟩
  have hXiAQ : ∀ w : F, Xi w
      = (ContactEnv v κ (toLp 2 (w, t + l)) - ‖w‖ ^ 2 / (2 * (t + l)))
        + (a * ‖w‖ ^ 2 - b * ‖w - x‖ ^ 2) := by
    intro w
    rw [hXid, had, hbd]
    field_simp
    ring
  have hXistrict : StrictConcaveOn ℝ (Set.univ : Set F) Xi := by
    refine ⟨convex_univ, fun w₀ _ w₁ _ hne α β hα hβ hαβ => ?_⟩
    have hA := (hfconc (t + l) hs).2 (Set.mem_univ w₀) (Set.mem_univ w₁) hα.le hβ.le hαβ
    have hq1 := hquad w₀ w₁ α β hαβ
    have hq2 := hquad (w₀ - x) (w₁ - x) α β hαβ
    have hcomb : α • (w₀ - x) + β • (w₁ - x) = (α • w₀ + β • w₁) - x := by
      have hx1 : α • x + β • x = x := by rw [← add_smul, hαβ, one_smul]
      rw [smul_sub, smul_sub,
        show α • w₀ - α • x + (β • w₁ - β • x)
          = (α • w₀ + β • w₁) - (α • x + β • x) from by abel, hx1]
    have hdiff : (w₀ - x) - (w₁ - x) = w₀ - w₁ := by abel
    rw [hcomb, hdiff] at hq2
    have hwpos : 0 < ‖w₀ - w₁‖ ^ 2 := by
      have h0 : w₀ - w₁ ≠ 0 := sub_ne_zero.mpr hne
      have hn : 0 < ‖w₀ - w₁‖ := norm_pos_iff.mpr h0
      positivity
    have hαβpos : 0 < α * β := mul_pos hα hβ
    simp only [hXiAQ, smul_eq_mul] at *
    nlinarith [hA, hq1, hq2, mul_pos hαβpos hwpos, hab]
  -- every solution of the defining equality is a maximizer of the objective
  have hmaxof : ∀ y' : F,
      QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t))
          = ContactEnv v κ (toLp 2 (y', t + l)) - ‖y' - x‖ ^ 2 / (2 * l) →
      IsMaxOn Xi Set.univ y' := by
    intro y' hy' w _
    show Xi w ≤ Xi y'
    rw [hXid]
    show ContactEnv v κ (toLp 2 (w, t + l)) - ‖w - x‖ ^ 2 / (2 * l)
      ≤ ContactEnv v κ (toLp 2 (y', t + l)) - ‖y' - x‖ ^ 2 / (2 * l)
    rw [← hy']
    exact hub x w
  obtain ⟨y, hy⟩ := hatx x
  obtain ⟨g, hgd⟩ : ∃ g : F, g = l⁻¹ • (y - x) := ⟨_, rfl⟩
  have hlne : l ≠ 0 := ne_of_gt hl
  have htne : t ≠ 0 := ne_of_gt ht
  -- ===================== Step 4: the lower supporting inequality ====================
  have hlower : ∀ h : F,
      QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t)) + inner ℝ g h - ‖h‖ ^ 2 / (2 * l)
        ≤ QuadEnvP (ContactEnv v κ) l (toLp 2 (x + h, t)) := by
    intro h
    have hcomp := hub (x + h) y
    have hyh : y - (x + h) = (y - x) - h := by abel
    have hexp : ‖y - (x + h)‖ ^ 2
        = ‖y - x‖ ^ 2 - 2 * (inner ℝ (y - x) h : ℝ) + ‖h‖ ^ 2 := by
      rw [hyh, norm_sub_sq_real]
    rw [hexp] at hcomp
    have hsplit : (‖y - x‖ ^ 2 - 2 * (inner ℝ (y - x) h : ℝ) + ‖h‖ ^ 2) / (2 * l)
        = ‖y - x‖ ^ 2 / (2 * l) - 2 * (inner ℝ (y - x) h : ℝ) / (2 * l)
          + ‖h‖ ^ 2 / (2 * l) := by ring
    rw [hsplit] at hcomp
    have hginner : (inner ℝ g h : ℝ) = 2 * (inner ℝ (y - x) h : ℝ) / (2 * l) := by
      rw [hgd, real_inner_smul_left]
      field_simp
    rw [hy, hginner]
    linarith [hcomp]
  -- ============ Step 5 tail: a subgradient gives an upper support =============
  obtain ⟨q', hupper⟩ : ∃ q' : F, ∀ h : F,
      QuadEnvP (ContactEnv v κ) l (toLp 2 (x + h, t))
        ≤ QuadEnvP (ContactEnv v κ) l (toLp 2 (x, t)) + inner ℝ q' h
            + ‖h‖ ^ 2 / (2 * t) := by
    have hpsi : ConvexOn ℝ (Set.univ : Set F)
        (fun x' : F =>
          -(QuadEnvP (ContactEnv v κ) l (toLp 2 (x', t)) - ‖x'‖ ^ 2 / (2 * t))) := by
      refine ⟨convex_univ, fun u₀ _ u₁ _ α β hα hβ hαβ => ?_⟩
      have h := hLam.2 (Set.mem_univ u₀) (Set.mem_univ u₁) hα hβ hαβ
      simp only [smul_eq_mul] at h ⊢
      linarith
    obtain ⟨q₀, hq₀⟩ := ConvexSubgradientExists (Set.univ : Set F) isOpen_univ _ hpsi x
      (Set.mem_univ _)
    refine ⟨-q₀ + t⁻¹ • x, fun h => ?_⟩
    have h1 := hq₀ (x + h) (Set.mem_univ _)
    have hxh : x + h - x = h := by abel
    simp only [hxh] at h1
    -- `h1` is the subgradient inequality at the shifted point
    have hnx : ‖x + h‖ ^ 2 = ‖x‖ ^ 2 + 2 * (inner ℝ x h : ℝ) + ‖h‖ ^ 2 :=
      norm_add_sq_real x h
    have hq'inner : (inner ℝ (-q₀ + t⁻¹ • x) h : ℝ)
        = -(inner ℝ q₀ h : ℝ) + 2 * (inner ℝ x h : ℝ) / (2 * t) := by
      rw [inner_add_left, inner_neg_left, real_inner_smul_left]
      field_simp
    rw [hq'inner]
    have hsplit : (‖x‖ ^ 2 + 2 * (inner ℝ x h : ℝ) + ‖h‖ ^ 2) / (2 * t)
        = ‖x‖ ^ 2 / (2 * t) + 2 * (inner ℝ x h : ℝ) / (2 * t) + ‖h‖ ^ 2 / (2 * t) := by
      ring
    rw [hnx, hsplit] at h1
    linarith [h1]
  -- ===================== Step 6: identification of `q'` ==============================
  -- Testing the two supports against the single vector `g - q'` -- rather than against
  -- all unit vectors, as the .tex phrases it -- gives the same conclusion and stays
  -- correct when `F` is the zero space, where a unit vector does not exist.
  have hq'g : q' = g := by
    obtain ⟨w, hwd⟩ : ∃ w : F, w = g - q' := ⟨_, rfl⟩
    obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = 1 / (2 * l) + 1 / (2 * t) := ⟨_, rfl⟩
    have hK0 : 0 < K := by rw [hKd]; positivity
    have hwzero : w = 0 := by
      by_contra hwne
      have hwpos : 0 < ‖w‖ ^ 2 := by
        have hn : 0 < ‖w‖ := norm_pos_iff.mpr hwne
        positivity
      obtain ⟨ρ, hρd⟩ : ∃ r : ℝ, r = 1 / (2 * K) := ⟨_, rfl⟩
      have hρ0 : 0 < ρ := by rw [hρd]; positivity
      have hρK : ρ * K = 1 / 2 := by rw [hρd]; field_simp
      have hlo := hlower (ρ • w)
      have hhi := hupper (ρ • w)
      have hgw : (inner ℝ g (ρ • w) : ℝ) = ρ * (inner ℝ g w : ℝ) :=
        real_inner_smul_right g w ρ
      have hqw : (inner ℝ q' (ρ • w) : ℝ) = ρ * (inner ℝ q' w : ℝ) :=
        real_inner_smul_right q' w ρ
      have hdiffw : (inner ℝ g w : ℝ) - (inner ℝ q' w : ℝ) = ‖w‖ ^ 2 := by
        rw [← inner_sub_left, ← hwd, real_inner_self_eq_norm_sq]
      have hnrm : ‖ρ • w‖ ^ 2 = ρ ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      rw [hgw, hnrm] at hlo
      rw [hqw, hnrm] at hhi
      -- the two bounds give `ρ‖w‖² ≤ ρ²‖w‖²K`, so `1 ≤ ρK = 1/2`
      have hcomb : ρ * ‖w‖ ^ 2 ≤ ρ ^ 2 * ‖w‖ ^ 2 * K := by
        have hsplitK : ρ ^ 2 * ‖w‖ ^ 2 / (2 * l) + ρ ^ 2 * ‖w‖ ^ 2 / (2 * t)
            = ρ ^ 2 * ‖w‖ ^ 2 * K := by rw [hKd]; ring
        nlinarith [hlo, hhi, hdiffw, hsplitK]
      have hfin : (1:ℝ) ≤ ρ * K := by
        have hp : 0 < ρ * ‖w‖ ^ 2 := by positivity
        nlinarith [hcomb, hp, hwpos, hρ0]
      rw [hρK] at hfin
      linarith
    have hgq : g - q' = 0 := by rw [← hwd]; exact hwzero
    have := sub_eq_zero.mp hgq
    exact this.symm
  rw [hq'g] at hupper
  refine ⟨y, hy, ?_, ?_, fun h => ⟨?_, ?_⟩⟩
  · -- uniqueness, from strict concavity
    intro y' hy'
    exact hXistrict.eq_of_isMaxOn (hmaxof y' hy') (hmaxof y hy)
      (Set.mem_univ _) (Set.mem_univ _)
  · -- differentiability, from the two-sided quadratic bound
    rw [← hgd, hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO,
      Asymptotics.isLittleO_iff]
    intro c hc
    obtain ⟨K, hKd⟩ : ∃ K : ℝ, K = 1 / (2 * l) + 1 / (2 * t) := ⟨_, rfl⟩
    have hK0 : 0 < K := by rw [hKd]; positivity
    refine Metric.eventually_nhds_iff.mpr ⟨c / K, by positivity, fun {x'} hx' => ?_⟩
    have hdist : ‖x' - x‖ < c / K := by rwa [dist_eq_norm] at hx'
    have hxx : x + (x' - x) = x' := by abel
    have hlo := hlower (x' - x)
    have hhi := hupper (x' - x)
    rw [hxx] at hlo hhi
    have hKb : ‖x' - x‖ ^ 2 / (2 * l) + ‖x' - x‖ ^ 2 / (2 * t)
        = K * ‖x' - x‖ ^ 2 := by rw [hKd]; ring
    have hval : (InnerProductSpace.toDual ℝ F g) (x' - x) = (inner ℝ g (x' - x) : ℝ) := rfl
    rw [Real.norm_eq_abs, hval, abs_le]
    have hKn : K * ‖x' - x‖ ≤ c := by
      have h1 : ‖x' - x‖ * K < c := (lt_div_iff₀ hK0).mp hdist
      linarith [h1]
    have hD : (0:ℝ) ≤ ‖x' - x‖ := norm_nonneg _
    have hKsq : K * ‖x' - x‖ ^ 2 ≤ c * ‖x' - x‖ := by
      have he : K * ‖x' - x‖ ^ 2 = (K * ‖x' - x‖) * ‖x' - x‖ := by ring
      rw [he]
      exact mul_le_mul_of_nonneg_right hKn hD
    have hb1 : ‖x' - x‖ ^ 2 / (2 * l) ≤ c * ‖x' - x‖ := by
      have h2 : (0:ℝ) ≤ ‖x' - x‖ ^ 2 / (2 * t) := by positivity
      linarith [hKb, h2, hKsq]
    have hb2 : ‖x' - x‖ ^ 2 / (2 * t) ≤ c * ‖x' - x‖ := by
      have h2 : (0:ℝ) ≤ ‖x' - x‖ ^ 2 / (2 * l) := by positivity
      linarith [hKb, h2, hKsq]
    constructor
    · linarith [hlo, hb1]
    · linarith [hhi, hb2]
  · rw [← hgd]; exact hlower h
  · rw [← hgd]; exact hupper h
