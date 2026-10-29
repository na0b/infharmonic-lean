module

public import InfHarmonic.ConeComparison
public import InfHarmonic.ConeSlopeContinuousInCenter

@[expose] public section
open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Proposition 2.5, slope limits: at a fixed center the two cone slopes of an
infinity-harmonic function have a common finite nonnegative limit as the radius
tends to zero. -/
theorem ConeSlopeLimitEq (D : Set E) (w : E → ℝ) (hw : IsInfHarmonicOn D w)
    (z : E) (hz : z ∈ D) :
    ∃ L : ℝ, 0 ≤ L ∧
      Tendsto (fun r => ConeSlopeUpper w z r) (𝓝[>] (0 : ℝ)) (𝓝 L) ∧
      Tendsto (fun r => ConeSlopeLower w z r) (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  obtain ⟨hD, hwc, -⟩ := hw.1
  -- Step 0: a radius `r₀ > 0` with `closedBall z (2 * r₀) ⊆ D`.
  obtain ⟨r₀, hr₀, hbig⟩ : ∃ r₀ : ℝ, 0 < r₀ ∧ closedBall z (2 * r₀) ⊆ D := by
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.mp hD z hz
    refine ⟨ε / 4, by positivity, fun x hx => hεD ?_⟩
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  have hsub : ∀ ρ : ℝ, ρ ≤ 2 * r₀ → closedBall z ρ ⊆ D := fun ρ hρ =>
    (closedBall_subset_closedBall hρ).trans hbig
  have hsubc : ∀ (k : E) (ρ : ℝ), ‖k‖ + ρ ≤ 2 * r₀ → closedBall (z + k) ρ ⊆ D := by
    intro k ρ hkρ x hx
    refine hbig ?_
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have hxk : x - z = (x - (z + k)) + k := by abel
    rw [hxk]
    calc ‖(x - (z + k)) + k‖ ≤ ‖x - (z + k)‖ + ‖k‖ := norm_add_le _ _
      _ ≤ ρ + ‖k‖ := by linarith
      _ ≤ 2 * r₀ := by linarith
  -- The generic upper-slope toolkit, in the function `v`, the center `c`, the radius `ρ`.
  have hmemD : ∀ (c : E) (ρ : ℝ), closedBall c ρ ⊆ D →
      ∀ h : E, h ∈ closedBall (0 : E) ρ → c + h ∈ D := by
    intro c ρ hball h hh
    refine hball ?_
    rw [mem_closedBall_iff_norm]
    simpa using mem_closedBall_zero_iff.mp hh
  have hcont : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), closedBall c ρ ⊆ D → ContinuousOn v D →
      ContinuousOn (fun h : E => (v (c + h) - v c) / ρ) (closedBall (0 : E) ρ) := by
    intro v c ρ hball hvc
    refine ContinuousOn.div_const (ContinuousOn.sub ?_ continuousOn_const) ρ
    exact hvc.comp (by fun_prop) (hmemD c ρ hball)
  have hset : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ D → ContinuousOn v D →
      (((fun h => (v (c + h) - v c) / ρ) '' closedBall (0 : E) ρ).Nonempty ∧
       BddAbove ((fun h => (v (c + h) - v c) / ρ) '' closedBall (0 : E) ρ)) := by
    intro v c ρ hρ hball hvc
    exact ⟨⟨(v (c + 0) - v c) / ρ, ⟨0, mem_closedBall_self hρ.le, rfl⟩⟩,
      (isCompact_closedBall (0 : E) ρ).bddAbove_image (hcont v c ρ hball hvc)⟩
  have hle : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ D → ContinuousOn v D →
      ∀ h : E, ‖h‖ ≤ ρ → (v (c + h) - v c) / ρ ≤ ConeSlopeUpper v c ρ := by
    intro v c ρ hρ hball hvc h hh
    exact le_csSup (hset v c ρ hρ hball hvc).2 ⟨h, mem_closedBall_zero_iff.mpr hh, rfl⟩
  have hnn : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ D → ContinuousOn v D →
      0 ≤ ConeSlopeUpper v c ρ := by
    intro v c ρ hρ hball hvc
    simpa using hle v c ρ hρ hball hvc 0 (by simpa using hρ.le)
  -- The supremum defining the upper slope is attained; this is the one fact neither cited
  -- theorem supplies, so it is proved inline by compactness.
  have hattain : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ D → ContinuousOn v D →
      ∃ k : E, ‖k‖ ≤ ρ ∧ ConeSlopeUpper v c ρ = (v (c + k) - v c) / ρ := by
    intro v c ρ hρ hball hvc
    obtain ⟨k, hk, hmax⟩ := (isCompact_closedBall (0 : E) ρ).exists_isMaxOn
      ⟨0, mem_closedBall_self hρ.le⟩ (hcont v c ρ hball hvc)
    refine ⟨k, by simpa using mem_closedBall_zero_iff.mp hk, ?_⟩
    refine le_antisymm (csSup_le (hset v c ρ hρ hball hvc).1 ?_)
      (hle v c ρ hρ hball hvc k (by simpa using mem_closedBall_zero_iff.mp hk))
    rintro x ⟨h, hh, rfl⟩
    exact hmax hh
  -- Exchanging the two slopes under `v ↦ -v`.
  have hexchU : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), ConeSlopeUpper (-v) c ρ = ConeSlopeLower v c ρ := by
    intro v c ρ
    show sSup ((fun h => ((-v) (c + h) - (-v) c) / ρ) '' closedBall (0 : E) ρ)
        = sSup ((fun h => (-(v (c + h) - v c)) / ρ) '' closedBall (0 : E) ρ)
    have hfun : (fun h : E => ((-v) (c + h) - (-v) c) / ρ)
        = fun h : E => (-(v (c + h) - v c)) / ρ := by
      funext h; simp only [Pi.neg_apply]; ring
    rw [hfun]
  have hexchL : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), ConeSlopeLower (-v) c ρ = ConeSlopeUpper v c ρ := by
    intro v c ρ
    show sSup ((fun h => (-((-v) (c + h) - (-v) c)) / ρ) '' closedBall (0 : E) ρ)
        = sSup ((fun h => (v (c + h) - v c) / ρ) '' closedBall (0 : E) ρ)
    have hfun : (fun h : E => (-((-v) (c + h) - (-v) c)) / ρ)
        = fun h : E => (v (c + h) - v c) / ρ := by
      funext h; simp only [Pi.neg_apply]; ring
    rw [hfun]
  have hnnL : ∀ (v : E → ℝ) (c : E) (ρ : ℝ), 0 < ρ → closedBall c ρ ⊆ D → ContinuousOn v D →
      0 ≤ ConeSlopeLower v c ρ := by
    intro v c ρ hρ hball hvc
    rw [← hexchU v c ρ]
    exact hnn (-v) c ρ hρ hball hvc.neg
  -- `-w` is infinity-harmonic on `D`, because `InfLap (-φ) = -InfLap φ` unconditionally.
  have hInfneg : ∀ (φ : E → ℝ) (Y : E), InfLap (-φ) Y = -InfLap φ Y := by
    intro φ Y
    unfold InfLap
    have hg : gradient (-φ) Y = -gradient φ Y := by
      unfold gradient; rw [fderiv_neg]; simp
    rw [hg, iteratedFDeriv_neg_apply]
    have hflip : ∀ M : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ,
        (M fun _ => -gradient φ Y) = M (fun _ => gradient φ Y) := by
      intro M
      have h1 : (fun _ : Fin 2 => -gradient φ Y)
          = fun i : Fin 2 => (fun _ : Fin 2 => (-1 : ℝ)) i •
              (fun _ : Fin 2 => gradient φ Y) i := by
        funext i; simp
      rw [h1, M.map_smul_univ]; simp
    simp [hflip]
  have hwneg : IsInfHarmonicOn D (-w) := by
    constructor
    · refine ⟨hD, hwc.neg, ?_⟩
      intro Y hY φ hφ hmax
      have hmin : IsLocalMinOn (fun x => w x - (-φ) x) D Y := by
        filter_upwards [hmax] with x hx
        simp only [Pi.neg_apply] at hx ⊢
        linarith
      have h := hw.2.2.2 Y hY (-φ) hφ.neg hmin
      rw [hInfneg] at h
      linarith
    · refine ⟨hD, hwc.neg, ?_⟩
      intro Y hY φ hφ hmin
      have hmax : IsLocalMaxOn (fun x => w x - (-φ) x) D Y := by
        filter_upwards [hmin] with x hx
        simp only [Pi.neg_apply] at hx ⊢
        linarith
      have h := hw.1.2.2 Y hY (-φ) hφ.neg hmax
      rw [hInfneg] at h
      linarith
  -- Step 1, pm-0004: the limit is the INFIMUM over `(0, r₀]`, so it needs `Nonempty` and
  -- `BddBelow`.  Nonemptiness is the competitor `ρ = r₀`; the lower bound is `0`.
  have hbbU : ∀ v : E → ℝ, ContinuousOn v D →
      BddBelow ((fun ρ => ConeSlopeUpper v z ρ) '' Ioc 0 r₀) := by
    intro v hvc
    refine ⟨0, ?_⟩
    rintro x ⟨ρ, ⟨h1, h2⟩, rfl⟩
    exact hnn v z ρ h1 (hsub ρ (by linarith)) hvc
  have hbbL : ∀ v : E → ℝ, ContinuousOn v D →
      BddBelow ((fun ρ => ConeSlopeLower v z ρ) '' Ioc 0 r₀) := by
    intro v hvc
    refine ⟨0, ?_⟩
    rintro x ⟨ρ, ⟨h1, h2⟩, rfl⟩
    exact hnnL v z ρ h1 (hsub ρ (by linarith)) hvc
  have hneU : ∀ v : E → ℝ, ((fun ρ => ConeSlopeUpper v z ρ) '' Ioc 0 r₀).Nonempty :=
    fun v => ⟨ConeSlopeUpper v z r₀, ⟨r₀, ⟨hr₀, le_refl _⟩, rfl⟩⟩
  have hneL : ∀ v : E → ℝ, ((fun ρ => ConeSlopeLower v z ρ) '' Ioc 0 r₀).Nonempty :=
    fun v => ⟨ConeSlopeLower v z r₀, ⟨r₀, ⟨hr₀, le_refl _⟩, rfl⟩⟩
  -- A bounded monotone family has a limit at the left endpoint, equal to its infimum.
  have tend : ∀ f : ℝ → ℝ, BddBelow (f '' Ioc 0 r₀) →
      (∀ a b : ℝ, 0 < a → a ≤ b → b ≤ r₀ → f a ≤ f b) →
      Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (sInf (f '' Ioc 0 r₀))) := by
    intro f hbb hmono
    have hne : (f '' Ioc 0 r₀).Nonempty := ⟨f r₀, ⟨r₀, ⟨hr₀, le_refl _⟩, rfl⟩⟩
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      filter_upwards [Ioc_mem_nhdsGT hr₀] with ρ hρ
      exact lt_of_lt_of_le ha (csInf_le hbb ⟨ρ, hρ, rfl⟩)
    · intro b hb
      obtain ⟨y, hy, hyb⟩ := exists_lt_of_csInf_lt hne hb
      obtain ⟨ρ₁, ⟨hρ₁a, hρ₁b⟩, rfl⟩ := hy
      filter_upwards [Ioc_mem_nhdsGT hρ₁a] with ρ hρ
      obtain ⟨hρa, hρb⟩ := hρ
      exact lt_of_le_of_lt (hmono ρ ρ₁ hρa hρb hρ₁b) hyb
  -- Step 2, generic in `v`: the upper limit is at most every admissible lower slope.
  have step2 : ∀ v : E → ℝ, IsInfHarmonicOn D v →
      sInf ((fun ρ => ConeSlopeUpper v z ρ) '' Ioc 0 r₀)
        ≤ sInf ((fun ρ => ConeSlopeLower v z ρ) '' Ioc 0 r₀) := by
    intro v hv
    have hvc : ContinuousOn v D := hv.1.2.1
    refine le_csInf (hneL v) ?_
    rintro x ⟨R, ⟨hR0, hR1⟩, rfl⟩
    by_contra hcon
    rw [not_le] at hcon
    obtain ⟨δ₀, hδ₀, hδ₀le⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ConeSlopeLower v z R + δ₀ ≤ sInf ((fun ρ => ConeSlopeUpper v z ρ) '' Ioc 0 r₀) :=
      ⟨(sInf ((fun ρ => ConeSlopeUpper v z ρ) '' Ioc 0 r₀) - ConeSlopeLower v z R) / 2,
        by linarith, by linarith⟩
    obtain ⟨-, hcty⟩ := ConeSlopeContinuousInCenter D v hv R hR0 z (hsub R (by linarith))
    obtain ⟨δ, hδ, hδc⟩ := Metric.continuousAt_iff.mp hcty δ₀ hδ₀
    obtain ⟨s, hs0, hsR, hsδ⟩ : ∃ s : ℝ, 0 < s ∧ s ≤ R / 2 ∧ s < δ :=
      ⟨min (R / 2) (δ / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
        lt_of_le_of_lt (min_le_right _ _) (by linarith)⟩
    obtain ⟨k, hknorm, hkeq⟩ := hattain v z s hs0 (hsub s (by linarith)) hvc
    -- `-k` is an admissible competitor for the lower slope at the center `z + k`.
    have hcross : ConeSlopeUpper v z s ≤ ConeSlopeLower v (z + k) s := by
      rw [← hexchU v (z + k) s]
      have hcomp := hle (-v) (z + k) s hs0 (hsubc k s (by linarith)) hvc.neg (-k)
        (by simpa using hknorm)
      have hzk : (z + k) + -k = z := by abel
      have heq : ((-v) ((z + k) + -k) - (-v) (z + k)) / s = (v (z + k) - v z) / s := by
        rw [hzk]; simp only [Pi.neg_apply]; ring
      rw [heq] at hcomp
      rw [hkeq]
      exact hcomp
    -- radial monotonicity at the shifted center, from the third conclusion of ConeComparison
    have hmono : ConeSlopeLower v (z + k) s ≤ ConeSlopeLower v (z + k) R := by
      obtain ⟨-, -, hm⟩ := ConeComparison D v hv (z + k) s hs0 (hsubc k s (by linarith))
      exact (hm R (by linarith) (hsubc k R (by linarith))).2
    -- continuity in the center at the fixed radius `R`
    have hclose : dist (z + k) z < δ := by
      rw [dist_eq_norm, add_sub_cancel_left]
      exact lt_of_le_of_lt hknorm hsδ
    have hub : ConeSlopeLower v (z + k) R < ConeSlopeLower v z R + δ₀ := by
      have hd := hδc hclose
      rw [Real.dist_eq] at hd
      have := (abs_lt.mp hd).2
      linarith
    have hinf : sInf ((fun ρ => ConeSlopeUpper v z ρ) '' Ioc 0 r₀) ≤ ConeSlopeUpper v z s :=
      csInf_le (hbbU v hvc) ⟨s, ⟨hs0, by linarith⟩, rfl⟩
    linarith
  -- Step 3: apply Step 2 to `-w` and exchange the slopes back.
  have hfU : (fun ρ => ConeSlopeUpper (-w) z ρ) = fun ρ => ConeSlopeLower w z ρ := by
    funext ρ; exact hexchU w z ρ
  have hfL : (fun ρ => ConeSlopeLower (-w) z ρ) = fun ρ => ConeSlopeUpper w z ρ := by
    funext ρ; exact hexchL w z ρ
  have hrev := step2 (-w) hwneg
  rw [hfU, hfL] at hrev
  have heq : sInf ((fun ρ => ConeSlopeLower w z ρ) '' Ioc 0 r₀)
      = sInf ((fun ρ => ConeSlopeUpper w z ρ) '' Ioc 0 r₀) :=
    le_antisymm hrev (step2 w hw)
  -- Conclusion.
  refine ⟨sInf ((fun ρ => ConeSlopeUpper w z ρ) '' Ioc 0 r₀), ?_, ?_, ?_⟩
  · refine le_csInf (hneU w) ?_
    rintro x ⟨ρ, ⟨h1, h2⟩, rfl⟩
    exact hnn w z ρ h1 (hsub ρ (by linarith)) hwc
  · refine tend _ (hbbU w hwc) ?_
    intro a b ha hab hb
    obtain ⟨-, -, hm⟩ := ConeComparison D w hw z a ha (hsub a (by linarith))
    exact (hm b hab (hsub b (by linarith))).1
  · rw [← heq]
    refine tend _ (hbbL w hwc) ?_
    intro a b ha hab hb
    obtain ⟨-, -, hm⟩ := ConeComparison D w hw z a ha (hsub a (by linarith))
    exact (hm b hab (hsub b (by linarith))).2
