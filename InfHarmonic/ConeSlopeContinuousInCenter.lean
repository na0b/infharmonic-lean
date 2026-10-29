module

public import InfHarmonic.IsInfHarmonicOn
public import InfHarmonic.ConeSlopeUpper
public import InfHarmonic.ConeSlopeLower

@[expose] public section
open Metric Set Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Lemma 2.3, continuity in the center: at a fixed allowable radius the two
cone slopes are continuous functions of the center. -/
theorem ConeSlopeContinuousInCenter (D : Set E) (w : E → ℝ) (hw : IsInfHarmonicOn D w)
    (r : ℝ) (hr : 0 < r) (z₀ : E) (hz₀ : closedBall z₀ r ⊆ D) :
    ContinuousAt (fun z => ConeSlopeUpper w z r) z₀ ∧
    ContinuousAt (fun z => ConeSlopeLower w z r) z₀ := by
  obtain ⟨⟨hD, hwc, -⟩, -⟩ := hw
  -- Step 1: a margin `η` with `closedBall z₀ (r + 2η) ⊆ D`.
  obtain ⟨η, hη, hηD⟩ : ∃ η > 0, closedBall z₀ (r + 2 * η) ⊆ D := by
    obtain ⟨δ, hδ, hsub⟩ := (isCompact_closedBall z₀ r).exists_thickening_subset_open hD hz₀
    refine ⟨δ / 4, by positivity, fun x hx => hsub ?_⟩
    rw [mem_closedBall, dist_eq_norm] at hx
    rw [Metric.mem_thickening_iff]
    rcases le_or_gt ‖x - z₀‖ r with h | h
    · exact ⟨x, by simpa [mem_closedBall, dist_eq_norm] using h, by simpa using hδ⟩
    · have hxz : (0:ℝ) < ‖x - z₀‖ := lt_trans hr h
      refine ⟨z₀ + (r / ‖x - z₀‖) • (x - z₀), ?_, ?_⟩
      · rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by positivity), div_mul_cancel₀ _ hxz.ne']
      · have e : x - (z₀ + (r / ‖x - z₀‖) • (x - z₀))
            = (1 - r / ‖x - z₀‖) • (x - z₀) := by rw [sub_smul, one_smul]; abel
        rw [dist_eq_norm, e, norm_smul, Real.norm_eq_abs,
          abs_of_pos (by have : r / ‖x - z₀‖ < 1 := (div_lt_one hxz).mpr h; linarith)]
        have e2 : (1 - r / ‖x - z₀‖) * ‖x - z₀‖ = ‖x - z₀‖ - r := by field_simp
        rw [e2]
        linarith
  -- the generic statement, applied below to `w` and to `-w`
  have key : ∀ f : E → ℝ, ContinuousOn f D →
      ContinuousAt (fun z => sSup ((fun h => (f (z + h) - f z) / r) '' closedBall (0:E) r)) z₀ := by
    intro f hf
    -- Step 2: uniform continuity on the compact margin ball
    have huc : UniformContinuousOn f (closedBall z₀ (r + 2 * η)) :=
      (isCompact_closedBall z₀ (r + 2 * η)).uniformContinuousOn_of_continuous (hf.mono hηD)
    have hmem : ∀ c : E, dist c z₀ ≤ η → ∀ h : E, ‖h‖ ≤ r →
        c + h ∈ closedBall z₀ (r + 2 * η) := by
      intro c hc h hh
      rw [dist_eq_norm] at hc
      rw [mem_closedBall, dist_eq_norm]
      have e : c + h - z₀ = c - z₀ + h := by abel
      calc ‖c + h - z₀‖ = ‖c - z₀ + h‖ := by rw [e]
        _ ≤ ‖c - z₀‖ + ‖h‖ := norm_add_le _ _
        _ ≤ r + 2 * η := by linarith
    -- Step 3: both suprema are of nonempty bounded sets
    have hcont : ∀ c : E, dist c z₀ ≤ η →
        ContinuousOn (fun h => (f (c + h) - f c) / r) (closedBall (0:E) r) := by
      intro c hc
      refine ContinuousOn.div_const (ContinuousOn.sub ?_ continuousOn_const) r
      have hmaps : MapsTo (fun h : E => c + h) (closedBall (0:E) r)
          (closedBall z₀ (r + 2 * η)) := by
        intro h hh
        rw [mem_closedBall, dist_eq_norm, sub_zero] at hh
        exact hmem c hc h hh
      exact (hf.mono hηD).comp (continuous_const.add continuous_id).continuousOn hmaps
    have hball : (closedBall (0:E) r).Nonempty := ⟨0, by simp [hr.le]⟩
    have hne : ∀ c : E, ((fun h => (f (c + h) - f c) / r) '' closedBall (0:E) r).Nonempty :=
      fun c => hball.image _
    have hbdd : ∀ c : E, dist c z₀ ≤ η →
        BddAbove ((fun h => (f (c + h) - f c) / r) '' closedBall (0:E) r) :=
      fun c hc => ((isCompact_closedBall (0:E) r).image_of_continuousOn (hcont c hc)).bddAbove
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδu⟩ := (Metric.uniformContinuousOn_iff.mp huc) (ε * r / 4) (by positivity)
    -- Step 4: the two-sided slope comparison
    have hcomp : ∀ a b : E, dist a z₀ ≤ η → dist b z₀ ≤ η → dist a b < δ →
        sSup ((fun h => (f (a + h) - f a) / r) '' closedBall (0:E) r)
          ≤ sSup ((fun h => (f (b + h) - f b) / r) '' closedBall (0:E) r) + ε / 2 := by
      intro a b ha hb hab
      refine csSup_le (hne a) ?_
      rintro v ⟨h, hh, rfl⟩
      rw [mem_closedBall, dist_eq_norm, sub_zero] at hh
      have h1 : dist (f (a + h)) (f (b + h)) < ε * r / 4 := by
        refine hδu _ (hmem a ha h hh) _ (hmem b hb h hh) ?_
        rw [dist_eq_norm] at hab ⊢
        have e : a + h - (b + h) = a - b := by abel
        rw [e]; exact hab
      have h2 : dist (f a) (f b) < ε * r / 4 := by
        have ha' := hmem a ha 0 (by simp [hr.le])
        have hb' := hmem b hb 0 (by simp [hr.le])
        simp only [add_zero] at ha' hb'
        exact hδu _ ha' _ hb' hab
      have hle : (f (b + h) - f b) / r
          ≤ sSup ((fun h => (f (b + h) - f b) / r) '' closedBall (0:E) r) :=
        le_csSup (hbdd b hb) ⟨h, by simpa [mem_closedBall, dist_eq_norm] using hh, rfl⟩
      rw [Real.dist_eq, abs_lt] at h1 h2
      have hdiv : (f (a + h) - f a) / r ≤ (f (b + h) - f b) / r + ε / 2 := by
        rw [div_le_iff₀ hr]
        have e : ((f (b + h) - f b) / r + ε / 2) * r = f (b + h) - f b + ε * r / 2 := by
          field_simp
        rw [e]
        linarith [h1.1, h1.2, h2.1, h2.2]
      linarith
    refine ⟨min δ η, lt_min hδ hη, fun z hz => ?_⟩
    have hzδ : dist z z₀ < δ := lt_of_lt_of_le hz (min_le_left _ _)
    have hzη : dist z z₀ ≤ η := le_of_lt (lt_of_lt_of_le hz (min_le_right _ _))
    have hz₀η : dist z₀ z₀ ≤ η := by simp [hη.le]
    rw [Real.dist_eq, abs_lt]
    constructor <;>
      linarith [hcomp z z₀ hzη hz₀η hzδ, hcomp z₀ z hz₀η hzη (by rwa [dist_comm] : dist z₀ z < δ)]
  refine ⟨key w hwc, ?_⟩
  have hfun : (fun z => ConeSlopeLower w z r)
      = fun z => sSup ((fun h => ((fun x => -w x) (z + h) - (fun x => -w x) z) / r) ''
          closedBall (0:E) r) := by
    funext z
    exact congrArg sSup (Set.image_congr (fun h _ => by ring)).symm
  rw [hfun]
  exact key (fun x => -w x) hwc.neg
