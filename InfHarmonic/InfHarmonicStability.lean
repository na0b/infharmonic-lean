module

public import InfHarmonic.IsInfHarmonicOn

@[expose] public section
open Metric Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Viscosity stability: a locally uniform limit of infinity-harmonic functions
on `Ω` is infinity-harmonic on `Ω`. -/
theorem InfHarmonicStability (Ω : Set E) (hΩ : IsOpen Ω) (u : ℕ → E → ℝ) (u₀ : E → ℝ)
    (hu : ∀ j, IsInfHarmonicOn Ω (u j))
    (hconv : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn u u₀ atTop K) :
    IsInfHarmonicOn Ω u₀ := by
  -- Step 0: continuity of the limit.
  have hu₀cont : ContinuousOn u₀ Ω := by
    refine continuousOn_of_forall_continuousAt fun x hx => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
    have hsub : closedBall x (ε / 2) ⊆ Ω :=
      (closedBall_subset_ball (by linarith)).trans hball
    have h1 : ContinuousOn u₀ (closedBall x (ε / 2)) :=
      (hconv _ hsub (isCompact_closedBall _ _)).continuousOn
        (.of_forall fun j => ((hu j).1.2.1).mono hsub)
    exact h1.continuousAt (closedBall_mem_nhds _ (by linarith))
  -- Steps 1-4, done once for both viscosity clauses. The sign `s` is `+1` for an upper test
  -- (Steps 1-3) and `-1` for a lower test (Step 4): `IsLocalMaxOn (fun x => s * (u₀ x - φ x))`
  -- is a local maximum of `u₀ - φ` when `s = 1` and a local minimum when `s = -1`, and
  -- `0 ≤ s * InfLap φ z` is the subsolution inequality when `s = 1` and the supersolution
  -- inequality when `s = -1`.
  have core : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z ∈ Ω, ∀ φ : E → ℝ,
      ContDiffAt ℝ 2 φ z → IsLocalMaxOn (fun x => s * (u₀ x - φ x)) Ω z →
      0 ≤ s * InfLap φ z := by
    intro s hs z hz φ hφ hmax
    have hs2 : s * s = 1 := by rcases hs with h | h <;> simp [h]
    have hsabs : |s| = 1 := by rcases hs with h | h <;> simp [h]
    -- Step 1: the quartic bump and the strictified test function.
    set q : E → ℝ := fun x => s * (‖x - z‖ ^ 2) ^ 2 with hqdef
    set ψ : E → ℝ := φ + q with hψdef
    have hnormsq : ContDiff ℝ 2 (fun x : E => ‖x - z‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    have hqC : ContDiff ℝ 2 q := contDiff_const.mul (hnormsq.pow 2)
    -- the everywhere derivative of the bump
    have hD : ∀ x : E, HasFDerivAt q ((s * (4 * ‖x - z‖ ^ 2)) • innerSL ℝ (x - z)) x := by
      intro x
      have h1 : HasFDerivAt (fun w : E => w - z) (ContinuousLinearMap.id ℝ E) x :=
        (hasFDerivAt_id x).sub_const z
      refine (((h1.norm_sq).pow 2).const_mul s).congr_fderiv (ContinuousLinearMap.ext fun w => ?_)
      simp
      ring
    have hfd : fderiv ℝ q = fun x => (s * (4 * ‖x - z‖ ^ 2)) • innerSL ℝ (x - z) :=
      funext fun x => (hD x).fderiv
    -- the second derivative of the bump vanishes at the contact point: `eq:stab-fourth`
    have hD2 : fderiv ℝ (fderiv ℝ q) z = (0 : E →L[ℝ] (E →L[ℝ] ℝ)) := by
      rw [hfd]
      have hsub : HasFDerivAt (fun w : E => w - z) (ContinuousLinearMap.id ℝ E) z :=
        (hasFDerivAt_id z).sub_const z
      have hc : HasFDerivAt (fun x : E => s * (4 * ‖x - z‖ ^ 2))
          ((s * 4) • (2 • (innerSL ℝ (z - z)).comp (ContinuousLinearMap.id ℝ E))) z := by
        refine (((hsub.norm_sq).const_mul (4 : ℝ)).const_mul s).congr_fderiv ?_
        apply ContinuousLinearMap.ext; intro w; simp
      have hf : HasFDerivAt (fun x : E => innerSL ℝ (x - z))
          ((innerSL ℝ (E := E)).comp (ContinuousLinearMap.id ℝ E)) z :=
        (innerSL ℝ (E := E)).hasFDerivAt.comp z hsub
      exact ((hc.smul hf).congr_fderiv (by simp)).fderiv
    have hjet : ∀ w : E, iteratedFDeriv ℝ 2 q z (fun _ => w) = 0 := by
      intro w; rw [iteratedFDeriv_two_apply, hD2]; simp
    -- `eq:stab-same-jet`: the strictified test has the same gradient and 2-jet at `z`
    have hq0 : fderiv ℝ q z = 0 := by rw [hfd]; simp
    have hgrad : gradient ψ z = gradient φ z := by
      unfold gradient
      rw [hψdef, fderiv_add (hφ.differentiableAt (by norm_num))
        ((hqC.differentiable (by norm_num)).differentiableAt), hq0]
      simp
    have hjetid : InfLap ψ z = InfLap φ z := by
      unfold InfLap
      rw [hgrad, hψdef, iteratedFDeriv_add_apply (i := 2) hφ hqC.contDiffAt]
      simp [hjet]
    -- a neighbourhood of `z` on which `ψ` is `C²`, inside `Ω`
    obtain ⟨t, ht, hφt⟩ := hφ.contDiffOn (m := 2) le_rfl (by simp)
    obtain ⟨V₀, hV₀t, hV₀open, hzV₀⟩ := _root_.mem_nhds_iff.mp ht
    set V : Set E := V₀ ∩ Ω with hVdef
    have hVopen : IsOpen V := hV₀open.inter hΩ
    have hzV : z ∈ V := ⟨hzV₀, hz⟩
    have hVΩ : V ⊆ Ω := inter_subset_right
    have hψV : ContDiffOn ℝ 2 ψ V :=
      (hφt.mono (fun w hw => hV₀t hw.1)).add (hqC.contDiffOn.mono (subset_univ _))
    have hψcont : ContinuousOn ψ V := hψV.continuousOn
    -- Step 3's continuity of the operator along the test function
    have hLapCont : ContinuousOn (fun x => InfLap ψ x) V := by
      have huniq : UniqueDiffOn ℝ V := hVopen.uniqueDiffOn
      have hA : ContinuousOn (fun x => iteratedFDeriv ℝ 2 ψ x) V := by
        have h := hψV.continuousOn_iteratedFDerivWithin (m := 2) le_rfl huniq
        exact h.congr fun x hx => (iteratedFDerivWithin_of_isOpen (f := ψ) 2 hVopen hx).symm
      have hgr : ContinuousOn (fun x => gradient ψ x) V := by
        have h : ContinuousOn (fderiv ℝ ψ) V := hψV.continuousOn_fderiv_of_isOpen hVopen
          (by norm_num)
        exact ((InnerProductSpace.toDual ℝ E).symm.continuous).comp_continuousOn h
      have hB : ContinuousOn (fun x => (fun _ : Fin 2 => gradient ψ x)) V :=
        continuousOn_pi.2 fun _ => hgr
      exact fun x hx => (hA x hx).eval (hB x hx)
    -- the radius `ϱ` of Step 1: inside `V` and inside the local-maximum neighbourhood
    have hmax' : ∀ᶠ w in 𝓝 z, s * (u₀ w - φ w) ≤ s * (u₀ z - φ z) := by
      have hnw : 𝓝[Ω] z = 𝓝 z := nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hz)
      rw [← hnw]; exact hmax
    obtain ⟨δ₁, hδ₁, hδ₁max⟩ := Metric.eventually_nhds_iff.mp hmax'
    obtain ⟨δ₂, hδ₂, hδ₂V⟩ := Metric.isOpen_iff.mp hVopen z hzV
    set ϱ : ℝ := min δ₁ δ₂ / 2 with hϱdef
    have hϱ : 0 < ϱ := by simp only [hϱdef]; positivity
    have hCV : closedBall z ϱ ⊆ V := by
      refine (closedBall_subset_ball ?_).trans hδ₂V
      simp only [hϱdef]
      have h1 := min_le_right δ₁ δ₂
      have h2 : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      linarith
    have hCmax : ∀ w ∈ closedBall z ϱ, s * (u₀ w - φ w) ≤ s * (u₀ z - φ z) := by
      intro w hw
      refine hδ₁max ?_
      have h1 : dist w z ≤ ϱ := mem_closedBall.mp hw
      have h2 := min_le_left δ₁ δ₂
      have h3 : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      simp only [hϱdef] at h1
      linarith
    have hCΩ : closedBall z ϱ ⊆ Ω := hCV.trans hVΩ
    have hCcpt : IsCompact (closedBall z ϱ) := isCompact_closedBall _ _
    have hzC : z ∈ closedBall z ϱ := mem_closedBall_self hϱ.le
    -- the strictified test has a strict maximum at `z` on the ball
    have hstrict : ∀ w ∈ closedBall z ϱ, w ≠ z → s * (u₀ w - ψ w) < s * (u₀ z - ψ z) := by
      intro w hw hwz
      have hqw : 0 < (‖w - z‖ ^ 2) ^ 2 := by
        have : w - z ≠ 0 := sub_ne_zero_of_ne hwz
        positivity
      have e1 : s * (u₀ w - ψ w) = s * (u₀ w - φ w) - (‖w - z‖ ^ 2) ^ 2 := by
        simp only [hψdef, hqdef, Pi.add_apply]; nlinarith [hs2]
      have e2 : s * (u₀ z - ψ z) = s * (u₀ z - φ z) := by
        simp only [hψdef, hqdef, Pi.add_apply]; simp
      rw [e1, e2]
      have := hCmax w hw
      linarith
    -- Step 2: maximizers of the approximations on the ball
    have hex : ∀ j : ℕ, ∃ w ∈ closedBall z ϱ,
        IsMaxOn (fun y => s * (u j y - ψ y)) (closedBall z ϱ) w := by
      intro j
      have hcj : ContinuousOn (fun y => s * (u j y - ψ y)) (closedBall z ϱ) :=
        continuousOn_const.mul ((((hu j).1.2.1).mono hCΩ).sub (hψcont.mono hCV))
      exact hCcpt.exists_isMaxOn ⟨z, hzC⟩ hcj
    choose ζ hζC hζmax using hex
    -- `ζ j → z`, by the annulus argument rather than the `.tex`'s subsequence route
    have htend : Tendsto ζ atTop (𝓝 z) := by
      refine Metric.tendsto_nhds.2 fun ε hε => ?_
      set r : ℝ := min ε ϱ with hrdef
      have hr : 0 < r := lt_min hε hϱ
      have hrε : r ≤ ε := min_le_left _ _
      by_cases hAempty : ∀ w ∈ closedBall z ϱ, dist w z < r
      · exact .of_forall fun j => lt_of_lt_of_le (hAempty _ (hζC j)) hrε
      · push Not at hAempty
        obtain ⟨w₀, hw₀C, hw₀r⟩ := hAempty
        set A : Set E := {w | w ∈ closedBall z ϱ ∧ r ≤ dist w z} with hAdef
        have hAcpt : IsCompact A := by
          have hAeq : A = closedBall z ϱ ∩ {w | r ≤ dist w z} := rfl
          rw [hAeq]
          exact hCcpt.inter_right
            (isClosed_le continuous_const (continuous_id.dist continuous_const))
        have hAne : A.Nonempty := ⟨w₀, hw₀C, hw₀r⟩
        have hgcont : ContinuousOn (fun y => s * (u₀ y - ψ y)) A :=
          continuousOn_const.mul (((hu₀cont.mono hCΩ).sub (hψcont.mono hCV)).mono
            fun w hw => hw.1)
        obtain ⟨m, hmA, hmmax⟩ := hAcpt.exists_isMaxOn hAne hgcont
        have hmz : m ≠ z := by
          intro h
          have hd : r ≤ dist z z := h ▸ hmA.2
          simp at hd; linarith
        have hlt : s * (u₀ m - ψ m) < s * (u₀ z - ψ z) := hstrict m hmA.1 hmz
        set M : ℝ := s * (u₀ z - ψ z) with hMdef
        set μ : ℝ := s * (u₀ m - ψ m) with hμdef
        have hδpos : 0 < (M - μ) / 2 := by simp only [hMdef, hμdef]; linarith
        have hunif := Metric.tendstoUniformlyOn_iff.mp (hconv _ hCΩ hCcpt) _ hδpos
        filter_upwards [hunif] with j hj
        refine lt_of_lt_of_le ?_ hrε
        by_contra hcon
        push Not at hcon
        have hζA : ζ j ∈ A := ⟨hζC j, hcon⟩
        have hclose : ∀ w ∈ closedBall z ϱ,
            |s * (u j w - ψ w) - s * (u₀ w - ψ w)| < (M - μ) / 2 := by
          intro w hw
          have h1 := hj w hw
          rw [Real.dist_eq] at h1
          have e : s * (u j w - ψ w) - s * (u₀ w - ψ w) = s * (u j w - u₀ w) := by ring
          rw [e, abs_mul, hsabs, one_mul, abs_sub_comm]
          exact h1
        have h1 := abs_lt.mp (hclose z hzC)
        have h2 := abs_lt.mp (hclose (ζ j) (hζC j))
        have h3 : s * (u j z - ψ z) ≤ s * (u j (ζ j) - ψ (ζ j)) := hζmax j hzC
        have h4 : s * (u₀ (ζ j) - ψ (ζ j)) ≤ μ := hmmax hζA
        simp only [← hMdef] at h1 h2 h3 h4 ⊢
        linarith [h1.1, h2.2]
    -- Step 3: the inequality at `ζ j`, then at `z`
    have hineq : ∀ᶠ j in atTop, 0 ≤ s * InfLap ψ (ζ j) := by
      have hballnhd : ∀ᶠ j in atTop, dist (ζ j) z < ϱ := Metric.tendsto_nhds.mp htend ϱ hϱ
      filter_upwards [hballnhd] with j hj
      have hjV : ζ j ∈ V := hCV (mem_closedBall.mpr hj.le)
      have hψat : ContDiffAt ℝ 2 ψ (ζ j) := hψV.contDiffAt (hVopen.mem_nhds hjV)
      have hlocal : ∀ᶠ w in 𝓝[Ω] (ζ j), s * (u j w - ψ w) ≤ s * (u j (ζ j) - ψ (ζ j)) := by
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [Metric.ball_mem_nhds (ζ j) (by linarith : 0 < ϱ - dist (ζ j) z)]
          with w hw
        refine hζmax j (mem_closedBall.mpr ?_)
        have hb := mem_ball.mp hw
        have ht := dist_triangle w (ζ j) z
        linarith
      rcases hs with hs1 | hs1
      · have hsub := (hu j).1.2.2 (ζ j) (hCΩ (mem_closedBall.mpr hj.le)) ψ hψat ?_
        · rw [hs1]; linarith
        · have hml : ∀ᶠ w in 𝓝[Ω] (ζ j), u j w - ψ w ≤ u j (ζ j) - ψ (ζ j) := by
            filter_upwards [hlocal] with w hw
            rw [hs1] at hw; linarith
          exact hml
      · have hsup := (hu j).2.2.2 (ζ j) (hCΩ (mem_closedBall.mpr hj.le)) ψ hψat ?_
        · rw [hs1]; linarith
        · have hml : ∀ᶠ w in 𝓝[Ω] (ζ j), u j (ζ j) - ψ (ζ j) ≤ u j w - ψ w := by
            filter_upwards [hlocal] with w hw
            rw [hs1] at hw; linarith
          exact hml
    have hcontz : Tendsto (fun j => s * InfLap ψ (ζ j)) atTop (𝓝 (s * InfLap ψ z)) :=
      tendsto_const_nhds.mul ((hLapCont.continuousAt (hVopen.mem_nhds hzV)).tendsto.comp htend)
    have hfin : 0 ≤ s * InfLap ψ z := ge_of_tendsto hcontz hineq
    rw [← hjetid]; exact hfin
  -- the two clauses
  refine ⟨⟨hΩ, hu₀cont, ?_⟩, ⟨hΩ, hu₀cont, ?_⟩⟩
  · intro z hz φ hφ hlm
    have h := core 1 (Or.inl rfl) z hz φ hφ (by simpa using hlm)
    linarith
  · intro z hz φ hφ hlm
    have h := core (-1) (Or.inr rfl) z hz φ hφ ?_
    · linarith
    · have hml : ∀ᶠ w in 𝓝[Ω] z, u₀ z - φ z ≤ u₀ w - φ w := hlm
      filter_upwards [hml] with w hw
      simp only [neg_mul, one_mul, neg_le_neg_iff]
      linarith
