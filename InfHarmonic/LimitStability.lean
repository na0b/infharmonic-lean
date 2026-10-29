import InfHarmonic.IsLimitSolutionOn
import InfHarmonic.QuarticBumpJetAndRegularity
import InfHarmonic.MaximizerSequenceTendsToStrictMax
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Viscosity stability for the limiting equation: a locally uniform limit of
solutions of `F[v] = 0` on `Ω` is a solution on `Ω`. -/
theorem LimitStability (Ω : Set (WithLp 2 (F × ℝ))) (hΩ : IsOpen Ω)
    (v : ℕ → WithLp 2 (F × ℝ) → ℝ) (v₀ : WithLp 2 (F × ℝ) → ℝ)
    (hv : ∀ j, IsLimitSolutionOn Ω (v j))
    (hconv : ∀ K ⊆ Ω, IsCompact K → TendstoUniformlyOn v v₀ atTop K) :
    IsLimitSolutionOn Ω v₀ := by
  -- Step 0: continuity of the limit.
  have hv₀cont : ContinuousOn v₀ Ω := by
    refine continuousOn_of_forall_continuousAt fun ζ hζ => ?_
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hΩ ζ hζ
    have hsub : closedBall ζ (ε / 2) ⊆ Ω :=
      (closedBall_subset_ball (by linarith)).trans hball
    have h1 : ContinuousOn v₀ (closedBall ζ (ε / 2)) :=
      (hconv _ hsub (isCompact_closedBall _ _)).continuousOn
        (.of_forall fun j => ((hv j).1.2.1).mono hsub)
    exact h1.continuousAt (closedBall_mem_nhds _ (by linarith))
  -- Steps 1-4, done once for both clauses. The sign `s` is `+1` for an upper test
  -- (Steps 1-3) and `-1` for a lower test (Step 4): `IsLocalMaxOn (fun w => s * (v₀ w - φ w))`
  -- is a local maximum of `v₀ - φ` when `s = 1` and a local minimum when `s = -1`, and
  -- `0 ≤ s * LimitOp φ z` is the subsolution inequality when `s = 1` and the supersolution
  -- inequality when `s = -1`.
  have core : ∀ s : ℝ, s = 1 ∨ s = -1 → ∀ z ∈ Ω, ∀ φ : WithLp 2 (F × ℝ) → ℝ,
      ContDiffAt ℝ 2 φ z → IsLocalMaxOn (fun w => s * (v₀ w - φ w)) Ω z →
      0 ≤ s * LimitOp φ z := by
    intro s hs z hz φ hφ hmax
    have hs2 : s * s = 1 := by rcases hs with h | h <;> simp [h]
    have hsabs : |s| = 1 := by rcases hs with h | h <;> simp [h]
    -- Step 1: the quartic bump and the strictified test function.
    obtain ⟨hjetid', V, hVopen, hzV, hVΩ, hψV'⟩ :=
      QuarticBumpJetAndRegularity Ω hΩ z hz s φ hφ
    set q : WithLp 2 (F × ℝ) → ℝ := fun ζ => s * (‖ζ - z‖ ^ 2) ^ 2 with hqdef
    set ψ : WithLp 2 (F × ℝ) → ℝ := φ + q with hψdef
    have hjetid : LimitOp ψ z = LimitOp φ z := hjetid'
    have hψV : ContDiffOn ℝ 2 ψ V := hψV'
    have hψcont : ContinuousOn ψ V := hψV.continuousOn
    -- Step 3's continuity of the operator along the test function
    have hLimCont : ContinuousOn (fun ζ => LimitOp ψ ζ) V := by
      have huniq : UniqueDiffOn ℝ V := hVopen.uniqueDiffOn
      have hA : ContinuousOn (fun ζ => iteratedFDeriv ℝ 2 ψ ζ) V := by
        have h := hψV.continuousOn_iteratedFDerivWithin (m := 2) le_rfl huniq
        exact h.congr fun x hx => (iteratedFDerivWithin_of_isOpen (f := ψ) 2 hVopen hx).symm
      have hgr : ContinuousOn (fun ζ => gradient ψ ζ) V := by
        have h : ContinuousOn (fderiv ℝ ψ) V := hψV.continuousOn_fderiv_of_isOpen hVopen
          (by norm_num)
        exact ((InnerProductSpace.toDual ℝ (WithLp 2 (F × ℝ))).symm.continuous).comp_continuousOn h
      have hB : ContinuousOn
          (fun ζ => (fun _ : Fin 2 => toLp 2 ((ofLp (gradient ψ ζ)).1, (1 : ℝ)))) V :=
        continuousOn_pi.2 fun _ =>
          (WithLp.prod_continuous_toLp 2 F ℝ).comp_continuousOn
            (((continuous_fst.comp (WithLp.prod_continuous_ofLp 2 F ℝ)).comp_continuousOn
              hgr).prodMk continuousOn_const)
      exact fun x hx => (hA x hx).eval (hB x hx)
    -- the radius `ϱ` of Step 1: inside `V` and inside the local-maximum neighbourhood
    have hmax' : ∀ᶠ w in 𝓝 z, s * (v₀ w - φ w) ≤ s * (v₀ z - φ z) := by
      have : 𝓝[Ω] z = 𝓝 z := nhdsWithin_eq_nhds.mpr (hΩ.mem_nhds hz)
      rw [← this]; exact hmax
    obtain ⟨δ₁, hδ₁, hδ₁max⟩ := Metric.eventually_nhds_iff.mp hmax'
    obtain ⟨δ₂, hδ₂, hδ₂V⟩ := Metric.isOpen_iff.mp hVopen z hzV
    set ϱ : ℝ := min δ₁ δ₂ / 2 with hϱdef
    have hϱ : 0 < ϱ := by simp only [hϱdef]; positivity
    have hCV : closedBall z ϱ ⊆ V := by
      refine (closedBall_subset_ball ?_).trans hδ₂V
      simp only [hϱdef]
      have := min_le_right δ₁ δ₂
      have h2 : (0:ℝ) < min δ₁ δ₂ := lt_min hδ₁ hδ₂
      linarith
    have hCmax : ∀ w ∈ closedBall z ϱ, s * (v₀ w - φ w) ≤ s * (v₀ z - φ z) := by
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
    have hstrict : ∀ w ∈ closedBall z ϱ, w ≠ z →
        s * (v₀ w - ψ w) < s * (v₀ z - ψ z) := by
      intro w hw hwz
      have hqw : 0 < (‖w - z‖ ^ 2) ^ 2 := by
        have : w - z ≠ 0 := sub_ne_zero_of_ne hwz
        positivity
      have e1 : s * (v₀ w - ψ w) = s * (v₀ w - φ w) - (‖w - z‖ ^ 2) ^ 2 := by
        simp only [hψdef, hqdef, Pi.add_apply]; nlinarith [hs2]
      have e2 : s * (v₀ z - ψ z) = s * (v₀ z - φ z) := by
        simp only [hψdef, hqdef, Pi.add_apply]; simp
      rw [e1, e2]
      have := hCmax w hw
      linarith
    -- Step 2: maximizers of the approximations on the ball
    have hex : ∀ j : ℕ, ∃ w ∈ closedBall z ϱ,
        IsMaxOn (fun y => s * (v j y - ψ y)) (closedBall z ϱ) w := by
      intro j
      have hcj : ContinuousOn (fun y => s * (v j y - ψ y)) (closedBall z ϱ) :=
        continuousOn_const.mul ((((hv j).1.2.1).mono hCΩ).sub (hψcont.mono hCV))
      exact hCcpt.exists_isMaxOn ⟨z, hzC⟩ hcj
    obtain ⟨ζ, hζC, hζmax, htend⟩ :=
      MaximizerSequenceTendsToStrictMax z ϱ hϱ s hsabs v v₀ ψ (hv₀cont.mono hCΩ)
        (hψcont.mono hCV) (hconv _ hCΩ hCcpt) hstrict hex
    -- Step 3: the inequality at `ζ j`, then at `z`
    have hineq : ∀ᶠ j in atTop, 0 ≤ s * LimitOp ψ (ζ j) := by
      have hballnhd : ∀ᶠ j in atTop, dist (ζ j) z < ϱ := Metric.tendsto_nhds.mp htend ϱ hϱ
      filter_upwards [hballnhd] with j hj
      have hjV : ζ j ∈ V := hCV (mem_closedBall.mpr hj.le)
      have hψat : ContDiffAt ℝ 2 ψ (ζ j) := hψV.contDiffAt (hVopen.mem_nhds hjV)
      have hlocal : ∀ᶠ w in 𝓝[Ω] (ζ j), s * (v j w - ψ w) ≤ s * (v j (ζ j) - ψ (ζ j)) := by
        refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
        filter_upwards [Metric.ball_mem_nhds (ζ j) (by linarith : 0 < ϱ - dist (ζ j) z)]
          with w hw
        refine hζmax j (mem_closedBall.mpr ?_)
        have := mem_ball.mp hw
        have := dist_triangle w (ζ j) z
        linarith
      rcases hs with hs1 | hs1
      · have hsub := (hv j).1.2.2 (ζ j) (hCΩ (mem_closedBall.mpr hj.le)) ψ hψat ?_
        · rw [hs1]; linarith
        · have hml : ∀ᶠ w in 𝓝[Ω] (ζ j), v j w - ψ w ≤ v j (ζ j) - ψ (ζ j) := by
            filter_upwards [hlocal] with w hw
            rw [hs1] at hw; linarith
          exact hml
      · have hsup := (hv j).2.2.2 (ζ j) (hCΩ (mem_closedBall.mpr hj.le)) ψ hψat ?_
        · rw [hs1]; linarith
        · have hml : ∀ᶠ w in 𝓝[Ω] (ζ j), v j (ζ j) - ψ (ζ j) ≤ v j w - ψ w := by
            filter_upwards [hlocal] with w hw
            rw [hs1] at hw; linarith
          exact hml
    have hcontz : Tendsto (fun j => s * LimitOp ψ (ζ j)) atTop (𝓝 (s * LimitOp ψ z)) :=
      (tendsto_const_nhds.mul
        ((hLimCont.continuousAt (hVopen.mem_nhds hzV)).tendsto.comp htend))
    have hfin : 0 ≤ s * LimitOp ψ z := ge_of_tendsto hcontz hineq
    rw [← hjetid]; exact hfin
  -- the two clauses
  refine ⟨⟨hΩ, hv₀cont, ?_⟩, ⟨hΩ, hv₀cont, ?_⟩⟩
  · intro z hz φ hφ hlm
    have := core 1 (Or.inl rfl) z hz φ hφ (by simpa using hlm)
    linarith
  · intro z hz φ hφ hlm
    have := core (-1) (Or.inr rfl) z hz φ hφ ?_
    · linarith
    · have : ∀ᶠ w in 𝓝[Ω] z, v₀ z - φ z ≤ v₀ w - φ w := hlm
      filter_upwards [this] with w hw
      simp only [neg_mul, one_mul, neg_le_neg_iff]
      linarith
