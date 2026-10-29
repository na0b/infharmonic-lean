module

public import InfHarmonic.SpatialFitModulus
public import InfHarmonic.CenteredGrowth
public import InfHarmonic.FitParamBound
public import InfHarmonic.LimitStability
public import InfHarmonic.TimeFitModulus

@[expose] public section
open Metric Set Filter Topology WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Lemma 4.2, compactness: a sequence of members of `A_{m,C₀}` centered at a
common point has a locally uniformly convergent subsequence, whose limit lies in
the class and is centered at the same point. -/
theorem ClassCompactness (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (zc : WithLp 2 (F × ℝ))
    (hzc : zc = 0 ∨ zc = toLp 2 ((0 : F), (1 : ℝ)))
    (v : ℕ → WithLp 2 (F × ℝ) → ℝ)
    (hv : ∀ j, IsFitClass C₀ (v j)) (hcent : ∀ j, IsCenteredAt C₀ (v j) zc) :
    ∃ (ι : ℕ → ℕ) (w : WithLp 2 (F × ℝ) → ℝ), StrictMono ι ∧
      (∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K →
        TendstoUniformlyOn (fun j => v (ι j)) w atTop K) ∧
      IsFitClass C₀ w ∧ IsCenteredAt C₀ w zc := by
  classical
  -- ===== Step 0: the four constants, and the centering in the disjunctive form =====
  obtain ⟨Cg, hCg0, hCgb⟩ := CenteredGrowth (F := F) C₀ hC₀
  obtain ⟨Cs, hCs0, hCsb⟩ := SpatialFitModulus (F := F) C₀ hC₀
  obtain ⟨Ct, hCt0, hCtb⟩ := TimeFitModulus (F := F) C₀ hC₀
  obtain ⟨Cp, hCp0, hCpb⟩ := FitParamBound (F := F) C₀ hC₀
  -- the four support nodes already accept either centering point, so the paper's
  -- reduction by a one-unit time translation is absorbed by their own hypotheses.
  have hcz : ∀ j, (IsCenteredAt C₀ (v j) 0
      ∨ IsCenteredAt C₀ (v j) (toLp 2 ((0 : F), (1 : ℝ)))) := by
    intro j
    rcases hzc with h | h
    · exact Or.inl (by rw [← h]; exact hcent j)
    · exact Or.inr (by rw [← h]; exact hcent j)
  have hfst : ∀ z : WithLp 2 (F × ℝ), ‖(ofLp z).1‖ ≤ ‖z‖ := fun z => WithLp.norm_fst_le _ z
  have hnormle : ∀ (q : F) (c : ℝ), ‖(toLp 2 (q, c) : WithLp 2 (F × ℝ))‖ ≤ ‖q‖ + |c| := by
    intro q c
    rw [WithLp.prod_norm_eq_of_L2,
      show (toLp 2 (q, c) : WithLp 2 (F × ℝ)).fst = q from rfl,
      show (toLp 2 (q, c) : WithLp 2 (F × ℝ)).snd = c from rfl, Real.norm_eq_abs]
    have h3 : ‖q‖ ^ 2 + |c| ^ 2 ≤ (‖q‖ + |c|) ^ 2 := by
      nlinarith only [norm_nonneg q, abs_nonneg c]
    calc Real.sqrt (‖q‖ ^ 2 + |c| ^ 2) ≤ Real.sqrt ((‖q‖ + |c|) ^ 2) := Real.sqrt_le_sqrt h3
      _ = ‖q‖ + |c| := Real.sqrt_sq (by positivity)
  have hsnd : ∀ z : WithLp 2 (F × ℝ), |(ofLp z).2| ≤ ‖z‖ := by
    intro z
    have h := WithLp.norm_snd_le _ z
    rwa [Real.norm_eq_abs] at h
  -- ===== Step 1: uniform local bounds =====
  have hbd : ∀ K : ℝ, 2 ≤ K → ∀ (j : ℕ) (z : WithLp 2 (F × ℝ)), ‖z‖ ≤ K →
      |v j z| ≤ Cg * K * (1 + Real.log K) ^ 2 := by
    intro K hK j z hz
    exact hCgb (v j) (hv j) (hcz j) K hK z (le_trans (hfst z) hz) (le_trans (hsnd z) hz)
  -- ===== Step 2: the log modulus bound, and equicontinuity on each ball =====
  -- `s (L + |log s|)^k ≤ (L + 4)^k √s` for `k = 1, 2`, through the fourth root of `s`
  have hmod : ∀ L s : ℝ, 1 ≤ L → 0 < s → s ≤ 1 / 2 →
      s * (L + |Real.log s|) ≤ (L + 4) * Real.sqrt s
      ∧ s * (L + |Real.log s|) ^ 2 ≤ (L ^ 2 + 8 * L + 16) * Real.sqrt s := by
    intro L s hL hs0 hs1
    have hsq0 : (0 : ℝ) < Real.sqrt s := Real.sqrt_pos.mpr hs0
    obtain ⟨u, hudef⟩ : ∃ t : ℝ, t = Real.sqrt (Real.sqrt s) := ⟨_, rfl⟩
    have hu0 : (0 : ℝ) < u := by rw [hudef]; exact Real.sqrt_pos.mpr hsq0
    have hu2 : u ^ 2 = Real.sqrt s := by
      rw [hudef]; exact Real.sq_sqrt (Real.sqrt_nonneg s)
    have hu4 : u ^ 4 = s := by
      have hid : u ^ 4 = (u ^ 2) ^ 2 := by ring
      rw [hid, hu2]; exact Real.sq_sqrt hs0.le
    have hsq1 : Real.sqrt s ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt (by linarith only [hs1])
    have hu1 : u ≤ 1 := by
      rw [hudef, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
      exact Real.sqrt_le_sqrt hsq1
    have husq1 : u ^ 2 ≤ 1 := by nlinarith only [hu0, hu1]
    have hlogu : -Real.log u ≤ 1 / u := by
      have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < u⁻¹ by positivity)
      rw [Real.log_inv, inv_eq_one_div] at h1
      linarith only [h1]
    have hlognp : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
    obtain ⟨Λ, hΛdef⟩ : ∃ t : ℝ, t = |Real.log s| := ⟨_, rfl⟩
    have hΛ0 : (0 : ℝ) ≤ Λ := by rw [hΛdef]; exact abs_nonneg _
    have hΛu : Λ * u ≤ 4 := by
      have hlogeq : Real.log s = 4 * Real.log u := by
        rw [← hu4, Real.log_pow]; push_cast; ring
      have hΛeq : Λ = -(4 * Real.log u) := by
        rw [hΛdef, hlogeq, abs_of_nonpos (by linarith only [hlognp])]
      rw [hΛeq]
      have h2 : -(4 * Real.log u) ≤ 4 * (1 / u) := by linarith only [hlogu]
      have h3 : 4 * (1 / u) * u = 4 := by field_simp
      nlinarith only [h2, h3, hu0]
    have hu42 : u ^ 4 ≤ u ^ 2 := by nlinarith only [husq1, sq_nonneg u, sq_nonneg (u ^ 2)]
    have hu32 : u ^ 3 ≤ u ^ 2 := by nlinarith only [hu0, hu1, sq_nonneg u]
    have hu3nn : (0 : ℝ) ≤ u ^ 3 := by positivity
    have e1 : u ^ 4 * Λ ≤ 4 * u ^ 3 := by
      have hid : u ^ 4 * Λ = u ^ 3 * (Λ * u) := by ring
      rw [hid]
      nlinarith only [hΛu, hu3nn]
    have e2 : u ^ 4 * L ≤ u ^ 2 * L := by nlinarith only [hu42, hL]
    have e5 : u ^ 4 * L ^ 2 ≤ u ^ 2 * L ^ 2 := by nlinarith only [hu42, hL]
    have hLu3 : (0 : ℝ) ≤ L * u ^ 3 := mul_nonneg (by linarith only [hL]) hu3nn
    have e3 : u ^ 4 * (L * Λ) ≤ 4 * (L * u ^ 3) := by
      have hid : u ^ 4 * (L * Λ) = (L * u ^ 3) * (Λ * u) := by ring
      rw [hid]
      nlinarith only [hΛu, hLu3]
    have e4 : u ^ 4 * Λ ^ 2 ≤ 16 * u ^ 2 := by
      have hid : u ^ 4 * Λ ^ 2 = (Λ * u) ^ 2 * u ^ 2 := by ring
      rw [hid]
      have hΛunn : (0 : ℝ) ≤ Λ * u := mul_nonneg hΛ0 hu0.le
      have h16 : (Λ * u) ^ 2 ≤ 16 := by nlinarith only [hΛu, hΛunn]
      nlinarith only [h16, sq_nonneg u]
    have e6 : L * u ^ 3 ≤ L * u ^ 2 := by nlinarith only [hu32, hL]
    rw [← hu2, ← hΛdef, ← hu4]
    constructor
    · nlinarith only [e1, e2, hu32]
    · nlinarith only [e3, e4, e5, e6, hu32]
  have hequi : ∀ K : ℝ, 2 ≤ K → ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      ∀ (j : ℕ) (z z' : WithLp 2 (F × ℝ)), ‖z‖ ≤ K → ‖z'‖ ≤ K → dist z z' ≤ δ →
        |v j z' - v j z| ≤ ε := by
    intro K hK ε hε
    have hL1 : (1 : ℝ) ≤ 1 + Real.log K := by
      have := Real.log_nonneg (by linarith only [hK] : (1 : ℝ) ≤ K); linarith only [this]
    obtain ⟨Mc, hMcdef⟩ : ∃ m : ℝ, m = Cs * ((1 + Real.log K) + 4)
        + Ct * ((1 + Real.log K) ^ 2 + 8 * (1 + Real.log K) + 16) := ⟨_, rfl⟩
    have hMc0 : (0 : ℝ) ≤ Mc := by
      rw [hMcdef]
      have h1 : (0 : ℝ) ≤ Cs * ((1 + Real.log K) + 4) := by
        apply mul_nonneg hCs0.le; linarith only [hL1]
      have h2 : (0 : ℝ) ≤ Ct * ((1 + Real.log K) ^ 2 + 8 * (1 + Real.log K) + 16) := by
        apply mul_nonneg hCt0.le; nlinarith only [hL1]
      linarith only [h1, h2]
    obtain ⟨c, hcdef⟩ : ∃ t : ℝ, t = ε / (2 * (Mc + 1)) := ⟨_, rfl⟩
    have hc0 : 0 < c := by rw [hcdef]; apply div_pos hε; linarith only [hMc0]
    obtain ⟨δ, hδdef⟩ : ∃ t : ℝ, t = min (1 / 2) (c ^ 2) := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδdef]; apply lt_min (by norm_num); positivity
    have hδhalf : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
    have hδc : Real.sqrt δ ≤ c := by
      have h1 : δ ≤ c ^ 2 := by rw [hδdef]; exact min_le_right _ _
      calc Real.sqrt δ ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt h1
        _ = c := Real.sqrt_sq hc0.le
    have hMcc : Mc * c ≤ ε / 2 := by
      rw [hcdef, mul_div_assoc']
      rw [div_le_div_iff₀ (by linarith only [hMc0]) (by norm_num : (0:ℝ) < 2)]
      nlinarith only [hMc0, hε]
    refine ⟨δ, hδ0, hδhalf, ?_⟩
    intro j z z' hz hz' hd
    obtain ⟨hs1, hs2⟩ := hmod (1 + Real.log K) δ hL1 hδ0 hδhalf
    obtain ⟨hh, hhdef⟩ : ∃ q : F, q = (ofLp z').1 - (ofLp z).1 := ⟨_, rfl⟩
    obtain ⟨τ, hτdef⟩ : ∃ t : ℝ, t = (ofLp z').2 - (ofLp z).2 := ⟨_, rfl⟩
    obtain ⟨zm, hzmdef⟩ : ∃ w : WithLp 2 (F × ℝ), w = toLp 2 ((ofLp z').1, (ofLp z).2) :=
      ⟨_, rfl⟩
    have hzsub : ‖hh‖ ≤ δ := by
      rw [hhdef]
      have h1 : ‖(ofLp (z' - z)).1‖ ≤ ‖z' - z‖ := hfst (z' - z)
      have h2 : (ofLp (z' - z)).1 = (ofLp z').1 - (ofLp z).1 := by simp
      rw [h2] at h1
      have h3 : ‖z' - z‖ = dist z z' := by rw [dist_eq_norm, norm_sub_rev]
      rw [h3] at h1
      linarith only [h1, hd]
    have hτsub : |τ| ≤ δ := by
      rw [hτdef]
      have h1 : |(ofLp (z' - z)).2| ≤ ‖z' - z‖ := hsnd (z' - z)
      have h2 : (ofLp (z' - z)).2 = (ofLp z').2 - (ofLp z).2 := by simp
      rw [h2] at h1
      have h3 : ‖z' - z‖ = dist z z' := by rw [dist_eq_norm, norm_sub_rev]
      rw [h3] at h1
      linarith only [h1, hd]
    have hzm1 : (ofLp zm).1 = (ofLp z').1 := by rw [hzmdef]
    have hzm2 : (ofLp zm).2 = (ofLp z).2 := by rw [hzmdef]
    have hstep1 : z + toLp 2 (hh, (0 : ℝ)) = zm := by
      rw [hzmdef, hhdef]
      have h1 : z + toLp 2 ((ofLp z').1 - (ofLp z).1, (0 : ℝ))
          = toLp 2 ((ofLp z).1 + ((ofLp z').1 - (ofLp z).1), (ofLp z).2 + 0) := rfl
      rw [h1, show (ofLp z).1 + ((ofLp z').1 - (ofLp z).1) = (ofLp z').1 from by abel,
        add_zero]
    have hstep2 : zm + toLp 2 ((0 : F), τ) = z' := by
      rw [hzmdef, hτdef]
      have h1 : (toLp 2 ((ofLp z').1, (ofLp z).2) : WithLp 2 (F × ℝ))
          + toLp 2 ((0 : F), (ofLp z').2 - (ofLp z).2)
          = toLp 2 ((ofLp z').1 + 0, (ofLp z).2 + ((ofLp z').2 - (ofLp z).2)) := rfl
      rw [h1, add_zero, show (ofLp z).2 + ((ofLp z').2 - (ofLp z).2) = (ofLp z').2 from by ring]
    -- the spatial half
    have hA : |v j zm - v j z| ≤ ε / 2 := by
      have h := hCsb (v j) (hv j) (hcz j) K hK z (le_trans (hfst z) hz)
        (le_trans (hsnd z) hz) δ hδ0 hh hzsub
      rw [hstep1] at h
      have h4 : Cs * (δ * ((1 + Real.log K) + |Real.log δ|))
          ≤ Cs * (((1 + Real.log K) + 4) * Real.sqrt δ) :=
        mul_le_mul_of_nonneg_left hs1 hCs0.le
      have h5 : Cs * (((1 + Real.log K) + 4) * Real.sqrt δ) ≤ Mc * Real.sqrt δ := by
        rw [hMcdef]
        have h6 : (0 : ℝ) ≤ Real.sqrt δ := Real.sqrt_nonneg δ
        have h7 : (0 : ℝ) ≤ Ct * ((1 + Real.log K) ^ 2 + 8 * (1 + Real.log K) + 16) := by
          apply mul_nonneg hCt0.le; nlinarith only [hL1]
        nlinarith only [h6, h7]
      have h8 : Mc * Real.sqrt δ ≤ Mc * c := mul_le_mul_of_nonneg_left hδc hMc0
      nlinarith only [h, h4, h5, h8, hMcc]
    -- the time half
    have hB : |v j z' - v j zm| ≤ ε / 2 := by
      rcases eq_or_ne τ 0 with h0 | h0
      · have hzz : z' = zm := by rw [← hstep2, h0]; simp
        rw [hzz, sub_self, abs_zero]
        linarith only [hε]
      · have hτ0 : 0 < |τ| := abs_pos.mpr h0
        have hτh : |τ| ≤ 1 / 2 := le_trans hτsub hδhalf
        have h := hCtb (v j) (hv j) (hcz j) K hK zm
          (by rw [hzm1]; exact le_trans (hfst z') hz') (by rw [hzm2]; exact le_trans (hsnd z) hz)
          τ hτ0 hτh
        rw [hstep2] at h
        obtain ⟨-, ht2⟩ := hmod (1 + Real.log K) (|τ|) hL1 hτ0 hτh
        have h4 : Ct * (|τ| * ((1 + Real.log K) + |Real.log (|τ|)|) ^ 2)
            ≤ Ct * (((1 + Real.log K) ^ 2 + 8 * (1 + Real.log K) + 16) * Real.sqrt (|τ|)) :=
          mul_le_mul_of_nonneg_left ht2 hCt0.le
        have h5 : Ct * (((1 + Real.log K) ^ 2 + 8 * (1 + Real.log K) + 16)
            * Real.sqrt (|τ|)) ≤ Mc * Real.sqrt (|τ|) := by
          rw [hMcdef]
          have h6 : (0 : ℝ) ≤ Real.sqrt (|τ|) := Real.sqrt_nonneg _
          have h7 : (0 : ℝ) ≤ Cs * ((1 + Real.log K) + 4) := by
            apply mul_nonneg hCs0.le; linarith only [hL1]
          nlinarith only [h6, h7]
        have h9 : Real.sqrt (|τ|) ≤ Real.sqrt δ := Real.sqrt_le_sqrt hτsub
        have h10 : Mc * Real.sqrt (|τ|) ≤ Mc * Real.sqrt δ :=
          mul_le_mul_of_nonneg_left h9 hMc0
        have h8 : Mc * Real.sqrt δ ≤ Mc * c := mul_le_mul_of_nonneg_left hδc hMc0
        nlinarith only [h, h4, h5, h10, h8, hMcc]
    have htri : |v j z' - v j z| ≤ |v j z' - v j zm| + |v j zm - v j z| := by
      have := abs_add_le (v j z' - v j zm) (v j zm - v j z)
      have hid : v j z' - v j zm + (v j zm - v j z) = v j z' - v j z := by ring
      rw [hid] at this
      exact this
    linarith only [htri, hA, hB]
  -- ===== Step 3a: pointwise convergence along one subsequence on a dense sequence =====
  obtain ⟨Q, hQ⟩ : ∃ q : ℕ → WithLp 2 (F × ℝ), DenseRange q :=
    ⟨TopologicalSpace.denseSeq (WithLp 2 (F × ℝ)),
      TopologicalSpace.denseRange_denseSeq (WithLp 2 (F × ℝ))⟩
  obtain ⟨Aq, hAqdef⟩ : ∃ a : ℕ → ℝ, a = fun k =>
    Cg * (max 2 ‖Q k‖) * (1 + Real.log (max 2 ‖Q k‖)) ^ 2 := ⟨_, rfl⟩
  have hAqb : ∀ (j k : ℕ), |v j (Q k)| ≤ Aq k := by
    intro j k
    rw [hAqdef]
    exact hbd (max 2 ‖Q k‖) (le_max_left _ _) j (Q k) (le_max_right _ _)
  have hcpt : IsCompact (Set.univ.pi (fun k : ℕ => Set.Icc (-(Aq k)) (Aq k))) :=
    isCompact_univ_pi fun k => isCompact_Icc
  have hmem : ∀ j : ℕ, (fun k => v j (Q k))
      ∈ Set.univ.pi (fun k : ℕ => Set.Icc (-(Aq k)) (Aq k)) := by
    intro j k _
    have h := hAqb j k
    exact Set.mem_Icc.mpr ⟨by linarith only [abs_le.mp h], (abs_le.mp h).2⟩
  obtain ⟨a, -, φ, hφmono, hφtend⟩ := hcpt.tendsto_subseq hmem
  have hptdense : ∀ k : ℕ, Tendsto (fun j => v (φ j) (Q k)) atTop (𝓝 (a k)) := by
    intro k
    exact (tendsto_pi_nhds.mp hφtend) k
  -- ===== Step 3b: uniformly Cauchy on each closed ball =====
  have hcau : ∀ R : ℝ, 2 ≤ R →
      UniformCauchySeqOn (fun j => v (φ j)) atTop (Metric.closedBall (0 : WithLp 2 (F × ℝ)) R) := by
    intro R hR
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    obtain ⟨δ, hδ0, hδh, hδb⟩ := hequi (R + 1) (by linarith only [hR]) (ε / 4) (by linarith only [hε])
    -- cover the ball by finitely many `δ`-balls centred at dense points
    have hcov : Metric.closedBall (0 : WithLp 2 (F × ℝ)) R ⊆ ⋃ k : ℕ, Metric.ball (Q k) δ := by
      intro x _
      obtain ⟨k, hk⟩ := Metric.denseRange_iff.mp hQ x δ hδ0
      exact Set.mem_iUnion.mpr ⟨k, by rwa [Metric.mem_ball]⟩
    obtain ⟨t, ht⟩ := (isCompact_closedBall (0 : WithLp 2 (F × ℝ)) R).elim_finite_subcover
      (fun k : ℕ => Metric.ball (Q k) δ) (fun k => Metric.isOpen_ball) hcov
    have hev : ∀ᶠ j in atTop, ∀ k ∈ t, |v (φ j) (Q k) - a k| < ε / 4 := by
      refine (Filter.eventually_all_finset t).mpr fun k _ => ?_
      have h := (hptdense k)
        (Metric.ball_mem_nhds (a k) (show (0 : ℝ) < ε / 4 by linarith only [hε]))
      filter_upwards [h] with j hj
      have hj' : dist (v (φ j) (Q k)) (a k) < ε / 4 := hj
      rwa [Real.dist_eq] at hj'
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N, fun m hm n hn x hx => ?_⟩
    obtain ⟨k, hkt, hkx⟩ := Set.mem_iUnion₂.mp (ht hx)
    have hxR : ‖x‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx
    have hQk : ‖Q k‖ ≤ R + 1 := by
      have h1 : dist x (Q k) < δ := Metric.mem_ball.mp hkx
      have h2 : dist (Q k) (0 : WithLp 2 (F × ℝ)) ≤ dist (Q k) x + dist x 0 :=
        dist_triangle _ _ _
      simp only [dist_zero_right] at h2
      rw [dist_comm (Q k) x] at h2
      linarith only [h1, h2, hxR, hδh]
    have hxR' : ‖x‖ ≤ R + 1 := by linarith only [hxR]
    have hd : dist (Q k) x ≤ δ := by
      rw [dist_comm]; exact le_of_lt (Metric.mem_ball.mp hkx)
    have hA1 := hδb (φ m) (Q k) x hQk hxR' hd
    have hA2 := hδb (φ n) (Q k) x hQk hxR' hd
    have hB1 := hN m hm k hkt
    have hB2 := hN n hn k hkt
    rw [Real.dist_eq]
    have hid : v (φ m) x - v (φ n) x
        = (v (φ m) x - v (φ m) (Q k)) + (v (φ m) (Q k) - a k)
          - (v (φ n) (Q k) - a k) - (v (φ n) x - v (φ n) (Q k)) := by ring
    have h1 := abs_le.mp hA1
    have h2 := abs_le.mp hA2
    have h3 := abs_lt.mp hB1
    have h4 := abs_lt.mp hB2
    rw [abs_lt]
    constructor
    · rw [hid]; linarith only [h1, h2, h3, h4]
    · rw [hid]; linarith only [h1, h2, h3, h4]
  -- ===== Step 3c: the pointwise limit `w` and uniform convergence on compacts =====
  have hptall : ∀ z : WithLp 2 (F × ℝ), ∃ L : ℝ, Tendsto (fun j => v (φ j) z) atTop (𝓝 L) := by
    intro z
    have hcs : CauchySeq (fun j => v (φ j) z) := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨N, hN⟩ := (Metric.uniformCauchySeqOn_iff.mp
        (hcau (max 2 ‖z‖) (le_max_left _ _))) ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hzm : z ∈ Metric.closedBall (0 : WithLp 2 (F × ℝ)) (max 2 ‖z‖) := by
        rw [Metric.mem_closedBall, dist_zero_right]; exact le_max_right _ _
      exact hN n hn N le_rfl z hzm
    exact cauchySeq_tendsto_of_complete hcs
  choose w hw using hptall
  have hconv : ∀ K : Set (WithLp 2 (F × ℝ)), IsCompact K →
      TendstoUniformlyOn (fun j => v (φ j)) w atTop K := by
    intro K hKc
    obtain ⟨R, hRb⟩ := hKc.isBounded.subset_closedBall (0 : WithLp 2 (F × ℝ))
    have hsub : K ⊆ Metric.closedBall (0 : WithLp 2 (F × ℝ)) (max 2 R) :=
      hRb.trans (Metric.closedBall_subset_closedBall (le_max_right _ _))
    refine TendstoUniformlyOn.mono ?_ hsub
    exact (hcau (max 2 R) (le_max_left _ _)).tendstoUniformlyOn_of_tendsto fun x _ => hw x
  -- ===== Step 4: `w` solves the equation =====
  have hwsol : IsLimitSolutionOn (Set.univ : Set (WithLp 2 (F × ℝ))) w :=
    LimitStability (Set.univ : Set (WithLp 2 (F × ℝ))) isOpen_univ (fun j => v (φ j)) w
      (fun j => (hv (φ j)).1) (fun K _ hKc => hconv K hKc)
  have hwcont : Continuous w := continuousOn_univ.mp hwsol.1.2.1
  -- ===== Step 5: `w` has fits at every centre and radius =====
  have hwfit : ∀ (z : WithLp 2 (F × ℝ)) (R : ℝ), 0 < R → ∃ (p : F) (b : ℝ),
      IsFit C₀ w z R p b := by
    intro z R hR
    obtain ⟨K, hKdef⟩ : ∃ t : ℝ, t = max 2 ‖z‖ := ⟨_, rfl⟩
    have hK2 : 2 ≤ K := by rw [hKdef]; exact le_max_left _ _
    have hz1 : ‖(ofLp z).1‖ ≤ K := by
      rw [hKdef]; exact le_trans (hfst z) (le_max_right _ _)
    have hz2 : |(ofLp z).2| ≤ K := by
      rw [hKdef]; exact le_trans (hsnd z) (le_max_right _ _)
    have hfits : ∀ j : ℕ, ∃ q : F × ℝ, IsFit C₀ (v (φ j)) z R q.1 q.2 := by
      intro j
      obtain ⟨p, b, hp⟩ := (hv (φ j)).2 z R hR
      exact ⟨(p, b), hp⟩
    choose P hP using hfits
    obtain ⟨Bnd, hBnddef⟩ : ∃ t : ℝ, t = Cp * ((1 + Real.log K) + |Real.log R|) := ⟨_, rfl⟩
    have hPb : ∀ j : ℕ, ‖(P j).1‖ + |(P j).2| ≤ Bnd := by
      intro j
      rw [hBnddef]
      exact hCpb (v (φ j)) (hv (φ j)) (hcz (φ j)) K hK2 z hz1 hz2 R hR (P j).1 (P j).2 (hP j)
    have hBnd0 : (0 : ℝ) ≤ Bnd := by
      have h := hPb 0
      have h1 : (0 : ℝ) ≤ ‖(P 0).1‖ := norm_nonneg _
      have h2 : (0 : ℝ) ≤ |(P 0).2| := abs_nonneg _
      linarith only [h, h1, h2]
    have hPmem : ∀ j : ℕ, P j ∈
        (Metric.closedBall (0 : F) Bnd) ×ˢ (Set.Icc (-Bnd) Bnd) := by
      intro j
      have h := hPb j
      have h1 : (0 : ℝ) ≤ ‖(P j).1‖ := norm_nonneg _
      have h2 : (0 : ℝ) ≤ |(P j).2| := abs_nonneg _
      refine Set.mk_mem_prod ?_ ?_
      · rw [Metric.mem_closedBall, dist_zero_right]; linarith only [h, h2]
      · have h3 := abs_le.mp (show |(P j).2| ≤ Bnd by linarith only [h, h1])
        exact Set.mem_Icc.mpr h3
    have hPcpt : IsCompact ((Metric.closedBall (0 : F) Bnd) ×ˢ (Set.Icc (-Bnd) Bnd)) :=
      (isCompact_closedBall (0 : F) Bnd).prod isCompact_Icc
    obtain ⟨pa, -, ψ, hψmono, hψtend⟩ := hPcpt.tendsto_subseq hPmem
    refine ⟨pa.1, pa.2, ?_⟩
    intro h l hl hhl
    -- the corrected increments, admissible for every member of the subsequence
    obtain ⟨hk, hkdef⟩ : ∃ g : ℕ → F, g = fun k => l • (P (ψ k)).1 + (h - l • pa.1) :=
      ⟨_, rfl⟩
    have hkadm : ∀ k, ‖hk k - l • (P (ψ k)).1‖ ≤ R := by
      intro k
      rw [hkdef, show l • (P (ψ k)).1 + (h - l • pa.1) - l • (P (ψ k)).1
        = h - l • pa.1 from by abel]
      exact hhl
    have hPtend : Tendsto (fun k => (P (ψ k)).1) atTop (𝓝 pa.1) :=
      (continuous_fst.tendsto pa).comp hψtend
    have hPtend2 : Tendsto (fun k => (P (ψ k)).2) atTop (𝓝 pa.2) :=
      (continuous_snd.tendsto pa).comp hψtend
    have hhktend : Tendsto hk atTop (𝓝 h) := by
      rw [hkdef]
      have h1 : Tendsto (fun k => l • (P (ψ k)).1 + (h - l • pa.1)) atTop
          (𝓝 (l • pa.1 + (h - l • pa.1))) :=
        ((continuous_const_smul l).tendsto pa.1).comp hPtend |>.add tendsto_const_nhds
      rwa [show l • pa.1 + (h - l • pa.1) = h from by abel] at h1
    -- the moving evaluation point
    obtain ⟨ζ, hζdef⟩ : ∃ g : ℕ → WithLp 2 (F × ℝ), g = fun k => z + toLp 2 (hk k, l) :=
      ⟨_, rfl⟩
    have hζtend : Tendsto ζ atTop (𝓝 (z + toLp 2 (h, l))) := by
      rw [hζdef]
      have hcm : Continuous fun q : F => (toLp 2 (q, l) : WithLp 2 (F × ℝ)) := by fun_prop
      exact tendsto_const_nhds.add ((hcm.tendsto h).comp hhktend)
    -- all the evaluation points sit in one compact ball
    obtain ⟨Rb, hRbdef⟩ : ∃ t : ℝ, t = ‖z‖ + (|l| * Bnd + ‖h - l • pa.1‖) + |l| + 1 :=
      ⟨_, rfl⟩
    have hζball : ∀ k, ζ k ∈ Metric.closedBall (0 : WithLp 2 (F × ℝ)) Rb := by
      intro k
      rw [Metric.mem_closedBall, dist_zero_right, hζdef, hRbdef]
      have h1 : ‖z + toLp 2 (hk k, l)‖ ≤ ‖z‖ + ‖(toLp 2 (hk k, l) : WithLp 2 (F × ℝ))‖ :=
        norm_add_le _ _
      have h2 : ‖(toLp 2 (hk k, l) : WithLp 2 (F × ℝ))‖ ≤ ‖hk k‖ + |l| := hnormle (hk k) l
      have h7 : ‖hk k‖ ≤ |l| * Bnd + ‖h - l • pa.1‖ := by
        rw [hkdef]
        have h8 : ‖l • (P (ψ k)).1 + (h - l • pa.1)‖
            ≤ ‖l • (P (ψ k)).1‖ + ‖h - l • pa.1‖ := norm_add_le _ _
        have h9 : ‖l • (P (ψ k)).1‖ = |l| * ‖(P (ψ k)).1‖ := by
          rw [norm_smul, Real.norm_eq_abs]
        have h10 : ‖(P (ψ k)).1‖ ≤ Bnd := by
          have := hPb (ψ k)
          have := abs_nonneg (P (ψ k)).2
          linarith only [hPb (ψ k), abs_nonneg (P (ψ k)).2]
        have h11 : |l| * ‖(P (ψ k)).1‖ ≤ |l| * Bnd :=
          mul_le_mul_of_nonneg_left h10 (abs_nonneg l)
        linarith only [h8, h9, h11]
      linarith only [h1, h2, h7]
    have hRb2 : 2 ≤ max 2 Rb := le_max_left _ _
    have hζball' : ∀ k, ζ k ∈ Metric.closedBall (0 : WithLp 2 (F × ℝ)) (max 2 Rb) :=
      fun k => Metric.closedBall_subset_closedBall (le_max_right _ _) (hζball k)
    have hlimball : (z + toLp 2 (h, l))
        ∈ Metric.closedBall (0 : WithLp 2 (F × ℝ)) (max 2 Rb) :=
      (Metric.isClosed_closedBall).mem_of_tendsto hζtend (Filter.Eventually.of_forall hζball')
    -- the subsequence still converges uniformly on that ball
    have hUC : TendstoUniformlyOn (fun k => v (φ (ψ k))) w atTop
        (Metric.closedBall (0 : WithLp 2 (F × ℝ)) (max 2 Rb)) := by
      have hbase := (hcau (max 2 Rb) hRb2).tendstoUniformlyOn_of_tendsto fun x _ => hw x
      intro u hu
      exact (hψmono.tendsto_atTop).eventually (hbase u hu)
    have hζnhds : Tendsto ζ atTop
        (𝓝[Metric.closedBall (0 : WithLp 2 (F × ℝ)) (max 2 Rb)] (z + toLp 2 (h, l))) :=
      tendsto_nhdsWithin_iff.mpr ⟨hζtend, Filter.Eventually.of_forall hζball'⟩
    have hvalζ : Tendsto (fun k => v (φ (ψ k)) (ζ k)) atTop (𝓝 (w (z + toLp 2 (h, l)))) :=
      hUC.tendsto_comp hwcont.continuousWithinAt hζnhds
    have hvalz : Tendsto (fun k => v (φ (ψ k)) z) atTop (𝓝 (w z)) :=
      (hw z).comp hψmono.tendsto_atTop
    have hinner : Tendsto (fun k => (inner ℝ (P (ψ k)).1 (hk k) : ℝ)) atTop
        (𝓝 (inner ℝ pa.1 h)) := by
      exact hPtend.inner hhktend
    have hnrm : Tendsto (fun k => ‖(P (ψ k)).1‖ ^ 2) atTop (𝓝 (‖pa.1‖ ^ 2)) :=
      ((continuous_norm.tendsto pa.1).comp hPtend).pow 2
    have hquad : Tendsto (fun k => ((P (ψ k)).2 - ‖(P (ψ k)).1‖ ^ 2 / 2) * l) atTop
        (𝓝 ((pa.2 - ‖pa.1‖ ^ 2 / 2) * l)) :=
      ((hPtend2.sub (hnrm.div_const 2))).mul_const l
    have hExpr : Tendsto (fun k => |v (φ (ψ k)) (ζ k) - v (φ (ψ k)) z
        - inner ℝ (P (ψ k)).1 (hk k)
        - ((P (ψ k)).2 - ‖(P (ψ k)).1‖ ^ 2 / 2) * l|) atTop
        (𝓝 |w (z + toLp 2 (h, l)) - w z - inner ℝ pa.1 h
          - (pa.2 - ‖pa.1‖ ^ 2 / 2) * l|) :=
      (((hvalζ.sub hvalz).sub hinner).sub hquad).abs
    have hbnd : ∀ k, |v (φ (ψ k)) (ζ k) - v (φ (ψ k)) z
        - inner ℝ (P (ψ k)).1 (hk k)
        - ((P (ψ k)).2 - ‖(P (ψ k)).1‖ ^ 2 / 2) * l| ≤ C₀ * R := by
      intro k
      rw [hζdef]
      exact hP (ψ k) (hk k) l hl (hkadm k)
    exact le_of_tendsto hExpr (Filter.Eventually.of_forall hbnd)
  -- ===== Step 6: `w` is centered at `zc` =====
  have hwcent : IsCenteredAt C₀ w zc := by
    refine ⟨?_, ?_⟩
    · have h2 : Tendsto (fun j => v (φ j) zc) atTop (𝓝 (w zc)) := hw zc
      have h4 : (fun j => v (φ j) zc) = fun _ : ℕ => (0 : ℝ) :=
        funext fun j => (hcent (φ j)).1
      rw [h4] at h2
      exact tendsto_nhds_unique h2 tendsto_const_nhds
    · intro hh l hl hhl
      have hbnd : ∀ j, |v (φ j) (zc + toLp 2 (hh, l)) - v (φ j) zc
          - inner ℝ (0 : F) hh - ((0 : ℝ) - ‖(0 : F)‖ ^ 2 / 2) * l| ≤ C₀ * 1 :=
        fun j => (hcent (φ j)).2 hh l hl hhl
      have hT : Tendsto (fun j => |v (φ j) (zc + toLp 2 (hh, l)) - v (φ j) zc
          - inner ℝ (0 : F) hh - ((0 : ℝ) - ‖(0 : F)‖ ^ 2 / 2) * l|) atTop
          (𝓝 |w (zc + toLp 2 (hh, l)) - w zc
            - inner ℝ (0 : F) hh - ((0 : ℝ) - ‖(0 : F)‖ ^ 2 / 2) * l|) :=
        ((((hw (zc + toLp 2 (hh, l))).sub (hw zc)).sub_const
          (inner ℝ (0 : F) hh : ℝ)).sub_const (((0 : ℝ) - ‖(0 : F)‖ ^ 2 / 2) * l)).abs
      exact le_of_tendsto hT (Filter.Eventually.of_forall hbnd)
  exact ⟨φ, w, hφmono, hconv, ⟨hwsol, hwfit⟩, hwcent⟩
