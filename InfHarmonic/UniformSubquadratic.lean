import InfHarmonic.CenteredGrowth
open Set WithLp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Equation (4.7): the centered members of `A_{m,C₀}` have subquadratic
spatial growth uniformly over the class, on every compact time interval. -/
theorem UniformSubquadratic (C₀ : ℝ) (hC₀ : 1 ≤ C₀) (zc : WithLp 2 (F × ℝ))
    (hzc : zc = 0 ∨ zc = toLp 2 ((0 : F), (1 : ℝ))) :
    ∀ J : Set ℝ, IsCompact J → ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧
      ∀ v : WithLp 2 (F × ℝ) → ℝ, IsFitClass C₀ v → IsCenteredAt C₀ v zc →
        ∀ z : WithLp 2 (F × ℝ), M ≤ ‖(ofLp z).1‖ → (ofLp z).2 ∈ J →
          |v z| ≤ ε * ‖(ofLp z).1‖ ^ 2 := by
  -- The growth constant of `CenteredGrowth`, fixed before `J` and `ε`.
  obtain ⟨C, hC0, hCG⟩ := CenteredGrowth (F := F) C₀ hC₀
  intro J hJ ε hε
  -- `J` compact ⇒ bounded: a time radius `T ≥ 2` containing `J`.
  obtain ⟨rJ, hrJ⟩ := hJ.isBounded.subset_closedBall (0 : ℝ)
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = max rJ 2 := ⟨_, rfl⟩
  have hT2 : (2:ℝ) ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hTJ : ∀ t ∈ J, |t| ≤ T := by
    intro t ht
    have h := hrJ ht
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
    exact h.trans (by rw [hTdef]; exact le_max_left _ _)
  -- The analytic radius, through the substitution `K = u⁴`: `(1 + log K)² ≤ 9 + 24u`
  -- and `ε K = ε u²` beats `9C + 24Cu` as soon as `ε u ≥ 48 C`.
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = max 1 (48 * C / ε) := ⟨_, rfl⟩
  have hU1 : (1:ℝ) ≤ U := by rw [hUdef]; exact le_max_left _ _
  have hU0 : (0:ℝ) < U := by linarith
  have hUkey : 48 * C ≤ ε * U := by
    have h : 48 * C / ε ≤ U := by rw [hUdef]; exact le_max_right _ _
    rw [div_le_iff₀ hε] at h
    linarith
  refine ⟨max T (U ^ 2), lt_of_lt_of_le (by linarith : (0:ℝ) < T) (le_max_left _ _), ?_⟩
  intro v hv hcen z hzM hzJ
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ‖(ofLp z).1‖ := ⟨_, rfl⟩
  rw [← hKdef] at hzM ⊢
  have hK2 : (2:ℝ) ≤ K := hT2.trans ((le_max_left T (U ^ 2)).trans hzM)
  have hK0 : (0:ℝ) < K := by linarith
  -- `hzc` names one of the two admissible centers, which is exactly the
  -- disjunctive centering hypothesis of `CenteredGrowth`.
  have hcen' : IsCenteredAt C₀ v 0 ∨ IsCenteredAt C₀ v (toLp 2 ((0 : F), (1 : ℝ))) := by
    rcases hzc with h | h
    · rw [h] at hcen; exact Or.inl hcen
    · rw [h] at hcen; exact Or.inr hcen
  have hbox1 : ‖(ofLp z).1‖ ≤ K := hKdef.ge
  have hbox2 : |(ofLp z).2| ≤ K :=
    (hTJ _ hzJ).trans ((le_max_left T (U ^ 2)).trans hzM)
  have hgrow := hCG v hv hcen' K hK2 z hbox1 hbox2
  -- The one analytic step, elementary: `log K = 4 log s` with `s⁴ = K`, and
  -- `log s ≤ s - 1`, so `log K ≤ 4s` and `(log K)² ≤ 16 s² = 16 u`.
  obtain ⟨u, hudef⟩ : ∃ u : ℝ, u = Real.sqrt K := ⟨_, rfl⟩
  have hu0 : (0:ℝ) < u := by rw [hudef]; exact Real.sqrt_pos.mpr hK0
  have husq : u ^ 2 = K := by rw [hudef]; exact Real.sq_sqrt hK0.le
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = Real.sqrt u := ⟨_, rfl⟩
  have hs0 : (0:ℝ) < s := by rw [hsdef]; exact Real.sqrt_pos.mpr hu0
  have hssq : s ^ 2 = u := by rw [hsdef]; exact Real.sq_sqrt hu0.le
  have hs4 : s ^ 4 = K := by
    have h : s ^ 4 = (s ^ 2) ^ 2 := by ring
    rw [h, hssq, husq]
  have hlogKs : Real.log K = 4 * Real.log s := by
    rw [← hs4, Real.log_pow]; norm_num
  have hlogK4 : Real.log K ≤ 4 * s := by
    rw [hlogKs]; linarith [Real.log_le_sub_one_of_pos hs0]
  have hlogK0 : 0 ≤ Real.log K := Real.log_nonneg (by linarith)
  have hsq : Real.log K ^ 2 ≤ 16 * u := by
    calc Real.log K ^ 2 ≤ (4 * s) ^ 2 := sq_le_sq' (by linarith) hlogK4
      _ = 16 * s ^ 2 := by ring
      _ = 16 * u := by rw [hssq]
  have hsu : s ≤ 1 + u := by
    rw [← hssq]; nlinarith [sq_nonneg (s - 1), hs0.le]
  have hbig : (1 + Real.log K) ^ 2 ≤ 9 + 24 * u := by
    nlinarith [hlogK4, hsq, hsu]
  -- `u ≥ U`, from `K ≥ U²`
  have huU : U ≤ u := by
    have hKU : U ^ 2 ≤ K := (le_max_right T (U ^ 2)).trans hzM
    rw [hudef]
    calc U = Real.sqrt (U ^ 2) := (Real.sqrt_sq hU0.le).symm
      _ ≤ Real.sqrt K := Real.sqrt_le_sqrt hKU
  have hu1 : (1:ℝ) ≤ u := hU1.trans huU
  have hεU : 48 * C ≤ ε * u := hUkey.trans (mul_le_mul_of_nonneg_left huU hε.le)
  have h9 : 9 * C ≤ 24 * C * u := by
    nlinarith [mul_nonneg hC0.le (by linarith : (0:ℝ) ≤ u - 1), hC0.le]
  have hfin : C * (1 + Real.log K) ^ 2 ≤ ε * K := by
    calc C * (1 + Real.log K) ^ 2 ≤ C * (9 + 24 * u) :=
          mul_le_mul_of_nonneg_left hbig hC0.le
      _ = 9 * C + 24 * C * u := by ring
      _ ≤ 24 * C * u + 24 * C * u := by linarith
      _ = 48 * C * u := by ring
      _ ≤ ε * u * u := mul_le_mul_of_nonneg_right hεU hu0.le
      _ = ε * u ^ 2 := by ring
      _ = ε * K := by rw [husq]
  calc |v z| ≤ C * K * (1 + Real.log K) ^ 2 := hgrow
    _ = C * (1 + Real.log K) ^ 2 * K := by ring
    _ ≤ ε * K * K := mul_le_mul_of_nonneg_right hfin hK0.le
    _ = ε * K ^ 2 := by ring
