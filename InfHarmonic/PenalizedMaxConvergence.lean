module

public import InfHarmonic.Preamble

@[expose] public section
open Set Filter Topology

/-- Penalization converges to the strict constrained maximum: if `Θ` has a strict
maximum at `k₀` among the points of the compact set `K` where the nonnegative penalty
`χ` vanishes, then maximizers of `Θ - λ χ` over `K` converge to `k₀` as `λ → ∞`. -/
theorem PenalizedMaxConvergence {Z : Type*} [MetricSpace Z]
    (K : Set Z) (hK : IsCompact K) (Θ χ : Z → ℝ)
    (hΘ : ContinuousOn Θ K) (hχ : ContinuousOn χ K) (hχ0 : ∀ k ∈ K, 0 ≤ χ k)
    (k₀ : Z) (hk₀ : k₀ ∈ K) (hχk₀ : χ k₀ = 0)
    (hstrict : ∀ k ∈ K, χ k = 0 → k ≠ k₀ → Θ k < Θ k₀)
    (lam : ℕ → ℝ) (hlam : ∀ m, 0 < lam m)
    (hlamtop : Tendsto lam atTop atTop)
    (ks : ℕ → Z) (hksK : ∀ m, ks m ∈ K)
    (hksmax : ∀ (m : ℕ), ∀ k ∈ K, Θ k - lam m * χ k ≤ Θ (ks m) - lam m * χ (ks m)) :
    Tendsto ks atTop (𝓝 k₀) := by
  obtain ⟨km, hkmK, hkmax⟩ := hK.exists_isMaxOn ⟨k₀, hk₀⟩ hΘ
  have hbase : ∀ m : ℕ, Θ k₀ ≤ Θ (ks m) - lam m * χ (ks m) := by
    intro m
    have h1 := hksmax m k₀ hk₀
    rwa [hχk₀, mul_zero, sub_zero] at h1
  have hΘge : ∀ m : ℕ, Θ k₀ ≤ Θ (ks m) := by
    intro m
    have h2 : 0 ≤ lam m * χ (ks m) := mul_nonneg (hlam m).le (hχ0 _ (hksK m))
    linarith [hbase m]
  have hpen : ∀ m : ℕ, lam m * χ (ks m) ≤ Θ km - Θ k₀ := by
    intro m
    have h3 : Θ (ks m) ≤ Θ km := hkmax (hksK m)
    linarith [hbase m]
  have hχto : Tendsto (fun m => χ (ks m)) atTop (𝓝 0) := by
    refine squeeze_zero (fun m => hχ0 _ (hksK m)) (fun m => ?_)
      (hlamtop.const_div_atTop (Θ km - Θ k₀))
    rw [le_div_iff₀ (hlam m)]
    linarith [hpen m]
  refine tendsto_of_subseq_tendsto (fun ns hns => ?_)
  obtain ⟨kh, hkhK, ms, hms, hconv⟩ := hK.tendsto_subseq (fun i => hksK (ns i))
  have hconv' : Tendsto (fun n => ks (ns (ms n))) atTop (𝓝 kh) := hconv
  have hidx : Tendsto (fun n => ns (ms n)) atTop atTop := hns.comp hms.tendsto_atTop
  have htw : Tendsto (fun n => ks (ns (ms n))) atTop (𝓝[K] kh) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hconv'
      (Eventually.of_forall (fun n => hksK _))
  -- the penalty vanishes in the limit, so `kh` lies on the zero set of χ
  have hχkh : χ kh = 0 := by
    have h1 : Tendsto (fun n => χ (ks (ns (ms n)))) atTop (𝓝 (χ kh)) :=
      ((hχ kh hkhK).tendsto).comp htw
    have h2 : Tendsto (fun n => χ (ks (ns (ms n)))) atTop (𝓝 0) := hχto.comp hidx
    exact tendsto_nhds_unique h1 h2
  -- and the value at `kh` is at least the value at `k₀`
  have hΘkh : Θ k₀ ≤ Θ kh := by
    have h1 : Tendsto (fun n => Θ (ks (ns (ms n)))) atTop (𝓝 (Θ kh)) :=
      ((hΘ kh hkhK).tendsto).comp htw
    refine ge_of_tendsto h1 ?_
    filter_upwards with n
    exact hΘge _
  have hkheq : kh = k₀ := by
    by_contra hne
    exact absurd (hstrict kh hkhK hχkh hne) (not_lt.mpr hΘkh)
  exact ⟨ms, hkheq ▸ hconv'⟩
