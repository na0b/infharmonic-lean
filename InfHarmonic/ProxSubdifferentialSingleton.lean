module

public import InfHarmonic.IsMoreauProx
public import InfHarmonic.MoreauProxMonotone

@[expose] public section
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Step 4(a) of Alexandrov's theorem: above a point where the proximal map is
differentiable with invertible derivative, the subdifferential of `ψ` at `u y` is
the single point `y - u y`. -/
theorem ProxSubdifferentialSingleton (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E)
    (hu : IsMoreauProx ψ u) (y : E) (P : E →L[ℝ] E) (hP : HasFDerivAt u P y)
    (hdet : LinearMap.det (P : E →ₗ[ℝ] E) ≠ 0) (s : E)
    (hs : ∀ x : E, ψ (u y) + inner ℝ s (x - u y) ≤ ψ x) :
    s = y - u y := by
  obtain ⟨d, hd⟩ : ∃ d : E, d = s - (y - u y) := ⟨_, rfl⟩
  -- `y - u y` is itself a subgradient at `u y`, by Minty applied to `hu y`
  have hp : ∀ x : E, ψ (u y) + inner ℝ (y - u y) (x - u y) ≤ ψ x :=
    (MoreauProxSubgradient ψ hψ y (u y)).mp (hu y)
  -- every point of the segment from `y - u y` to `s` is a subgradient, so `u` is
  -- constant along the corresponding segment of base points
  have hconst : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → u (y + t • d) = u y := by
    intro t ht0 ht1
    have hseg : ∀ x : E, ψ (u y) + inner ℝ ((y + t • d) - u y) (x - u y) ≤ ψ x := by
      intro x
      have h1 := hs x
      have h2 := hp x
      have hrw : ((y + t • d) - u y) = (1 - t) • (y - u y) + t • s := by
        rw [hd]; module
      rw [hrw, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      nlinarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - t),
        mul_le_mul_of_nonneg_left h1 ht0]
    have hmin := (MoreauProxSubgradient ψ hψ (y + t • d) (u y)).mpr hseg
    have huniq := MoreauProxMonotone ψ hψ (y + t • d) (y + t • d) (u y) (u (y + t • d))
      hmin (hu (y + t • d))
    rw [show (y + t • d) - (y + t • d) = (0:E) by abel, norm_zero] at huniq
    have hz : ‖u y - u (y + t • d)‖ = 0 := by
      nlinarith [norm_nonneg (u y - u (y + t • d)),
        sq_nonneg ‖((y + t • d) - u y) - ((y + t • d) - u (y + t • d))‖]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  -- the derivative therefore kills `d`
  have hPd : P d = 0 := by
    have hc : Filter.Tendsto (fun n : ℕ => ‖(n : ℝ) + 1‖) Filter.atTop Filter.atTop := by
      have habs : ∀ n : ℕ, ‖(n : ℝ) + 1‖ = (n : ℝ) + 1 := by
        intro n; rw [Real.norm_eq_abs]; exact abs_of_nonneg (by positivity)
      simp only [habs]
      exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hlim := hP.lim d (c := fun n : ℕ => ((n : ℝ) + 1)) (l := Filter.atTop) hc
    have hzero : ∀ n : ℕ,
        ((n : ℝ) + 1) • (u (y + (((n : ℝ) + 1))⁻¹ • d) - u y) = (0 : E) := by
      intro n
      have hpos : (0:ℝ) < (n : ℝ) + 1 := by positivity
      have hn1 : (1:ℝ) ≤ (n : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) n; linarith
      have h2 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
        nlinarith [mul_inv_cancel₀ (ne_of_gt hpos), inv_pos.mpr hpos]
      rw [hconst _ (by positivity) h2, sub_self, smul_zero]
    simp only [hzero] at hlim
    exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm
  -- `det P ≠ 0` forces `d = 0`
  have hd0 : d = 0 := by
    by_contra hdne
    have hkb : LinearMap.ker (P : E →ₗ[ℝ] E) = ⊥ :=
      (LinearMap.isUnit_iff_ker_eq_bot _).mp
        ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet))
    have hmem : d ∈ LinearMap.ker (P : E →ₗ[ℝ] E) := LinearMap.mem_ker.mpr hPd
    rw [hkb, Submodule.mem_bot] at hmem
    exact hdne hmem
  have hfin : s - (y - u y) = 0 := by rw [← hd]; exact hd0
  exact sub_eq_zero.mp hfin
