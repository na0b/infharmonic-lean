import InfHarmonic.IsMoreauProx
import InfHarmonic.MoreauProxMonotone
open Set MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Wherever the convex function `ψ` is differentiable, the point is in the range
of the proximal map: `x = u (x + ∇ψ x)`. -/
theorem ProxHitsGradientPoints (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (u : E → E)
    (hu : IsMoreauProx ψ u) (x q : E) (hq : HasGradientAt ψ q x) :
    u (x + q) = x := by
  -- Body-only acknowledgement (trap 2): the instance bundle is part of this node's protected
  -- signature; the route below consumes finite-dimensionality only through its dependencies.
  have _ : FiniteDimensional ℝ E := inferInstance
  -- STEP 1: THE GRADIENT IS A SUBGRADIENT.  The .tex passes to the limit t ↓ 0 in the convexity
  -- difference quotient; in Lean the same content is an ε-argument: for every ε > 0 pick ONE
  -- admissible t, so the limit is replaced by `le_of_forall_pos_le_add`.
  have hsub : ∀ x' : E, ψ x + inner ℝ q (x' - x) ≤ ψ x' := by
    intro x'
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    -- the little-o window of the gradient, at the scale c = ε / (‖x' - x‖ + 1)
    obtain ⟨c, hc⟩ : ∃ t : ℝ, t = ε / (‖x' - x‖ + 1) := ⟨_, rfl⟩
    have hd : (0:ℝ) < ‖x' - x‖ + 1 := by positivity
    have hcpos : 0 < c := by rw [hc]; exact div_pos hε hd
    have hcb : c * ‖x' - x‖ ≤ ε := by
      rw [hc, div_mul_eq_mul_div, div_le_iff₀ hd]
      nlinarith [norm_nonneg (x' - x), hε.le]
    have hlo := (hasGradientAt_iff_isLittleO.mp hq)
    rw [Asymptotics.isLittleO_iff] at hlo
    have hwin := hlo hcpos
    rw [Metric.eventually_nhds_iff] at hwin
    obtain ⟨ρ, hρ, hball⟩ := hwin
    -- one admissible step size: t ≤ 1 and t ‖x' - x‖ < ρ
    obtain ⟨t, ht⟩ : ∃ s : ℝ, s = min 1 (ρ / (2 * (‖x' - x‖ + 1))) := ⟨_, rfl⟩
    have htpos : 0 < t := by
      rw [ht]
      exact lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := by rw [ht]; exact min_le_left _ _
    have htsmall : t * ‖x' - x‖ < ρ := by
      have h2 : t ≤ ρ / (2 * (‖x' - x‖ + 1)) := by rw [ht]; exact min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h2
      nlinarith [norm_nonneg (x' - x), htpos, hρ]
    -- convexity at the interpolated point
    have hpt : (1 - t) • x + t • x' = x + t • (x' - x) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    have hconv0 : ψ ((1 - t) • x + t • x') ≤ (1 - t) * ψ x + t * ψ x' :=
      hψ.2 (mem_univ x) (mem_univ x') (by linarith) htpos.le (by ring)
    rw [hpt] at hconv0
    -- the little-o bound at the point x + t (x' - x)
    have hzx : x + t • (x' - x) - x = t • (x' - x) := by abel
    have hmem : dist (x + t • (x' - x)) x < ρ := by
      rw [dist_eq_norm, hzx, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
      exact htsmall
    have hb := hball hmem
    rw [hzx, norm_smul, show ‖t‖ = t by rw [Real.norm_eq_abs, abs_of_pos htpos],
      real_inner_smul_right, Real.norm_eq_abs] at hb
    have hb' := (abs_le.mp hb).1
    -- divide the resulting inequality by t > 0
    have hfin : t * inner ℝ q (x' - x) ≤ t * (ψ x' - ψ x) + c * (t * ‖x' - x‖) := by
      linarith only [hb', hconv0]
    have hkey : inner ℝ q (x' - x) ≤ (ψ x' - ψ x) + c * ‖x' - x‖ := by
      refine le_of_mul_le_mul_left ?_ htpos
      calc t * inner ℝ q (x' - x) ≤ t * (ψ x' - ψ x) + c * (t * ‖x' - x‖) := hfin
        _ = t * ((ψ x' - ψ x) + c * ‖x' - x‖) := by ring
    linarith only [hkey, hcb]
  -- STEP 2: MINTY.  With y = x + q, `hsub` is exactly the right-hand clause of
  -- MoreauProxSubgradient at this base point, so the left-hand clause holds: `x` minimizes
  -- x' ↦ ψ x' + ‖x' - y‖² / 2 over E.
  have hmin : ∀ x' : E, ψ x + ‖x - (x + q)‖ ^ 2 / 2 ≤ ψ x' + ‖x' - (x + q)‖ ^ 2 / 2 := by
    refine (MoreauProxSubgradient ψ hψ (x + q) x).mpr ?_
    intro x'
    have h := hsub x'
    rwa [show x + q - x = q by abel]
  -- STEP 3: UNIQUENESS OF THE MINIMIZER, via firm nonexpansiveness at y₁ = y₂ = x + q.
  have hmono := MoreauProxMonotone ψ hψ (x + q) (x + q) x (u (x + q)) hmin (hu (x + q))
  rw [show ‖(x + q) - (x + q)‖ ^ 2 = 0 by simp] at hmono
  have hns : ‖x - u (x + q)‖ = 0 := by
    have hq2 : ‖x - u (x + q)‖ ^ 2 ≤ 0 := by
      linarith only [hmono, sq_nonneg ‖((x + q) - x) - ((x + q) - u (x + q))‖]
    have hnn := norm_nonneg (x - u (x + q))
    nlinarith only [hq2, hnn]
  have := sub_eq_zero.mp (norm_eq_zero.mp hns)
  exact this.symm
