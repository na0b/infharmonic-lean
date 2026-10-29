module

public import InfHarmonic.Preamble

@[expose] public section
open Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Minty's characterization: `x₀` minimizes `x ↦ ψ x + ‖x - y‖² / 2` exactly
when `y - x₀` is a subgradient of `ψ` at `x₀`. -/
theorem MoreauProxSubgradient (ψ : E → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (y x₀ : E) :
    (∀ x : E, ψ x₀ + ‖x₀ - y‖ ^ 2 / 2 ≤ ψ x + ‖x - y‖ ^ 2 / 2) ↔
      (∀ x : E, ψ x₀ + inner ℝ (y - x₀) (x - x₀) ≤ ψ x) := by
  have hneg : x₀ - y = -(y - x₀) := by abel
  have hsign : ∀ a : E, inner ℝ (x₀ - y) a = - inner ℝ (y - x₀) a := by
    intro a
    rw [hneg, inner_neg_left]
  have hsign' : ∀ a : E, inner ℝ a (x₀ - y) = - inner ℝ (y - x₀) a := by
    intro a
    rw [real_inner_comm (x₀ - y) a, hsign a]
  have hexp : ∀ a b : E, ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 :=
    fun a b => norm_add_sq_real a b
  constructor
  · -- (1) implies (2): the perturbation x_t = x₀ + t (x - x₀)
    intro h1 x
    have hK : (0 : ℝ) ≤ ‖x - x₀‖ ^ 2 / 2 := by positivity
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
        ψ x₀ + inner ℝ (y - x₀) (x - x₀) ≤ ψ x + t * (‖x - x₀‖ ^ 2 / 2) := by
      intro t ht ht1
      have hconv : ψ ((1 - t) • x₀ + t • x) ≤ (1 - t) * ψ x₀ + t * ψ x :=
        hψ.2 (mem_univ x₀) (mem_univ x) (by linarith) ht.le (by ring)
      have hz : (1 - t) • x₀ + t • x - y = (x₀ - y) + t • (x - x₀) := by
        rw [sub_smul, one_smul, smul_sub]
        abel
      have hnorm : ‖(1 - t) • x₀ + t • x - y‖ ^ 2
          = ‖x₀ - y‖ ^ 2 - 2 * t * inner ℝ (y - x₀) (x - x₀)
            + t ^ 2 * ‖x - x₀‖ ^ 2 := by
        rw [hz, hexp, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
          abs_of_pos ht, hsign (x - x₀)]
        ring
      have h := h1 ((1 - t) • x₀ + t • x)
      rw [hnorm] at h
      have hmul : t * (ψ x₀ + inner ℝ (y - x₀) (x - x₀))
          ≤ t * (ψ x + t * (‖x - x₀‖ ^ 2 / 2)) := by nlinarith
      exact le_of_mul_le_mul_left hmul ht
    refine le_of_forall_sub_le ?_
    intro ε hε
    have hden : (0 : ℝ) < ‖x - x₀‖ ^ 2 / 2 + 1 := by linarith
    have ht0 : 0 < min 1 (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) :=
      lt_min one_pos (div_pos hε hden)
    have ht1 : min 1 (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) ≤ 1 := min_le_left _ _
    have htsmall : min 1 (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) * (‖x - x₀‖ ^ 2 / 2) ≤ ε := by
      have hle : min 1 (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) ≤ ε / (‖x - x₀‖ ^ 2 / 2 + 1) :=
        min_le_right _ _
      have hmul : min 1 (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) * (‖x - x₀‖ ^ 2 / 2)
          ≤ (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) * (‖x - x₀‖ ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hle hK
      have hfrac : (ε / (‖x - x₀‖ ^ 2 / 2 + 1)) * (‖x - x₀‖ ^ 2 / 2) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hden]
        nlinarith
      linarith
    linarith [key _ ht0 ht1]
  · -- (2) implies (1): expand the square and cancel the inner products
    intro h2 x
    have hnorm : ‖x - y‖ ^ 2
        = ‖x - x₀‖ ^ 2 - 2 * inner ℝ (y - x₀) (x - x₀) + ‖x₀ - y‖ ^ 2 := by
      have hz : x - y = (x - x₀) + (x₀ - y) := by abel
      rw [hz, hexp, hsign' (x - x₀)]
      ring
    have hx := h2 x
    have hK : (0 : ℝ) ≤ ‖x - x₀‖ ^ 2 / 2 := by positivity
    rw [hnorm]
    linarith
