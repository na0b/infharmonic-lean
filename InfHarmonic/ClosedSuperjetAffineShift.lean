import InfHarmonic.ClosedSuperjet
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Part I(C) of the theorem of sums: translating the base point to `0` and
subtracting the affine function `w ↦ g z + ⟪p, w⟫` shifts the closed superjet by
exactly `p` in the gradient slot and leaves the Hessian slot alone. -/
theorem ClosedSuperjetAffineShift (g : E → ℝ) (z p q : E) (X : E →L[ℝ] E →L[ℝ] ℝ) :
    (q, X) ∈ ClosedSuperjet (fun w : E => g (z + w) - g z - inner ℝ p w) 0 ↔
      (q + p, X) ∈ ClosedSuperjet g z := by
  -- Body-only acknowledgement (trap 2): the instance bundle is part of this node's protected
  -- signature; the route below uses finite-dimensionality only through `ClosedSuperjet` itself.
  have _ : FiniteDimensional ℝ E := inferInstance
  have hc : Continuous fun w : E => (inner ℝ p w : ℝ) :=
    (continuous_const (y := p)).inner continuous_id
  have hg0 : (fun w : E => g (z + w) - g z - inner ℝ p w) 0 = 0 := by simp
  -- STEP 1: the pointwise equivalence of superjets, at an ARBITRARY base point.  Both sides
  -- impose the same symmetry condition on the Hessian slot, and the two inequalities differ by
  -- the affine terms, which cancel: -⟪p, w₀ + h⟫ + ⟪p, w₀⟫ = -⟪p, h⟫.
  have key : ∀ (w₀ q' : E) (Y : E →L[ℝ] E →L[ℝ] ℝ),
      (q', Y) ∈ Superjet (fun w : E => g (z + w) - g z - inner ℝ p w) w₀ ↔
        (q' + p, Y) ∈ Superjet g (z + w₀) := by
    intro w₀ q' Y
    constructor
    · rintro ⟨hsym, hineq⟩
      refine ⟨hsym, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hball⟩ := hineq ε hε
      refine ⟨δ, hδ, fun h hh => ?_⟩
      -- the hypothesis, written out with the lambda applied
      have hb : g (z + (w₀ + h)) - g z - inner ℝ p (w₀ + h)
          ≤ (g (z + w₀) - g z - inner ℝ p w₀) + inner ℝ q' h + Y h h / 2 + ε * ‖h‖ ^ 2 :=
        hball h hh
      rw [show z + (w₀ + h) = z + w₀ + h from by abel,
        show (inner ℝ p (w₀ + h) : ℝ) = inner ℝ p w₀ + inner ℝ p h from by
          rw [inner_add_right]] at hb
      show g (z + w₀ + h) ≤ g (z + w₀) + inner ℝ (q' + p) h + Y h h / 2 + ε * ‖h‖ ^ 2
      rw [show (inner ℝ (q' + p) h : ℝ) = inner ℝ q' h + inner ℝ p h from by rw [inner_add_left]]
      linarith
    · rintro ⟨hsym, hineq⟩
      refine ⟨hsym, fun ε hε => ?_⟩
      obtain ⟨δ, hδ, hball⟩ := hineq ε hε
      refine ⟨δ, hδ, fun h hh => ?_⟩
      have hb : g (z + w₀ + h)
          ≤ g (z + w₀) + inner ℝ (q' + p) h + Y h h / 2 + ε * ‖h‖ ^ 2 := hball h hh
      rw [show (inner ℝ (q' + p) h : ℝ) = inner ℝ q' h + inner ℝ p h from by
        rw [inner_add_left]] at hb
      show g (z + (w₀ + h)) - g z - inner ℝ p (w₀ + h)
          ≤ (g (z + w₀) - g z - inner ℝ p w₀) + inner ℝ q' h + Y h h / 2 + ε * ‖h‖ ^ 2
      rw [show z + (w₀ + h) = z + w₀ + h from by abel,
        show (inner ℝ p (w₀ + h) : ℝ) = inner ℝ p w₀ + inner ℝ p h from by
          rw [inner_add_right]]
      linarith
  constructor
  · -- STEP 2: translating the defining sequences forward
    rintro ⟨ws, qs, Xs, hjet, hw, hgw, hq, hX⟩
    rw [hg0] at hgw
    refine ⟨fun k => z + ws k, fun k => qs k + p, Xs, fun k => ?_, ?_, ?_, ?_, hX⟩
    · exact (key (ws k) (qs k) (Xs k)).mp (hjet k)
    · have h1 := (tendsto_const_nhds (x := z) (f := Filter.atTop (α := ℕ))).add hw
      rw [add_zero] at h1
      exact h1
    · have hip : Filter.Tendsto (fun k => (inner ℝ p (ws k) : ℝ)) Filter.atTop (nhds 0) := by
        have h2 := (hc.tendsto (0 : E)).comp hw
        rw [inner_zero_right p] at h2
        exact h2
      have heq : (fun k => g (z + ws k)) = fun k =>
          (g (z + ws k) - g z - inner ℝ p (ws k)) + g z + inner ℝ p (ws k) := by
        funext k; ring
      rw [heq]
      have hfin := (hgw.add (tendsto_const_nhds (x := g z))).add hip
      rw [show (0:ℝ) + g z + 0 = g z from by ring] at hfin
      exact hfin
    · have h1 := hq.add (tendsto_const_nhds (x := p))
      exact h1
  · -- STEP 3: translating the defining sequences backward
    rintro ⟨zs, πs, Xs, hjet, hzs, hgz, hπ, hX⟩
    have hsub : Filter.Tendsto (fun k => zs k - z) Filter.atTop (nhds (0 : E)) := by
      have h1 := hzs.sub (tendsto_const_nhds (x := z))
      rw [sub_self] at h1
      exact h1
    refine ⟨fun k => zs k - z, fun k => πs k - p, Xs, fun k => ?_, hsub, ?_, ?_, hX⟩
    · have h1 : z + (zs k - z) = zs k := by abel
      have h2 : (πs k - p) + p = πs k := by abel
      have h3 := key (zs k - z) (πs k - p) (Xs k)
      rw [h1, h2] at h3
      exact h3.mpr (hjet k)
    · rw [hg0]
      have hip : Filter.Tendsto (fun k => (inner ℝ p (zs k - z) : ℝ)) Filter.atTop (nhds 0) := by
        have h2 := (hc.tendsto (0 : E)).comp hsub
        rw [inner_zero_right p] at h2
        exact h2
      have heq : (fun k => g (z + (zs k - z)) - g z - inner ℝ p (zs k - z))
          = fun k => g (zs k) - g z - inner ℝ p (zs k - z) := by
        funext k
        rw [show z + (zs k - z) = zs k from by abel]
      rw [heq]
      have hfin := (hgz.sub (tendsto_const_nhds (x := g z))).sub hip
      rw [show g z - g z - (0:ℝ) = 0 from by ring] at hfin
      exact hfin
    · have h1 := hπ.sub (tendsto_const_nhds (x := p))
      rw [show q + p - p = q from by abel] at h1
      exact h1
