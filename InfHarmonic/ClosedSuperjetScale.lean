module

public import InfHarmonic.ClosedSuperjet

@[expose] public section
set_option linter.unusedSectionVars false
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Rescaling a function by a positive constant rescales its closed superjets by the
same constant: `(p, X)` is a closed superjet of `θ • g` at `z` exactly when
`(θ⁻¹ • p, θ⁻¹ • X)` is one of `g` at `z`. -/
theorem ClosedSuperjetScale (θ : ℝ) (hθ : 0 < θ) (g : E → ℝ) (z p : E)
    (X : E →L[ℝ] E →L[ℝ] ℝ) :
    (p, X) ∈ ClosedSuperjet (fun w => θ * g w) z ↔
      (θ⁻¹ • p, θ⁻¹ • X) ∈ ClosedSuperjet g z := by
  -- one direction, proved once and applied twice
  have key : ∀ (c : ℝ), 0 < c → ∀ (h : E → ℝ) (p' : E) (X' : E →L[ℝ] E →L[ℝ] ℝ),
      (p', X') ∈ ClosedSuperjet h z → (c • p', c • X') ∈ ClosedSuperjet (fun w => c * h w) z := by
    intro c hc h p' X' hmem
    obtain ⟨zs, ps, Xs, hjet, hz, hgz, hp, hX⟩ := hmem
    refine ⟨zs, fun k => c • ps k, fun k => c • Xs k, ?_, hz, ?_, ?_, ?_⟩
    · intro k
      obtain ⟨hsym, hineq⟩ := hjet k
      constructor
      · intro a b
        -- the pair's projections are not beta-reduced in the goal; a `show` is the bridge
        show (c • Xs k) a b = (c • Xs k) b a
        simp only [smul_apply, smul_eq_mul]
        rw [hsym a b]
      · intro ε hε
        obtain ⟨δ, hδ, hball⟩ := hineq (ε / c) (by positivity)
        refine ⟨δ, hδ, fun u hu => ?_⟩
        show c * h (zs k + u) ≤ c * h (zs k) + inner ℝ (c • ps k) u
          + (c • Xs k) u u / 2 + ε * ‖u‖ ^ 2
        have h1 := hball u hu
        have h2 : (inner ℝ (c • ps k) u : ℝ) = c * inner ℝ (ps k) u :=
          real_inner_smul_left (ps k) u c
        have h3 : (c • Xs k) u u = c * Xs k u u := by
          simp only [smul_apply, smul_eq_mul]
        rw [h2, h3]
        have h4 : ε / c * ‖u‖ ^ 2 * c = ε * ‖u‖ ^ 2 := by field_simp
        nlinarith [h1, hc]
    · exact hgz.const_mul c
    · exact hp.const_smul c
    · exact hX.const_smul c
  constructor
  · intro hmem
    have h1 := key θ⁻¹ (by positivity) (fun w => θ * g w) p X hmem
    have h2 : (fun w => θ⁻¹ * (θ * g w)) = g := by
      funext w; field_simp
    rwa [h2] at h1
  · intro hmem
    have h1 := key θ hθ g (θ⁻¹ • p) (θ⁻¹ • X) hmem
    have hne : θ ≠ 0 := ne_of_gt hθ
    have h2 : θ • (θ⁻¹ • p) = p := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    have h3 : θ • (θ⁻¹ • X) = X := by
      rw [smul_smul, mul_inv_cancel₀ hne, one_smul]
    rwa [h2, h3] at h1
