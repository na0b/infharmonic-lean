module

public import InfHarmonic.BadScales
public import InfHarmonic.NonaffineLimit
public import InfHarmonic.Liouville

@[expose] public section
open Set Metric Filter Topology WithLp

/-- Proposition 3.2 (uniform power decay): the family flatness modulus obeys a
power bound `b_d(s) ≤ B s^γ` on an interval `(0, s₀]`, with `B`, `γ ≤ 1` and
`s₀ ≤ 1/8` depending only on `d`. -/
theorem PowerDecay (d : ℕ) (hd : 1 ≤ d) :
    ∃ B γ s₀ : ℝ, 0 < B ∧ 0 < γ ∧ γ ≤ 1 ∧ 0 < s₀ ∧ s₀ ≤ 1 / 8 ∧
      ∀ s : ℝ, 0 < s → s ≤ s₀ → FlatnessModulus d hd s ≤ B * s ^ γ := by
  -- ===================================================================
  -- This node is PURE COMPOSITION: `BadScales` once, `NonaffineLimit` once,
  -- `Liouville` once, and Mathlib's `Submodule.reflection_sub` once.  Nothing here is an
  -- analysis step, and the two things the paper says in passing cost nothing in Lean:
  -- "reducing the exponent gives γ ≤ 1" is absorbed because `γ ≤ 1` sits in BOTH the goal
  -- and `BadScales`'s hypothesis, so the contradiction never leaves that range; and "the
  -- constants depend only on `d`" is automatic, because the existential is under `(d) (hd)`
  -- with nothing else in scope.
  --
  -- THE ONE INTERFACE SHAPE WORTH KNOWING: `NonaffineLimit` takes `P`, `Φ` and `v` as
  -- TOTAL functions on ℕ with hypotheses only for `i ≥ i₁`.  Stating each family as
  -- `∀ i, ∃ x, i₁ ≤ i → …` -- trivially satisfiable below `i₁` by any value -- and then
  -- `choose` avoids fighting the choice principle, and the dummy below `i₁` is never used.
  -- ===================================================================
  by_contra hcon
  push Not at hcon
  -- ===================== STEP 1: THE NEGATION IS `BadScales`' HYPOTHESIS =======
  -- `push_neg` turns each `¬(A ∧ B)` into `A → ¬B` and flips the final `≤` into the
  -- strict `<` in the direction `hfail` wants.  Only the binder GROUPING differs, so the
  -- re-statement below is `intro` followed by `exact`.
  have hfail : ∀ B : ℝ, 0 < B → ∀ γ : ℝ, 0 < γ → γ ≤ 1 → ∀ s₀ : ℝ, 0 < s₀ → s₀ ≤ 1 / 8 →
      ∃ s : ℝ, 0 < s ∧ s ≤ s₀ ∧ B * s ^ γ < FlatnessModulus d hd s := by
    intro B hB gm hgm0 hgm1 s₀ hs₀0 hs₀1
    exact hcon B gm s₀ hB hgm0 hgm1 hs₀0 hs₀1
  obtain ⟨gam, sq, r, lam, U, z, hdata⟩ := BadScales d hd hfail
  have hdat := hdata
  obtain ⟨hgam0, hgamlim, hs0, hslim, hlam0, hlamlim, hUnorm, hzG, hr0, hrle,
    hbad, hgood⟩ := hdat
  -- ===================== STEP 2: THE SLOPES `P_i` AND THE INDEX `i₁` ==========
  -- `hgood` at `M = 2` is admissible since `2 ≤ 2`; at `w = z i` the displacement is `0`
  -- and at `ρ = r i` the radius is `≤ 2 r i`, both by `r i > 0`.
  obtain ⟨i₁, hi₁⟩ := hgood 2 (le_refl 2)
  obtain ⟨eb, hebdef⟩ : ∃ eb : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      eb = toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) := ⟨_, rfl⟩
  have hebn : ‖eb‖ = 1 := by
    rw [hebdef]
    have hsq := WithLp.prod_norm_sq_eq_of_L2
      (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    have h1 : ‖(toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).fst‖ = 0 := by
      show ‖(0 : EuclideanSpace ℝ (Fin d))‖ = 0
      exact norm_zero
    have h2 : ‖(toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))
        : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)).snd‖ = 1 := by
      show ‖(1 : ℝ)‖ = 1
      exact norm_one
    rw [h1, h2] at hsq
    have hnn := norm_nonneg (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))
      : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    nlinarith only [hsq, hnn]
  have hPex : ∀ i : ℕ, ∃ Pi : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      i₁ ≤ i → IsCylinderFit (U i) (z i) (r i) (32 * lam i) Pi := by
    intro i
    by_cases hi : i₁ ≤ i
    · have hd0 : ‖z i - z i‖ ≤ 2 * r i := by
        rw [sub_self, norm_zero]
        linarith only [hr0 i]
      obtain ⟨-, -, Pi, hPfit⟩ :=
        hi₁ i hi (z i) hd0 (r i) (hr0 i) (by linarith only [hr0 i])
      exact ⟨Pi, fun _ => hPfit⟩
    · exact ⟨eb, fun h => absurd h hi⟩
  choose P hP using hPex
  have hcc0 : ∀ i ≥ i₁, (0 : ℝ) < ‖P i‖ := fun i hi => norm_pos_iff.mpr (hP i hi).1
  -- ===================== STEP 3: THE ANISOTROPIC FRAME `Φ_i` ==================
  -- The .tex builds the reflection by hand and verifies linearity, isometry, involution
  -- and `Φ_i(e_b) = w_i`.  In Lean that whole construction is ONE Mathlib citation:
  -- `Submodule.reflection (ℝ ∙ (e_b - w_i))ᗮ` is already a `≃ₗᵢ[ℝ]`, which is the type of
  -- `NonaffineLimit`'s `Φ` slot, and `Submodule.reflection_sub` sends its FIRST argument
  -- to its second given only that the two have equal norms.  The .tex's case split on
  -- `w_i = e_b` is not needed: there `ℝ ∙ 0 = ⊥`, its orthogonal complement is `⊤`, and
  -- the reflection is the identity, so the single formula covers that branch too.
  have hΦex : ∀ i : ℕ, ∃ Ψ : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)
        ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      i₁ ≤ i → Ψ (toLp 2 ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ))) = ‖P i‖⁻¹ • P i := by
    intro i
    by_cases hi : i₁ ≤ i
    · have hc0 : (0 : ℝ) < ‖P i‖ := hcc0 i hi
      have hwn : ‖‖P i‖⁻¹ • P i‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt (inv_pos.mpr hc0)),
          inv_mul_cancel₀ (ne_of_gt hc0)]
      refine ⟨Submodule.reflection (Submodule.span ℝ {eb - ‖P i‖⁻¹ • P i})ᗮ, fun _ => ?_⟩
      rw [← hebdef]
      exact Submodule.reflection_sub (by rw [hebn, hwn])
    · exact ⟨LinearIsometryEquiv.refl ℝ _, fun h => absurd h hi⟩
  choose Φ hΦ using hΦex
  -- ===================== STEP 4: THE NORMALIZED FUNCTIONS `v_i` ===============
  -- eq:pd-vdef, solved for `v_i`.  `r_i`, `c_i` and `λ_i` are all positive for `i ≥ i₁`,
  -- so the division is legitimate and eq:pd-normalization follows by clearing it.
  obtain ⟨vv, hvvdef⟩ : ∃ vv : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ,
      vv = fun i w => (1 / lam i) *
        ((U i (z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))
          - U i (z i)) / (r i * ‖P i‖) - (ofLp w).2) := ⟨_, rfl⟩
  have hvv : ∀ i ≥ i₁, ∀ w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
      U i (z i + r i • Φ i (toLp 2 (Real.sqrt (lam i) • (ofLp w).1, (ofLp w).2)))
        = U i (z i) + r i * ‖P i‖ * ((ofLp w).2 + lam i * vv i w) := by
    intro i hi w
    have hc0 : (0 : ℝ) < ‖P i‖ := hcc0 i hi
    have hr : (0 : ℝ) < r i := hr0 i
    have hl : (0 : ℝ) < lam i := hlam0 i
    have hlne : lam i ≠ 0 := ne_of_gt hl
    have hrcne : r i * ‖P i‖ ≠ 0 := ne_of_gt (mul_pos hr hc0)
    rw [hvvdef]
    field_simp
    ring
  -- ===================== STEP 5: THE NONAFFINE ENTIRE SOLUTION ================
  obtain ⟨C₀, psi, vlim, hC₀, hpsimono, hpsige, hvcont, hvconv, hfitcl, hnonaff⟩ :=
    NonaffineLimit d hd gam sq r lam U z hdata i₁ P hP Φ hΦ vv hvv
  -- ===================== STEP 6: THE CONTRADICTION ============================
  -- `Liouville` carries no dimension slot: the paper's `m = d` is just the instantiation
  -- `F = EuclideanSpace ℝ (Fin d)`, and `C₀` is a plain parameter taking the `256` that
  -- `NonaffineLimit` returns, with `0 ≤ C₀` its first returned conjunct and
  -- `IsFitClass C₀ vlim` its sixth.
  exact hnonaff (Liouville C₀ hC₀ vlim hfitcl)
