import InfHarmonic.BilinearFormBolzanoWeierstrass
import InfHarmonic.ClosedSuperjetLocal
import InfHarmonic.ClosedSuperjetQuartic
import InfHarmonic.ClosedSuperjetAffineShift
import InfHarmonic.SumRuleQuadraticTest
import InfHarmonic.SumRuleResolvent
import InfHarmonic.SumRuleDualityTest
import InfHarmonic.SumRuleJetFromJensen
open Set MeasureTheory Metric
open scoped Gradient
open WithLp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- Part V(1)-(2) of the theorem of sums: for a FIXED regularization parameter
`τ > 0` the jets produced by Part IV at shrinking radii converge, along a
subsequence, to closed superjets of the original `g j` at the original base
points, whose Hessians obey the matrix inequality for the PERTURBED form
`D²Ψ + τ id` and are bounded in norm by a single constant `Lam`, chosen before
`τ` and therefore independent of it.  That `τ`-free bound is what makes the final
limit `τ ↓ 0` possible. -/
theorem SumRuleFixedTauJets (N : ℕ) (hN : 0 < N) (O : Fin N → Set E)
    (hO : ∀ j, IsOpen (O j)) (g : Fin N → E → ℝ) (hg : ∀ j, ContinuousOn (g j) (O j))
    (Ψ : PiLp 2 (fun _ : Fin N => E) → ℝ) (Z : PiLp 2 (fun _ : Fin N => E))
    (hZ : ∀ j, ofLp Z j ∈ O j) (hΨ : ContDiffAt ℝ 2 Ψ Z)
    (hmax : IsLocalMax (fun Y : PiLp 2 (fun _ : Fin N => E) =>
      (∑ j, g j (ofLp Y j)) - Ψ Y) Z)
    (η : ℝ) (hη : 0 < η) :
    ∃ Lam : ℝ, 0 ≤ Lam ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∃ X : Fin N → (E →L[ℝ] E →L[ℝ] ℝ),
        (∀ j, ∀ a b : E, X j a b = X j b a) ∧
        (∀ j, ‖X j‖ ≤ Lam) ∧
        (∀ j, ((ofLp (∇ Ψ Z) j), X j) ∈ ClosedSuperjet (g j) (ofLp Z j)) ∧
        (∀ ζ : PiLp 2 (fun _ : Fin N => E),
          (∑ j, X j (ofLp ζ j) (ofLp ζ j))
            ≤ ((fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ + τ * ‖ζ‖ ^ 2)
              + η * ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ + τ • innerSL ℝ ζ‖ ^ 2) := by
  classical
  -- DURABLE ROUTE NOTES (burst 405, closure burst).  Three places where the Lean needs a bridge
  -- the .tex does not spell out; the .tex route is correct and is deliberately left untouched
  -- (this burst is `local`, so aligning it would only re-fingerprint a SOUND proof).
  --   * THE RIESZ BRIDGE, WHICH IS THE ONE REAL INTERFACE STEP.  The statement's (T3) carries
  --     `‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ + τ • innerSL ℝ ζ‖`, the norm of the FUNCTIONAL
  --     `ξ ↦ A(ζ,ξ) + τ⟪ζ,ξ⟫` in `V →L[ℝ] ℝ`, while `SumRuleResolvent`'s (R6) carries
  --     `‖B ζ‖`, the norm of the VECTOR `B_τ ζ ∈ V`.  They agree because `innerSL` is an
  --     isometry: `hBtvec` below proves `innerSL ℝ (Bt ζ)` IS that functional (by `ext`) and
  --     then transports the norm across `innerSL_apply_norm`.  Without that step the final
  --     `linarith` has two unrelated atoms.
  --   * `Abar` IS BUILT BY `InnerProductSpace.continuousLinearMapOfBilin`, not by hand: it
  --     turns the bilinear form `fderiv ℝ (fderiv ℝ Ψ) Z` into the operator with
  --     `⟪Abar v, w⟫ = A v w`, and its self-adjointness is exactly
  --     `ContDiffAt.isSymmSndFDerivAt`, which the `ContDiffAt ℝ 2 Ψ Z` hypothesis supplies.
  --   * THE QUANTIFIER ORDER OF STEP 0 IS LOAD-BEARING AND IS VISIBLE IN THE TACTIC SCRIPT:
  --     `Lam` is `obtain`ed and `refine ⟨Lam, hLam0, ?_⟩` is discharged BEFORE `intro τ`, so
  --     `Lam` cannot mention τ even by accident.  `eps`, `Bt` and everything else come after.
  --     The chain `1/eps + 4‖Bt‖ ≤ Lam` (hLamb) is what carries (T1) past the k-limit.
  --   * `BilinearFormBolzanoWeierstrass` is stated from `k ≥ 0` while the .tex indexes from
  --     `k ≥ 1`; the Lean sidesteps the reindex by taking the radii to be `1/(k+1)`.
  -- ============ the operator attached to D²Ψ(Z) by the Riesz representation ============
  obtain ⟨Abar, hAbar⟩ : ∃ T : PiLp 2 (fun _ : Fin N => E) →L[ℝ] PiLp 2 (fun _ : Fin N => E),
      ∀ v w : PiLp 2 (fun _ : Fin N => E),
        (inner ℝ (T v) w : ℝ) = (fderiv ℝ (fderiv ℝ Ψ) Z) v w :=
    ⟨InnerProductSpace.continuousLinearMapOfBilin (fderiv ℝ (fderiv ℝ Ψ) Z),
      fun v w => InnerProductSpace.continuousLinearMapOfBilin_apply _ v w⟩
  have hA2sym : ∀ v w : PiLp 2 (fun _ : Fin N => E),
      (fderiv ℝ (fderiv ℝ Ψ) Z) v w = (fderiv ℝ (fderiv ℝ Ψ) Z) w v :=
    hΨ.isSymmSndFDerivAt (by simp)
  -- ============ Step 0: the constant Λ, fixed BEFORE τ ============
  obtain ⟨Lam, hLamd⟩ : ∃ x : ℝ, x = max (2 / η) (2 * ‖Abar‖ + 4) + 4 * (‖Abar‖ + 1) := ⟨_, rfl⟩
  have hLam0 : 0 ≤ Lam := by
    rw [hLamd]
    have h1 : (0:ℝ) ≤ 2 * ‖Abar‖ + 4 := by positivity
    have h2 : (0:ℝ) ≤ max (2 / η) (2 * ‖Abar‖ + 4) := le_trans h1 (le_max_right _ _)
    have h3 : (0:ℝ) ≤ 4 * (‖Abar‖ + 1) := by positivity
    linarith
  refine ⟨Lam, hLam0, ?_⟩
  intro τ hτ0 hτ1
  -- ============ the perturbed operator B_τ = Abar + τ id ============
  obtain ⟨Bt, hBtd⟩ : ∃ T : PiLp 2 (fun _ : Fin N => E) →L[ℝ] PiLp 2 (fun _ : Fin N => E),
      T = Abar + τ • ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin N => E)) := ⟨_, rfl⟩
  have hBtapp : ∀ v w : PiLp 2 (fun _ : Fin N => E),
      (inner ℝ (Bt v) w : ℝ)
        = (fderiv ℝ (fderiv ℝ Ψ) Z) v w + τ * (inner ℝ v w : ℝ) := by
    intro v w
    rw [hBtd]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, inner_add_left,
      real_inner_smul_left]
    rw [hAbar]
  have hBtsa : ∀ ξ ζ : PiLp 2 (fun _ : Fin N => E),
      (inner ℝ (Bt ξ) ζ : ℝ) = inner ℝ ξ (Bt ζ) := by
    intro ξ ζ
    -- name the term: the generic `real_inner_comm` needs both slots given explicitly here
    have h1 : (inner ℝ ξ (Bt ζ) : ℝ) = inner ℝ (Bt ζ) ξ := real_inner_comm (Bt ζ) ξ
    rw [h1, hBtapp, hBtapp, hA2sym ζ ξ, real_inner_comm ξ ζ]
  have hBtnorm : ‖Bt‖ ≤ ‖Abar‖ + 1 := by
    rw [hBtd]
    -- name the term: `norm_add_le` with implicit arguments picks the wrong norm instance
    refine le_trans (norm_add_le Abar
      (τ • ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin N => E)))) ?_
    have hid : ‖ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin N => E))‖ ≤ 1 :=
      ContinuousLinearMap.norm_id_le
    have h1 : ‖τ • ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin N => E))‖ ≤ τ := by
      refine le_trans (ContinuousLinearMap.opNorm_smul_le τ
        (ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin N => E)))) ?_
      rw [Real.norm_eq_abs, abs_of_pos hτ0]
      nlinarith [hτ0, norm_nonneg (ContinuousLinearMap.id ℝ (PiLp 2 (fun _ : Fin N => E)))]
    linarith
  have hBtnn : (0:ℝ) ≤ ‖Bt‖ := norm_nonneg Bt
  -- THE RIESZ BRIDGE the statement needs: `‖B_τ ζ‖` is a VECTOR norm in V, while the goal
  -- carries the norm of the FUNCTIONAL `ξ ↦ A(ζ,ξ) + τ ⟪ζ,ξ⟫`.  They agree because
  -- `innerSL` is an isometry.
  have hBtvec : ∀ ζ : PiLp 2 (fun _ : Fin N => E),
      ‖Bt ζ‖ = ‖(fderiv ℝ (fderiv ℝ Ψ) Z) ζ + τ • innerSL ℝ ζ‖ := by
    intro ζ
    have hfun : innerSL ℝ (Bt ζ) = (fderiv ℝ (fderiv ℝ Ψ) Z) ζ + τ • innerSL ℝ ζ := by
      ext w
      simp only [innerSL_apply_apply, add_apply, smul_apply, smul_eq_mul]
      rw [hBtapp]
    rw [← innerSL_apply_norm (𝕜 := ℝ) (Bt ζ), hfun]
  -- ============ Step 0 continued: the regularization parameter ε(τ) ============
  obtain ⟨eps, hepsd⟩ : ∃ x : ℝ, x = min (η / 2) (1 / (2 * ‖Bt‖ + 2)) := ⟨_, rfl⟩
  have hden : (0:ℝ) < 2 * ‖Bt‖ + 2 := by linarith
  have heps0 : 0 < eps := by
    rw [hepsd]
    exact lt_min (by positivity) (by positivity)
  have hepsη : 2 * eps ≤ η := by
    have h1 : eps ≤ η / 2 := by rw [hepsd]; exact min_le_left _ _
    linarith
  have hepsB : eps * ‖Bt‖ ≤ 1 / 2 := by
    have h1 : eps ≤ 1 / (2 * ‖Bt‖ + 2) := by rw [hepsd]; exact min_le_right _ _
    have h2 : eps * ‖Bt‖ ≤ (1 / (2 * ‖Bt‖ + 2)) * ‖Bt‖ :=
      mul_le_mul_of_nonneg_right h1 hBtnn
    have h3 : (1 / (2 * ‖Bt‖ + 2)) * ‖Bt‖ ≤ 1 / 2 := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ hden (by norm_num)]
      linarith
    linarith
  have hepsinv : 1 / eps ≤ max (2 / η) (2 * ‖Abar‖ + 4) := by
    rcases le_total (η / 2) (1 / (2 * ‖Bt‖ + 2)) with hc | hc
    · have he : eps = η / 2 := by rw [hepsd, min_eq_left hc]
      have h1 : 1 / (η / 2) = 2 / η := by field_simp
      rw [he, h1]
      exact le_max_left _ _
    · have he : eps = 1 / (2 * ‖Bt‖ + 2) := by rw [hepsd, min_eq_right hc]
      have h1 : 1 / (1 / (2 * ‖Bt‖ + 2)) = 2 * ‖Bt‖ + 2 := by field_simp
      rw [he, h1]
      refine le_trans ?_ (le_max_right _ _)
      linarith
  have hLamb : 1 / eps + 4 * ‖Bt‖ ≤ Lam := by
    rw [hLamd]
    linarith
  -- ============ Step 1: the quadratic test ============
  obtain ⟨a, C, G, ha, hC, hGc, hGb, hGagree, hG3⟩ :=
    SumRuleQuadraticTest N hN O hO g hg Ψ Z hZ hΨ hmax τ hτ0
  have hG0 : ∀ j, G j 0 = 0 := by
    intro j
    rw [hGagree j 0 (by simpa using ha.le)]
    simp
  have hG3' : ∀ W : PiLp 2 (fun _ : Fin N => E), W ≠ 0 →
      (∑ j, G j (ofLp W j)) - (inner ℝ (Bt W) W : ℝ) / 2 ≤ -∑ j, ‖ofLp W j‖ ^ 4 := by
    intro W hW
    have h1 := hG3 W hW
    have h2 : (inner ℝ (Bt W) W : ℝ)
        = (fderiv ℝ (fderiv ℝ Ψ) Z) W W + τ * ‖W‖ ^ 2 := by
      rw [hBtapp, real_inner_self_eq_norm_sq]
    rw [h2]
    linarith
  -- ============ Step 2: the resolvent ============
  obtain ⟨Aeps, hAsa, hres, hinv, hpos, hAn, hR6⟩ :=
    SumRuleResolvent Bt hBtsa eps heps0 hepsB
  -- ============ Step 3: the duality test ============
  obtain ⟨hsep, Up, hUpdef, hUp0, hUpneg, hUpsc, hUpc⟩ :=
    SumRuleDualityTest N G C hC hGc hGb hG0 Bt Aeps hBtsa hAsa eps heps0 hres hinv hpos hG3'
  -- ============ Step 4: jets at the shrinking radii 1/(k+1) ============
  have hjet : ∀ k : ℕ, ∃ (Z' Pv : PiLp 2 (fun _ : Fin N => E))
      (Xf : Fin N → (E →L[ℝ] E →L[ℝ] ℝ)),
      ‖Z'‖ < 1 / ((k : ℝ) + 1) ∧
      ‖Pv‖ ≤ 1 / ((k : ℝ) + 1) + ‖Aeps‖ * (1 / ((k : ℝ) + 1)) ∧
      (∀ j, ∀ u v : E, Xf j u v = Xf j v u) ∧
      (∀ j, ‖Xf j‖ ≤ 1 / eps + 2 * ‖Aeps‖) ∧
      (∀ j, ((ofLp Pv j), Xf j) ∈ Superjet (G j) (ofLp Z' j + eps • ofLp Pv j)) ∧
      (∀ ζ : PiLp 2 (fun _ : Fin N => E),
        (∑ j, Xf j (ofLp ζ j) (ofLp ζ j)) ≤ (inner ℝ (Aeps ζ) ζ : ℝ)) := by
    intro k
    exact SumRuleJetFromJensen N G C hC hGc hGb eps heps0 Aeps hAsa Up hUpdef hsep
      hUp0 hUpneg hUpsc hUpc (1 / ((k : ℝ) + 1)) (1 / ((k : ℝ) + 1))
      (by positivity) (by positivity)
  choose Zs Ps Xs hZs hPs hXssym hXsnorm hXsjet hXsform using hjet
  -- the uniform, τ-free bound: this is the whole point of Step 0
  have hbound : ∀ (k : ℕ) (j : Fin N), ‖Xs k j‖ ≤ Lam := by
    intro k j
    have h1 := hXsnorm k j
    linarith [hAn, hLamb]
  -- ============ Step 5: the limit k → ∞ ============
  obtain ⟨Xl, φ, hφ, hconv⟩ := BilinearFormBolzanoWeierstrass N Lam Xs hbound
  have heval : ∀ (u v : E) (j : Fin N),
      Filter.Tendsto (fun k => Xs (φ k) j u v) Filter.atTop (nhds (Xl j u v)) := by
    intro u v j
    have hc : Continuous (fun Y : E →L[ℝ] E →L[ℝ] ℝ => Y u v) :=
      ((ContinuousLinearMap.apply ℝ ℝ v).comp
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) u)).continuous
    exact (hc.tendsto (Xl j)).comp (hconv j)
  have hXlsym : ∀ (j : Fin N) (u v : E), Xl j u v = Xl j v u := by
    intro j u v
    have h1 := heval u v j
    have h2 := heval v u j
    have heq : (fun k => Xs (φ k) j u v) = fun k => Xs (φ k) j v u := by
      funext k; exact hXssym (φ k) j u v
    rw [heq] at h1
    exact tendsto_nhds_unique h1 h2
  have hXlnorm : ∀ j : Fin N, ‖Xl j‖ ≤ Lam := by
    intro j
    refine le_of_tendsto ((continuous_norm.tendsto (Xl j)).comp (hconv j)) ?_
    filter_upwards with k
    exact hbound (φ k) j
  have hXlform : ∀ ζ : PiLp 2 (fun _ : Fin N => E),
      (∑ j, Xl j (ofLp ζ j) (ofLp ζ j)) ≤ (inner ℝ (Aeps ζ) ζ : ℝ) := by
    intro ζ
    refine le_of_tendsto (tendsto_finsetSum _
      (fun j _ => heval (ofLp ζ j) (ofLp ζ j) j)) ?_
    filter_upwards with k
    exact hXsform (φ k) ζ
  -- the ℓ²-coordinate bound, used to push the two shrinking estimates to a single coordinate
  have hpyth : ∀ ζ : PiLp 2 (fun _ : Fin N => E), (∑ j, ‖ofLp ζ j‖ ^ 2) = ‖ζ‖ ^ 2 := by
    intro ζ
    rw [← real_inner_self_eq_norm_sq, PiLp.inner_apply]
    exact Finset.sum_congr rfl (fun i _ => by rw [real_inner_self_eq_norm_sq])
  have hco : ∀ (ζ : PiLp 2 (fun _ : Fin N => E)) (j : Fin N), ‖ofLp ζ j‖ ≤ ‖ζ‖ := by
    intro ζ j
    have h1 : ‖ofLp ζ j‖ ^ 2 ≤ ∑ i, ‖ofLp ζ i‖ ^ 2 :=
      Finset.single_le_sum (f := fun i : Fin N => ‖ofLp ζ i‖ ^ 2)
        (fun i _ => by positivity) (Finset.mem_univ j)
    rw [hpyth ζ] at h1
    nlinarith [norm_nonneg (ofLp ζ j), norm_nonneg ζ]
  -- the subsequence only helps: φ k ≥ k, so the rates still go to zero
  have hinvle : ∀ k : ℕ, 1 / ((φ k : ℝ) + 1) ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have h1 : k ≤ φ k := hφ.le_apply
    have h2 : (k : ℝ) ≤ (φ k : ℝ) := Nat.cast_le.mpr h1
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  have htend0 : Filter.Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hAn0 : (0:ℝ) ≤ ‖Aeps‖ := norm_nonneg Aeps
  have hPn : ∀ (k : ℕ) (j : Fin N),
      ‖ofLp (Ps (φ k)) j‖ ≤ (1 + ‖Aeps‖) * (1 / ((k : ℝ) + 1)) := by
    intro k j
    have h1 : ‖ofLp (Ps (φ k)) j‖ ≤ ‖Ps (φ k)‖ := hco (Ps (φ k)) j
    have h2 := hPs (φ k)
    have h3 := hinvle k
    have h4 : (0:ℝ) < 1 / ((φ k : ℝ) + 1) := by positivity
    nlinarith [h1, h2, h3, hAn0]
  have hZn : ∀ (k : ℕ) (j : Fin N),
      ‖ofLp (Zs (φ k)) j‖ ≤ 1 / ((k : ℝ) + 1) := by
    intro k j
    have h1 : ‖ofLp (Zs (φ k)) j‖ ≤ ‖Zs (φ k)‖ := hco (Zs (φ k)) j
    have h2 := hZs (φ k)
    have h3 := hinvle k
    linarith
  have hps0 : ∀ j : Fin N, Filter.Tendsto
      (fun k => ofLp (Ps (φ k)) j) Filter.atTop (nhds 0) := by
    intro j
    have hb2 : Filter.Tendsto (fun k : ℕ => (1 + ‖Aeps‖) * (1 / ((k : ℝ) + 1)))
        Filter.atTop (nhds 0) := by simpa using htend0.const_mul (1 + ‖Aeps‖)
    exact squeeze_zero_norm (fun k => hPn k j) hb2
  have hzs0 : ∀ j : Fin N, Filter.Tendsto
      (fun k => ofLp (Zs (φ k)) j + eps • ofLp (Ps (φ k)) j) Filter.atTop (nhds 0) := by
    intro j
    have hb1 : ∀ k : ℕ, ‖ofLp (Zs (φ k)) j + eps • ofLp (Ps (φ k)) j‖
        ≤ (1 + eps * (1 + ‖Aeps‖)) * (1 / ((k : ℝ) + 1)) := by
      intro k
      have h1 : ‖ofLp (Zs (φ k)) j + eps • ofLp (Ps (φ k)) j‖
          ≤ ‖ofLp (Zs (φ k)) j‖ + ‖eps • ofLp (Ps (φ k)) j‖ := norm_add_le _ _
      have h2 : ‖eps • ofLp (Ps (φ k)) j‖ = eps * ‖ofLp (Ps (φ k)) j‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos heps0]
      have h3 := hPn k j
      have h4 := hZn k j
      nlinarith [heps0, h1, h2, h3, h4]
    have hb2 : Filter.Tendsto (fun k : ℕ => (1 + eps * (1 + ‖Aeps‖)) * (1 / ((k : ℝ) + 1)))
        Filter.atTop (nhds 0) := by
      simpa using htend0.const_mul (1 + eps * (1 + ‖Aeps‖))
    exact squeeze_zero_norm hb1 hb2
  -- the closed superjet of `G j` at `0`: all four requirements of `ClosedSuperjet`
  have hcs : ∀ j : Fin N, ((0 : E), Xl j) ∈ ClosedSuperjet (G j) 0 := by
    intro j
    exact ⟨fun k => ofLp (Zs (φ k)) j + eps • ofLp (Ps (φ k)) j,
      fun k => ofLp (Ps (φ k)) j, fun k => Xs (φ k) j,
      fun k => hXsjet (φ k) j, hzs0 j, ((hGc j).tendsto 0).comp (hzs0 j),
      hps0 j, hconv j⟩
  -- ============ Step 6: back to g j, along ClosedSuperjetLocal → Quartic → AffineShift ======
  have hgoal : ∀ j : Fin N,
      ((ofLp (∇ Ψ Z) j), Xl j) ∈ ClosedSuperjet (g j) (ofLp Z j) := by
    intro j
    have h1 : ClosedSuperjet (G j) 0
        = ClosedSuperjet (fun w : E => (g j (ofLp Z j + w) - g j (ofLp Z j)
            - (inner ℝ (ofLp (∇ Ψ Z) j) w : ℝ)) - ‖w‖ ^ 4) 0 :=
      ClosedSuperjetLocal (G j) _ a ha (fun w hw => hGagree j w hw.le)
    have h2 : ClosedSuperjet (fun w : E => (g j (ofLp Z j + w) - g j (ofLp Z j)
            - (inner ℝ (ofLp (∇ Ψ Z) j) w : ℝ)) - ‖w‖ ^ 4) 0
        = ClosedSuperjet (fun w : E => g j (ofLp Z j + w) - g j (ofLp Z j)
            - (inner ℝ (ofLp (∇ Ψ Z) j) w : ℝ)) 0 :=
      ClosedSuperjetQuartic _
    have h4 : ((0 : E), Xl j) ∈ ClosedSuperjet (fun w : E => g j (ofLp Z j + w)
        - g j (ofLp Z j) - (inner ℝ (ofLp (∇ Ψ Z) j) w : ℝ)) 0 := by
      rw [← h2, ← h1]
      exact hcs j
    have h5 := (ClosedSuperjetAffineShift (g j) (ofLp Z j) (ofLp (∇ Ψ Z) j) 0 (Xl j)).mp h4
    rwa [zero_add] at h5
  -- ============ Step 7: the matrix inequality for B_τ ============
  refine ⟨Xl, hXlsym, hXlnorm, hgoal, ?_⟩
  intro ζ
  have h1 := hXlform ζ
  have h2 := hR6 η hepsη ζ
  have h3 : (inner ℝ (Bt ζ) ζ : ℝ)
      = (fderiv ℝ (fderiv ℝ Ψ) Z) ζ ζ + τ * ‖ζ‖ ^ 2 := by
    rw [hBtapp, real_inner_self_eq_norm_sq]
  rw [hBtvec ζ, h3] at h2
  linarith
