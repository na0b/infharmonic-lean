import InfHarmonic.IsBadScaleData
import InfHarmonic.CylinderFitSlopeBounds
import InfHarmonic.CylinderComparisonSameCenter
import InfHarmonic.CylinderComparisonShifted
import InfHarmonic.CylinderFitDoublingChain
import InfHarmonic.NormalizedSlopeCoefficients
import InfHarmonic.AnisotropicBoxOffsets
import InfHarmonic.ShearedBoxInFitCylinder
set_option maxHeartbeats 400000
open Metric Set Filter Topology WithLp

/-- Step 5 of Proposition 3.6, both parts.  Part 1 produces the enclosing fit at
`(z i, Rad K * r i)`: its slope is normalized, its cylinder contains the image
of `Box K`, and the quarter-bounds of Claim 4a together with the base
comparison with `P i` are exported alongside it.  Part 2 then produces, for
every `w` in `Box K`, a nearby fit at `(Zi i w, S * r i)` whose normalized
coefficients are bounded independently of `i`.  The route is a chain of
citations run twice out of the common base radius `min S (Rad K) * r i`, which
avoids a case split on whether `S` or `Rad K` is the larger. -/
theorem EnclosingAndNearbyFits (d : ℕ) (r lam : ℕ → ℝ)
    (U : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ) (z P : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (Φ : ℕ → (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) ≃ₗᵢ[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
    (th cc : ℕ → ℝ) (Zi : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
    (Box : ℝ → Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))) (Rad : ℝ → ℝ)
    (Mof : ℝ → ℝ → ℝ) (iadm : ℝ → ℝ → ℕ)
    (L C₁ C₂ : ℝ) (i₂ : ℕ)
    (hr0 : ∀ i, 0 < r i) (hlam0 : ∀ i, 0 < lam i) (hL0 : (0:ℝ) ≤ L)
    (hthdef : th = fun i => Real.sqrt (32 * lam i))
    (htail2 : ∀ i ≥ i₂, th i ≤ 1 / 2)
    (hC₁1 : 1 ≤ C₁)
    (hcmpA :
      (∀ (i : ℕ) (w : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (H H' : ℝ)
        (Q Q' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), i₂ ≤ i →
        0 < H → H ≤ H' → H' ≤ 2 * H →
        1 / 2 ≤ ‖Q‖ → ‖Q‖ ≤ L + 1 → 1 / 2 ≤ ‖Q'‖ → ‖Q'‖ ≤ L + 1 →
        IsCylinderFit (U i) w H (32 * lam i) Q →
        IsCylinderFit (U i) w H' (32 * lam i) Q' →
        ‖Q - Q'‖ + ‖‖Q‖⁻¹ • Q - ‖Q'‖⁻¹ • Q'‖ ≤ C₁ * th i ∧
        |‖Q‖ - ‖Q'‖| ≤ C₁ * th i ^ 2))
    (hcmpB :
      (∀ (i : ℕ) (w w' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (H : ℝ)
        (Q Q' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), i₂ ≤ i → 0 < H →
        1 / 2 ≤ ‖Q‖ → ‖Q‖ ≤ L + 1 → 1 / 2 ≤ ‖Q'‖ → ‖Q'‖ ≤ L + 1 →
        |(inner ℝ (‖Q‖⁻¹ • Q) (w' - w) : ℝ)| ≤ H / 4 →
        ‖(w' - w) - (inner ℝ (‖Q‖⁻¹ • Q) (w' - w) : ℝ) • (‖Q‖⁻¹ • Q)‖ ≤ th i * H / 4 →
        IsCylinderFit (U i) w H (32 * lam i) Q →
        IsCylinderFit (U i) w' H (32 * lam i) Q' →
        ‖Q - Q'‖ + ‖‖Q‖⁻¹ • Q - ‖Q'‖⁻¹ • Q'‖ ≤ C₁ * th i ∧
        |‖Q‖ - ‖Q'‖| ≤ C₁ * th i ^ 2))
    (hC₂0 : (0:ℝ) ≤ C₂)
    (hchain :
      ∀ R : ℝ, 2 ≤ R → ∀ M : ℝ, 2 ≤ M → R ≤ M → ∃ i₀ : ℕ, i₂ ≤ i₀ ∧ ∀ i ≥ i₀,
        ∃ PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (z i) (R * r i) (32 * lam i) PR ∧
          1 / 2 ≤ ‖PR‖ ∧ ‖PR‖ ≤ L + 1 ∧
          ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log R) * th i ∧
          |‖PR‖ - cc i| ≤ C₂ * (1 + Real.log R) * th i ^ 2)
    (hRad2 : ∀ K : ℝ, 1 ≤ K → 2 ≤ Rad K)
    (hMofK : ∀ K S : ℝ, 1 ≤ K → 0 < S → 2 * K ≤ Mof K S)
    (hMofR : ∀ K S : ℝ, 1 ≤ K → 0 < S → Rad K ≤ Mof K S)
    (hMofS : ∀ K S : ℝ, 1 ≤ K → 0 < S → S ≤ Mof K S)
    (hiadm : ∀ K S : ℝ, i₂ ≤ iadm K S)
    (hfitw :
      (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ iadm K S, ∀ w ∈ Box K,
        ∀ rho : ℝ, 0 < rho → rho ≤ Mof K S * r i →
        ∃ Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (Zi i w) rho (32 * lam i) Q ∧
          1 / 2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ L + 1))
    (hcoeff :
      ∀ i ≥ i₂, ∀ (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (δ : ℝ),
            0 ≤ δ → 1 / 2 ≤ ‖Q‖ → ‖Q‖ ≤ L + 1 →
            ‖‖Q‖⁻¹ • Q - (cc i)⁻¹ • P i‖ ≤ δ * th i → |‖Q‖ - cc i| ≤ δ * th i ^ 2 →
            ∃ (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
              Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p', cc i * (1 + lam i * q'))) ∧
              ‖p'‖ + |q'| ≤ 100 * (1 + L) * (δ + δ ^ 2))
    (hclaim4a :
      ∀ K : ℝ, 1 ≤ K → ∀ i ≥ i₂,
            ∀ PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), 1 / 2 ≤ ‖PR‖ →
            ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log (Rad K)) * th i →
            ∀ w ∈ Box K,
              |(inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ)| ≤ Rad K * r i / 4 ∧
              ‖(Zi i w - z i)
                  - (inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ) • (‖PR‖⁻¹ • PR)‖
                ≤ th i * (Rad K * r i) / 4) :
    ∃ (CR : ℝ → ℝ → ℝ) (ifitR : ℝ → ℝ → ℕ) (CN : ℝ → ℝ → ℝ)
      (ifitN : ℝ → ℝ → ℕ),
      (∀ K S : ℝ, 0 ≤ CR K S) ∧
      (∀ K S : ℝ, iadm K S ≤ ifitR K S) ∧
      (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifitR K S,
        ∃ (PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          (pR : EuclideanSpace ℝ (Fin d)) (qR : ℝ),
          IsCylinderFit (U i) (z i) (Rad K * r i) (32 * lam i) PR ∧
          1 / 2 ≤ ‖PR‖ ∧ ‖PR‖ ≤ L + 1 ∧
          PR = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • pR,
            cc i * (1 + lam i * qR))) ∧
          ‖pR‖ + |qR| ≤ CR K S ∧
          (∀ w ∈ Box K, Zi i w ∈ FitCylinder (z i) (Rad K * r i) (32 * lam i) PR) ∧
          (∀ w ∈ Box K,
            |(inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ)| ≤ Rad K * r i / 4 ∧
            ‖(Zi i w - z i)
                - (inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ) • (‖PR‖⁻¹ • PR)‖
              ≤ th i * (Rad K * r i) / 4) ∧
          ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log (Rad K)) * th i ∧
          |‖PR‖ - cc i| ≤ C₂ * (1 + Real.log (Rad K)) * th i ^ 2) ∧
      (∀ K S : ℝ, 0 ≤ CN K S) ∧
      (∀ K S : ℝ, ifitR K S ≤ ifitN K S) ∧
      (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifitN K S, ∀ w ∈ Box K,
        ∃ (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
          (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
          IsCylinderFit (U i) (Zi i w) (S * r i) (32 * lam i) Q ∧
          Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p',
            cc i * (1 + lam i * q'))) ∧
          ‖p'‖ + |q'| ≤ CN K S) := by
  -- ===================== STEP 5, PART 1: THE ENCLOSING FIT ===================
  -- `hchain` supplies the fit at `(z_i, R r_i)` and its comparison with `P_i`; `hclaim4a`
  -- puts `Z_i(Box K)` in its quarter-cylinder, hence a fortiori in its cylinder; and
  -- `hcoeff` normalizes its slope.  The quarter-bounds are exported too, because Step 2(b)
  -- consumes them when the nearby fit is compared with this one.
  obtain ⟨CR, ifitR, hCR0, hifitR, henclR⟩ :
      ∃ (CR : ℝ → ℝ → ℝ) (ifitR : ℝ → ℝ → ℕ),
        (∀ K S : ℝ, 0 ≤ CR K S) ∧
        (∀ K S : ℝ, iadm K S ≤ ifitR K S) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifitR K S,
          ∃ (PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
            (pR : EuclideanSpace ℝ (Fin d)) (qR : ℝ),
            IsCylinderFit (U i) (z i) (Rad K * r i) (32 * lam i) PR ∧
            1 / 2 ≤ ‖PR‖ ∧ ‖PR‖ ≤ L + 1 ∧
            PR = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • pR,
              cc i * (1 + lam i * qR))) ∧
            ‖pR‖ + |qR| ≤ CR K S ∧
            (∀ w ∈ Box K, Zi i w ∈ FitCylinder (z i) (Rad K * r i) (32 * lam i) PR) ∧
            (∀ w ∈ Box K,
              |(inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ)| ≤ Rad K * r i / 4 ∧
              ‖(Zi i w - z i)
                  - (inner ℝ (‖PR‖⁻¹ • PR) (Zi i w - z i) : ℝ) • (‖PR‖⁻¹ • PR)‖
                ≤ th i * (Rad K * r i) / 4) ∧
            ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log (Rad K)) * th i ∧
            |‖PR‖ - cc i| ≤ C₂ * (1 + Real.log (Rad K)) * th i ^ 2) := by
    -- `hchain`'s threshold, as a total function of `(K, S)`
    have hch : ∀ K S : ℝ, ∃ j : ℕ, 1 ≤ K → 0 < S → i₂ ≤ j ∧ ∀ i ≥ j,
        ∃ PR : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (z i) (Rad K * r i) (32 * lam i) PR ∧
          1 / 2 ≤ ‖PR‖ ∧ ‖PR‖ ≤ L + 1 ∧
          ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ C₂ * (1 + Real.log (Rad K)) * th i ∧
          |‖PR‖ - cc i| ≤ C₂ * (1 + Real.log (Rad K)) * th i ^ 2 := by
      intro K S
      by_cases hKS : 1 ≤ K ∧ 0 < S
      · have hM2 : (2 : ℝ) ≤ Mof K S := by
          have h := hMofK K S hKS.1 hKS.2
          linarith only [h, hKS.1]
        obtain ⟨j, hj0, hj⟩ := hchain (Rad K) (hRad2 K hKS.1) (Mof K S) hM2
          (hMofR K S hKS.1 hKS.2)
        exact ⟨j, fun _ _ => ⟨hj0, hj⟩⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hKS⟩
    choose jch hjch using hch
    obtain ⟨dR, hdRdef⟩ : ∃ dR : ℝ → ℝ,
        dR = fun K => C₂ * (1 + Real.log (Rad K)) := ⟨_, rfl⟩
    have hdRapp : ∀ K : ℝ, dR K = C₂ * (1 + Real.log (Rad K)) := by
      intro K; rw [hdRdef]
    have hdR0 : ∀ K : ℝ, 1 ≤ K → 0 ≤ dR K := by
      intro K hK
      rw [hdRapp K]
      refine mul_nonneg hC₂0 ?_
      linarith only [Real.log_nonneg (by linarith only [hRad2 K hK] : (1 : ℝ) ≤ Rad K)]
    refine ⟨fun K S => max 0 (100 * (1 + L) * (dR K + dR K ^ 2)),
      fun K S => max (iadm K S) (jch K S), fun K S => le_max_left _ _,
      fun K S => le_max_left _ _, ?_⟩
    · intro K hK S hS i hi
      have hi2 : i₂ ≤ i :=
        le_trans (le_trans (hiadm K S) (le_max_left _ _)) hi
      have hij : jch K S ≤ i := le_trans (le_max_right _ _) hi
      obtain ⟨-, hj⟩ := hjch K S hK hS
      obtain ⟨PR, hfit, hPl, hPu, hdir, hnrm⟩ := hj i hij
      have hdirD : ‖‖PR‖⁻¹ • PR - (cc i)⁻¹ • P i‖ ≤ dR K * th i := by
        rw [hdRapp K]; exact hdir
      have hnrmD : |‖PR‖ - cc i| ≤ dR K * th i ^ 2 := by
        rw [hdRapp K]; exact hnrm
      obtain ⟨pR, qR, heq, hbd⟩ :=
        hcoeff i hi2 PR (dR K) (hdR0 K hK) hPl hPu hdirD hnrmD
      have hq4 := hclaim4a K hK i hi2 PR hPl hdir
      refine ⟨PR, pR, qR, hfit, hPl, hPu, heq,
        le_trans hbd (le_max_right _ _), ?_, hq4, hdir, hnrm⟩
      intro w hw
      obtain ⟨ha, hb⟩ := hq4 w hw
      have hthsq : Real.sqrt (32 * lam i) = th i := by rw [hthdef]
      have hRr0 : (0 : ℝ) < Rad K * r i :=
        mul_pos (by linarith only [hRad2 K hK]) (hr0 i)
      have hth0 : 0 ≤ th i := by rw [hthdef]; exact Real.sqrt_nonneg _
      refine ⟨by linarith only [ha, hRr0], ?_⟩
      rw [hthsq]
      have h1 : 0 ≤ th i * (Rad K * r i) := mul_nonneg hth0 (le_of_lt hRr0)
      linarith only [hb, h1]
  -- The doubling-chain constant, at the slope window `[1/2, L+1]` of eq:nl-slope.
  obtain ⟨Cdc, hCdc0, hdchain⟩ := CylinderFitDoublingChain
    (E := WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (1 / 2) (L + 1) (by norm_num)
    (by linarith only [hL0])
  -- `max 2 (a/m) * m` lies between `a` and `2a` whenever `0 < m ≤ a`.  This is what makes
  -- the cited chain node usable at an arbitrary ratio: the node insists on ratio `≥ 2`,
  -- and clamping the ratio at 2 overshoots the target radius by at most one doubling,
  -- which ONE same-centre comparison (Step 2(a)) repairs.
  have hratio : ∀ m a : ℝ, 0 < m → 0 < a → m ≤ a →
      a ≤ max 2 (a / m) * m ∧ max 2 (a / m) * m ≤ 2 * a := by
    intro m a hm ha hma
    have hdm : a / m * m = a := div_mul_cancel₀ a (ne_of_gt hm)
    refine ⟨?_, ?_⟩
    · have h1 : a / m ≤ max 2 (a / m) := le_max_right _ _
      nlinarith only [h1, hdm, hm]
    · rcases le_total (a / m) 2 with h | h
      · rw [max_eq_left h]; linarith only [hma, hm]
      · rw [max_eq_right h]; linarith only [hdm, ha]
  -- ===================== STEP 5, PART 2: THE NEARBY FITS =====================
  -- For `w ∈ Box K` we need a fit at `(Z_i(w), S r_i)` whose normalized coefficients are
  -- bounded independently of `i`.  The route, and it is all CITATIONS:
  --
  --   Q  at (Z_i(w), S r_i)      --.
  --                                 >-- both compared to Q_m at the COMMON base radius
  --   Q_R at (Z_i(w), R r_i)     --'    m r_i, m = min(S, R), via two instances of
  --                                     `CylinderFitDoublingChain` plus one Step 2(a)
  --   Q_R  vs  P_R at (z_i, R r_i)      by Step 2(b), whose two centre-offset
  --                                     hypotheses are exactly Claim 4a's quarter-bounds
  --   P_R  vs  P_i                      by eq:nl-base-chain, now exported by `henclR`
  --
  -- Running the chain twice OUT of the common base `m r_i` -- rather than once from the
  -- smaller to the larger of the two radii -- avoids a case split on `S ≤ R(K)`: both
  -- `S r_i` and `R(K) r_i` are `≥ m r_i`, so the two legs are literally the same argument.
  -- Each leg's ratio is clamped at 2 by `hratio`, so each costs one extra Step 2(a); and
  -- because `r_i` cancels out of `max 2 (a/m)`, both ratios -- hence the constant -- are
  -- independent of `i`, which is what Steps 7 and 8 need.
  obtain ⟨CN, ifitN, hCN0, hifitN, hnearbyN⟩ :
      ∃ (CN : ℝ → ℝ → ℝ) (ifitN : ℝ → ℝ → ℕ),
        (∀ K S : ℝ, 0 ≤ CN K S) ∧
        (∀ K S : ℝ, ifitR K S ≤ ifitN K S) ∧
        (∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifitN K S, ∀ w ∈ Box K,
          ∃ (Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ))
            (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
            IsCylinderFit (U i) (Zi i w) (S * r i) (32 * lam i) Q ∧
            Q = Φ i (toLp 2 ((cc i * Real.sqrt (lam i)) • p',
              cc i * (1 + lam i * q'))) ∧
            ‖p'‖ + |q'| ≤ CN K S) := by
    -- the triangle inequality in the shape every leg uses
    have htri3 : ∀ x y u : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
        ‖x - u‖ ≤ ‖x - y‖ + ‖y - u‖ := by
      intro x y u
      have h : x - u = (x - y) + (y - u) := by abel
      rw [h]; exact norm_add_le _ _
    -- `δ(K,S)`: the total drift from `Q` back to `P_i` along the four links above.
    obtain ⟨dl, hdldef⟩ : ∃ dl : ℝ → ℝ → ℝ, dl = fun K S =>
        Cdc * (1 + Real.log (max 2 (S / min S (Rad K))))
          + Cdc * (1 + Real.log (max 2 (Rad K / min S (Rad K))))
          + 2 * C₁ + C₁ + C₂ * (1 + Real.log (Rad K)) := ⟨_, rfl⟩
    have hdlapp : ∀ K S : ℝ, dl K S =
        Cdc * (1 + Real.log (max 2 (S / min S (Rad K))))
          + Cdc * (1 + Real.log (max 2 (Rad K / min S (Rad K))))
          + 2 * C₁ + C₁ + C₂ * (1 + Real.log (Rad K)) := by
      intro K S; rw [hdldef]
    refine ⟨fun K S => max 0 (100 * (1 + L) * (dl K S + dl K S ^ 2)),
      fun K S => max (ifitR K S) (iadm K (2 * max S (Rad K))),
      fun K S => le_max_left _ _, fun K S => le_max_left _ _, ?_⟩
    intro K hK S hS i hi w hw
    have hiR : ifitR K S ≤ i := le_trans (le_max_left _ _) hi
    have hi2 : i₂ ≤ i := le_trans (hiadm K S) (le_trans (hifitR K S) hiR)
    have hr := hr0 i
    have hth0 : (0 : ℝ) < th i := by
      rw [hthdef]; exact Real.sqrt_pos.mpr (by linarith only [hlam0 i])
    have hth1 : th i < 1 := by linarith only [htail2 i hi2]
    have hthsq : th i ^ 2 = 32 * lam i := by
      rw [hthdef]; exact Real.sq_sqrt (by linarith only [hlam0 i])
    have hRad0 : (0 : ℝ) < Rad K := by linarith only [hRad2 K hK]
    -- the three `i`-independent scales: the common base `m`, and the two clamped ratios
    obtain ⟨m0, hm0def⟩ : ∃ m0 : ℝ, m0 = min S (Rad K) := ⟨_, rfl⟩
    obtain ⟨Ra, hRadef⟩ : ∃ Ra : ℝ, Ra = max 2 (S / m0) := ⟨_, rfl⟩
    obtain ⟨Rb, hRbdef⟩ : ∃ Rb : ℝ, Rb = max 2 (Rad K / m0) := ⟨_, rfl⟩
    obtain ⟨Sb, hSbdef⟩ : ∃ Sb : ℝ, Sb = 2 * max S (Rad K) := ⟨_, rfl⟩
    have hm00 : (0 : ℝ) < m0 := by rw [hm0def]; exact lt_min hS hRad0
    have hm0S : m0 ≤ S := by rw [hm0def]; exact min_le_left _ _
    have hm0R : m0 ≤ Rad K := by rw [hm0def]; exact min_le_right _ _
    have hmS : S ≤ max S (Rad K) := le_max_left _ _
    have hmR : Rad K ≤ max S (Rad K) := le_max_right _ _
    have hSb0 : (0 : ℝ) < Sb := by rw [hSbdef]; linarith only [hmS, hS]
    have hSSb : S ≤ Sb := by rw [hSbdef]; linarith only [hmS, hS]
    have hRSb : Rad K ≤ Sb := by rw [hSbdef]; linarith only [hmR, hRad0]
    have hm0Sb : m0 ≤ Sb := le_trans hm0S hSSb
    have hiSb : iadm K Sb ≤ i := by
      rw [hSbdef]; exact le_trans (le_max_right _ _) hi
    -- `hgood` at the enlarged scale: a fit at EVERY radius up to `Sb r_i`, centre `Z_i(w)`
    have hfitall : ∀ rho : ℝ, 0 < rho → rho ≤ Sb * r i →
        ∃ Q : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (Zi i w) rho (th i ^ 2) Q ∧
            1 / 2 ≤ ‖Q‖ ∧ ‖Q‖ ≤ L + 1 := by
      intro rho hrho0 hrhole
      obtain ⟨Q, hQfit, hQl, hQu⟩ := hfitw K hK Sb hSb0 i hiSb w hw rho hrho0
        (le_trans hrhole (mul_le_mul_of_nonneg_right (hMofS K Sb hK hSb0) (le_of_lt hr)))
      exact ⟨Q, by rw [hthsq]; exact hQfit, hQl, hQu⟩
    -- the ratio arithmetic, once per leg
    have hRa2 : (2 : ℝ) ≤ Ra := by rw [hRadef]; exact le_max_left _ _
    have hRb2 : (2 : ℝ) ≤ Rb := by rw [hRbdef]; exact le_max_left _ _
    have hRaS : S ≤ Ra * m0 ∧ Ra * m0 ≤ 2 * S := by
      rw [hRadef]; exact hratio m0 S hm00 hS hm0S
    have hRbR : Rad K ≤ Rb * m0 ∧ Rb * m0 ≤ 2 * Rad K := by
      rw [hRbdef]; exact hratio m0 (Rad K) hm00 hRad0 hm0R
    have hSbA : Ra * m0 ≤ Sb := by rw [hSbdef]; linarith only [hRaS.2, hmS]
    have hSbB : Rb * m0 ≤ Sb := by rw [hSbdef]; linarith only [hRbR.2, hmR]
    have hm0r : (0 : ℝ) < m0 * r i := mul_pos hm00 hr
    -- the base fit and the two target fits
    obtain ⟨Qm, hQmfit, hQml, hQmu⟩ := hfitall (m0 * r i) hm0r
      (mul_le_mul_of_nonneg_right hm0Sb (le_of_lt hr))
    obtain ⟨Q, hQfit, hQl, hQu⟩ := hfitall (S * r i) (mul_pos hS hr)
      (mul_le_mul_of_nonneg_right hSSb (le_of_lt hr))
    obtain ⟨QR, hQRfit, hQRl, hQRu⟩ := hfitall (Rad K * r i) (mul_pos hRad0 hr)
      (mul_le_mul_of_nonneg_right hRSb (le_of_lt hr))
    -- LEG A: the chain from `m r_i` out to `Ra * (m r_i) ∈ [S r_i, 2 S r_i]`, then Step 2(a)
    have hfitsA : ∀ rho : ℝ, 0 < rho → rho ≤ Ra * (m0 * r i) →
        ∃ Q' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (Zi i w) rho (th i ^ 2) Q' ∧
            1 / 2 ≤ ‖Q'‖ ∧ ‖Q'‖ ≤ L + 1 := by
      intro rho h1 h2
      refine hfitall rho h1 (le_trans h2 ?_)
      have hassoc : Ra * (m0 * r i) = Ra * m0 * r i := by ring
      rw [hassoc]
      exact mul_le_mul_of_nonneg_right hSbA (le_of_lt hr)
    obtain ⟨QA, hQAfit, hQAl, hQAu, hQAdir, hQAnrm⟩ :=
      hdchain (U i) (Zi i w) (m0 * r i) (th i) Ra Qm hm0r hth0 hth1 hRa2 hQml hQmu
        hQmfit hfitsA
    have hAlo : S * r i ≤ Ra * (m0 * r i) := by
      have h := mul_le_mul_of_nonneg_right hRaS.1 (le_of_lt hr)
      nlinarith only [h]
    have hAhi : Ra * (m0 * r i) ≤ 2 * (S * r i) := by
      have h := mul_le_mul_of_nonneg_right hRaS.2 (le_of_lt hr)
      nlinarith only [h]
    obtain ⟨gA1, gA2⟩ := hcmpA i (Zi i w) (S * r i) (Ra * (m0 * r i)) Q QA hi2
      (mul_pos hS hr) hAlo hAhi hQl hQu hQAl hQAu
      (by rw [← hthsq]; exact hQfit) (by rw [← hthsq]; exact hQAfit)
    -- LEG B: the same, out to `Rb * (m r_i) ∈ [R r_i, 2 R r_i]`
    have hfitsB : ∀ rho : ℝ, 0 < rho → rho ≤ Rb * (m0 * r i) →
        ∃ Q' : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ),
          IsCylinderFit (U i) (Zi i w) rho (th i ^ 2) Q' ∧
            1 / 2 ≤ ‖Q'‖ ∧ ‖Q'‖ ≤ L + 1 := by
      intro rho h1 h2
      refine hfitall rho h1 (le_trans h2 ?_)
      have hassoc : Rb * (m0 * r i) = Rb * m0 * r i := by ring
      rw [hassoc]
      exact mul_le_mul_of_nonneg_right hSbB (le_of_lt hr)
    obtain ⟨QB, hQBfit, hQBl, hQBu, hQBdir, hQBnrm⟩ :=
      hdchain (U i) (Zi i w) (m0 * r i) (th i) Rb Qm hm0r hth0 hth1 hRb2 hQml hQmu
        hQmfit hfitsB
    have hBlo : Rad K * r i ≤ Rb * (m0 * r i) := by
      have h := mul_le_mul_of_nonneg_right hRbR.1 (le_of_lt hr)
      nlinarith only [h]
    have hBhi : Rb * (m0 * r i) ≤ 2 * (Rad K * r i) := by
      have h := mul_le_mul_of_nonneg_right hRbR.2 (le_of_lt hr)
      nlinarith only [h]
    obtain ⟨gB1, gB2⟩ := hcmpA i (Zi i w) (Rad K * r i) (Rb * (m0 * r i)) QR QB hi2
      (mul_pos hRad0 hr) hBlo hBhi hQRl hQRu hQBl hQBu
      (by rw [← hthsq]; exact hQRfit) (by rw [← hthsq]; exact hQBfit)
    -- LINK 3: Step 2(b) at the common radius `R r_i`, fed by Claim 4a's quarter-bounds
    obtain ⟨PR, pR, qR, hPRfit, hPRl, hPRu, hPReq, hPRbd, hPRcyl, hPRq4, hPRdir, hPRnrm⟩ :=
      henclR K hK S hS i hiR
    obtain ⟨hax, htr⟩ := hPRq4 w hw
    obtain ⟨gD1, gD2⟩ := hcmpB i (z i) (Zi i w) (Rad K * r i) PR QR hi2
      (mul_pos hRad0 hr) hPRl hPRu hQRl hQRu hax htr hPRfit
      (by rw [← hthsq]; exact hQRfit)
    -- assemble the four links
    obtain ⟨da, hdadef⟩ : ∃ da : ℝ, da = Cdc * (1 + Real.log Ra) := ⟨_, rfl⟩
    obtain ⟨db, hdbdef⟩ : ∃ db : ℝ, db = Cdc * (1 + Real.log Rb) := ⟨_, rfl⟩
    obtain ⟨dp, hdpdef⟩ : ∃ dp : ℝ, dp = C₂ * (1 + Real.log (Rad K)) := ⟨_, rfl⟩
    rw [← hdadef] at hQAdir hQAnrm
    rw [← hdbdef] at hQBdir hQBnrm
    rw [← hdpdef] at hPRdir hPRnrm
    have hdQA : ‖‖Q‖⁻¹ • Q - ‖QA‖⁻¹ • QA‖ ≤ C₁ * th i := by
      linarith only [gA1, norm_nonneg (Q - QA)]
    have hdQRB : ‖‖QR‖⁻¹ • QR - ‖QB‖⁻¹ • QB‖ ≤ C₁ * th i := by
      linarith only [gB1, norm_nonneg (QR - QB)]
    have hdPRQR : ‖‖PR‖⁻¹ • PR - ‖QR‖⁻¹ • QR‖ ≤ C₁ * th i := by
      linarith only [gD1, norm_nonneg (PR - QR)]
    -- `Q -> Q_m` and `Q_R -> Q_m`
    have hdQm : ‖‖Q‖⁻¹ • Q - ‖Qm‖⁻¹ • Qm‖ ≤ da * th i + C₁ * th i :=
      le_trans (htri3 (‖Q‖⁻¹ • Q) (‖QA‖⁻¹ • QA) (‖Qm‖⁻¹ • Qm))
        (by linarith only [hdQA, hQAdir])
    have hdQRm : ‖‖QR‖⁻¹ • QR - ‖Qm‖⁻¹ • Qm‖ ≤ db * th i + C₁ * th i :=
      le_trans (htri3 (‖QR‖⁻¹ • QR) (‖QB‖⁻¹ • QB) (‖Qm‖⁻¹ • Qm))
        (by linarith only [hdQRB, hQBdir])
    -- `Q -> Q_R` through `Q_m`, then `Q_R -> P_R -> P_i`
    have hdQQR : ‖‖Q‖⁻¹ • Q - ‖QR‖⁻¹ • QR‖ ≤ da * th i + db * th i + 2 * C₁ * th i := by
      have hrev : ‖‖Qm‖⁻¹ • Qm - ‖QR‖⁻¹ • QR‖ = ‖‖QR‖⁻¹ • QR - ‖Qm‖⁻¹ • Qm‖ :=
        norm_sub_rev _ _
      have h := htri3 (‖Q‖⁻¹ • Q) (‖Qm‖⁻¹ • Qm) (‖QR‖⁻¹ • QR)
      rw [hrev] at h
      linarith only [h, hdQm, hdQRm]
    have hdfin : ‖‖Q‖⁻¹ • Q - (cc i)⁻¹ • P i‖ ≤ dl K S * th i := by
      have hrev : ‖‖QR‖⁻¹ • QR - ‖PR‖⁻¹ • PR‖ = ‖‖PR‖⁻¹ • PR - ‖QR‖⁻¹ • QR‖ :=
        norm_sub_rev _ _
      have h1 := htri3 (‖Q‖⁻¹ • Q) (‖QR‖⁻¹ • QR) ((cc i)⁻¹ • P i)
      have h2 := htri3 (‖QR‖⁻¹ • QR) (‖PR‖⁻¹ • PR) ((cc i)⁻¹ • P i)
      rw [hrev] at h2
      have hexp : dl K S * th i
          = da * th i + db * th i + 2 * C₁ * th i + C₁ * th i + dp * th i := by
        rw [hdlapp K S, hdadef, hdbdef, hdpdef, hRadef, hRbdef, hm0def]; ring
      rw [hexp]
      linarith only [h1, h2, hdQQR, hdPRQR, hPRdir]
    have hnfin : |‖Q‖ - cc i| ≤ dl K S * th i ^ 2 := by
      have h1 := abs_sub_le ‖Q‖ ‖QR‖ (cc i)
      have h2 := abs_sub_le ‖QR‖ ‖PR‖ (cc i)
      have h3 := abs_sub_le ‖Q‖ ‖Qm‖ ‖QR‖
      have h4 : |‖QR‖ - ‖Qm‖| = |‖Qm‖ - ‖QR‖| := abs_sub_comm _ _
      have h5 : |‖QR‖ - ‖PR‖| = |‖PR‖ - ‖QR‖| := abs_sub_comm _ _
      have h6 := abs_sub_le ‖Q‖ ‖QA‖ ‖Qm‖
      have h7 := abs_sub_le ‖QR‖ ‖QB‖ ‖Qm‖
      have hexp : dl K S * th i ^ 2
          = da * th i ^ 2 + db * th i ^ 2 + 2 * C₁ * th i ^ 2
            + C₁ * th i ^ 2 + dp * th i ^ 2 := by
        rw [hdlapp K S, hdadef, hdbdef, hdpdef, hRadef, hRbdef, hm0def]; ring
      rw [hexp]
      linarith only [h1, h2, h3, h4, h5, h6, h7, gA2, gB2, gD2, hQAnrm, hQBnrm, hPRnrm]
    -- `NormalizedSlopeCoefficients`, through `hcoeff`
    have hdl0 : 0 ≤ dl K S := by
      have hla : (0 : ℝ) ≤ Real.log Ra := Real.log_nonneg (by linarith only [hRa2])
      have hlb : (0 : ℝ) ≤ Real.log Rb := Real.log_nonneg (by linarith only [hRb2])
      have hlp : (0 : ℝ) ≤ Real.log (Rad K) :=
        Real.log_nonneg (by linarith only [hRad2 K hK])
      have hexp : dl K S = da + db + 2 * C₁ + C₁ + dp := by
        rw [hdlapp K S, hdadef, hdbdef, hdpdef, hRadef, hRbdef, hm0def]
      rw [hexp, hdadef, hdbdef, hdpdef]
      have ha : (0 : ℝ) ≤ Cdc * (1 + Real.log Ra) :=
        mul_nonneg hCdc0 (by linarith only [hla])
      have hb : (0 : ℝ) ≤ Cdc * (1 + Real.log Rb) :=
        mul_nonneg hCdc0 (by linarith only [hlb])
      have hp : (0 : ℝ) ≤ C₂ * (1 + Real.log (Rad K)) :=
        mul_nonneg hC₂0 (by linarith only [hlp])
      linarith only [ha, hb, hp, hC₁1]
    obtain ⟨p', q', heq, hbd⟩ := hcoeff i hi2 Q (dl K S) hdl0 hQl hQu hdfin hnfin
    rw [hthsq] at hQfit
    exact ⟨Q, p', q', hQfit, heq, le_trans hbd (le_max_right _ _)⟩
  exact ⟨CR, ifitR, CN, ifitN, hCR0, hifitR, henclR, hCN0, hifitN, hnearbyN⟩
