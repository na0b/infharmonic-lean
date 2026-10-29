module

public import InfHarmonic.AsymptEquicontOriginNormalizedLimit

@[expose] public section
set_option maxHeartbeats 500000
open Metric Set Filter Topology WithLp

/-- Step 9 of paper Proposition 3.6 (`NonaffineLimit`): the normalized solutions
have a locally uniformly convergent subsequence with a continuous limit
vanishing at the origin.

Work in `X = ℓ²(ℝ^d × ℝ)` and write `Box K` for the sup box
`{w : |w_x| ≤ K and |w_t| ≤ K}`. The data are the normalized solutions
`v_i : X → ℝ`, an index `i₁`, and the two outputs of Steps 7 and 8, whose
derivations are not repeated here: a bound `A(K)` valid on `Box K` past an
index `i_4(K)`, and the increment estimate at scale `S` --- for `K ≥ 1`,
`S > 0`, `i ≥ i_5(K,S)` and `w ∈ Box K` there are `p'` and `q'` with
`|p'| + |q'| ≤ C_3(K,S)` and `1 + λ_i q' ≥ 1/2` such that
`|v_i(w + (h,l)) - v_i(w) - ⟨p',h⟩ - q' l| ≤ 64 S` for every offset `(h,l)`
with `|l| ≤ S/2` and `|h - (l/(1 + λ_i q')) p'| ≤ S`. It is also assumed that
`v_i(0) = 0` for `i ≥ i₁`.

The conclusion is the whole extraction package: a strictly increasing
`ψ : ℕ → ℕ` with `ψ(j) ≥ i₁`, and a *continuous* `v_∞` with `v_∞(0) = 0`, such
that `v_{ψ(j)} → v_∞` uniformly on every compact subset of `X`. It is produced
by \noderef{AsymptEquicontOriginNormalizedLimit}, which supplies the
subsequence, the continuity of the limit and the value at the origin; what is
proved here are that node's two interface hypotheses.

The first is the uniform bound on a Euclidean ball: since `Box K` is a sup box,
it contains the closed Euclidean ball of the same radius, so the Step 7 bound on
`Box (max 1 ρ)` restricts to `closedBall 0 ρ`.

The second is the asymptotic modulus of continuity. Given `ρ > 0` and
`ε > 0`, put `K = max 1 ρ` and fix the scale `S = ε/128`, so that the estimate's
own error `64 S` is exactly `ε/2`. That fixes the coefficient bound
`C = C_3(K,S)`, and only then is the radius `η` chosen, small enough for three
purposes: `η ≤ S/2` makes the time offset admissible, `η(1 + 2C) ≤ S` makes the
sheared space offset admissible, and `η·4(C+1) ≤ ε` beats the two coefficient
terms `|⟨p',h⟩|` and `|q' l|`, each at most `C η`, by `ε/2` in total. The order
matters: `η` is chosen after `S`, so the `C`-dependence of the third condition
is harmless. The two thresholds are independent --- the cited node carries one
existential index inside each hypothesis --- so the `(K,S)`-dependent threshold
`i_5(K,S)` costs nothing. The ambient space is the Euclidean space-time of
dimension `d + 1`. -/
theorem NonaffineLimitEquicontinuousSubsequence (d : ℕ) (lam : ℕ → ℝ)
    (v : ℕ → WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ) (i₁ : ℕ)
    (Box : ℝ → Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)))
    (Abd : ℝ → ℝ) (ifour : ℝ → ℕ)
    (Cthree : ℝ → ℝ → ℝ) (ifive : ℝ → ℝ → ℕ)
    (hBoxdef : Box = fun K => {w | ‖(ofLp w).1‖ ≤ K ∧ |(ofLp w).2| ≤ K})
    (horigin : ∀ i ≥ i₁, v i 0 = 0)
    (hbound : ∀ K : ℝ, 1 ≤ K → ∀ i ≥ ifour K, ∀ w ∈ Box K, |v i w| ≤ Abd K)
    (hCthree0 : ∀ K S : ℝ, 0 ≤ Cthree K S)
    (hfit : ∀ K : ℝ, 1 ≤ K → ∀ S : ℝ, 0 < S → ∀ i ≥ ifive K S, ∀ w ∈ Box K,
      ∃ (p' : EuclideanSpace ℝ (Fin d)) (q' : ℝ),
        ‖p'‖ + |q'| ≤ Cthree K S ∧ 1 / 2 ≤ 1 + lam i * q' ∧
        ∀ (h : EuclideanSpace ℝ (Fin d)) (l : ℝ), |l| ≤ S / 2 →
          ‖h - (l / (1 + lam i * q')) • p'‖ ≤ S →
          |v i (w + toLp 2 (h, l)) - v i w - (inner ℝ p' h : ℝ) - q' * l|
            ≤ 64 * S) :
    ∃ (psi : ℕ → ℕ) (vlim : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ),
      StrictMono psi ∧ (∀ j, i₁ ≤ psi j) ∧ Continuous vlim ∧
      (∀ K : Set (WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)), IsCompact K →
        TendstoUniformlyOn (fun j => v (psi j)) vlim atTop K) ∧
      vlim 0 = 0 := by
  have hballbox : ∀ (rho : ℝ) (y : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)),
      y ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) rho →
      ‖(ofLp y).1‖ ≤ rho ∧ |(ofLp y).2| ≤ rho := by
    intro rho y hy
    rw [mem_closedBall, dist_zero_right] at hy
    have hsq := WithLp.prod_norm_sq_eq_of_L2 y
    have h1 : ‖y.fst‖ = ‖(ofLp y).1‖ := rfl
    have h2 : ‖y.snd‖ = |(ofLp y).2| := rfl
    rw [h1, h2] at hsq
    have hn : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    exact ⟨by nlinarith only [hsq, hy, hn, norm_nonneg (ofLp y).1, abs_nonneg (ofLp y).2],
      by nlinarith only [hsq, hy, hn, norm_nonneg (ofLp y).1, abs_nonneg (ofLp y).2]⟩
  refine AsymptEquicontOriginNormalizedLimit v i₁ ?_ ?_ horigin
  · -- `hbd` from eq:nl-bound
    intro rho hrho
    refine ⟨Abd (max 1 rho), ifour (max 1 rho), ?_⟩
    intro j hj y hy
    refine hbound (max 1 rho) (le_max_left _ _) j hj y ?_
    rw [hBoxdef]
    obtain ⟨h1, h2⟩ := hballbox rho y hy
    exact ⟨le_trans h1 (le_max_right _ _), le_trans h2 (le_max_right _ _)⟩
  · -- `hequi` from eq:nl-fit, by the ε/2 + ε/2 split
    intro rho hrho eps heps
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = max 1 rho := ⟨_, rfl⟩
    have hK1 : 1 ≤ K := by rw [hKdef]; exact le_max_left _ _
    have hKrho : rho ≤ K := by rw [hKdef]; exact le_max_right _ _
    obtain ⟨S, hSdef⟩ : ∃ S : ℝ, S = eps / 128 := ⟨_, rfl⟩
    have hS0 : 0 < S := by rw [hSdef]; linarith only [heps]
    have h64S : 64 * S = eps / 2 := by rw [hSdef]; ring
    obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = Cthree K S := ⟨_, rfl⟩
    have hC0 : 0 ≤ C := by rw [hCdef]; exact hCthree0 K S
    have h2C0 : (0 : ℝ) < 1 + 2 * C := by linarith only [hC0]
    have hC10 : (0 : ℝ) < 4 * (C + 1) := by linarith only [hC0]
    obtain ⟨eta, hetadef⟩ : ∃ eta : ℝ,
        eta = min (S / 2) (min (S / (1 + 2 * C)) (eps / (4 * (C + 1)))) := ⟨_, rfl⟩
    have heA : eta ≤ S / 2 := by rw [hetadef]; exact min_le_left _ _
    have heB : eta ≤ S / (1 + 2 * C) := by
      rw [hetadef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    have heC : eta ≤ eps / (4 * (C + 1)) := by
      rw [hetadef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    have heta0 : 0 < eta := by
      rw [hetadef]
      exact lt_min (by linarith only [hS0])
        (lt_min (div_pos hS0 h2C0) (div_pos heps hC10))
    have heBm : eta * (1 + 2 * C) ≤ S := (le_div_iff₀ h2C0).mp heB
    have heCm : eta * (4 * (C + 1)) ≤ eps := (le_div_iff₀ hC10).mp heC
    refine ⟨eta, heta0, ifive K S, ?_⟩
    intro j hj y hy y' hy' hdist
    -- both points lie in `Box K`
    have hyb : y ∈ Box K := by
      rw [hBoxdef]
      obtain ⟨h1, h2⟩ := hballbox rho y hy
      exact ⟨le_trans h1 hKrho, le_trans h2 hKrho⟩
    -- the increment, in coordinates
    obtain ⟨p', q', hpq, hA, hinc⟩ := hfit K hK1 S hS0 j hj y hyb
    have hAp : (0 : ℝ) < 1 + lam j * q' := by linarith only [hA]
    have hp'C : ‖p'‖ ≤ C := by
      rw [hCdef]; linarith only [hpq, abs_nonneg q']
    have hq'C : |q'| ≤ C := by
      rw [hCdef]; linarith only [hpq, norm_nonneg p']
    have hrev : ‖y' - y‖ ≤ eta := by rw [norm_sub_rev]; exact hdist
    obtain ⟨hh, hl⟩ := hballbox eta (y' - y)
      (by rw [mem_closedBall, dist_zero_right]; exact hrev)
    have hofs1 : (ofLp (y' - y)).1 = (ofLp y').1 - (ofLp y).1 := rfl
    have hofs2 : (ofLp (y' - y)).2 = (ofLp y').2 - (ofLp y).2 := rfl
    rw [hofs1] at hh
    rw [hofs2] at hl
    have hsum : y + toLp 2 ((ofLp y').1 - (ofLp y).1, (ofLp y').2 - (ofLp y).2) = y' := by
      have h1 : (ofLp (y' - y))
          = ((ofLp y').1 - (ofLp y).1, (ofLp y').2 - (ofLp y).2) := rfl
      calc y + toLp 2 ((ofLp y').1 - (ofLp y).1, (ofLp y').2 - (ofLp y).2)
          = y + toLp 2 (ofLp (y' - y)) := by rw [h1]
        _ = y + (y' - y) := rfl
        _ = y' := by abel
    -- the two domain conditions of eq:nl-fit
    have hdom1 : |(ofLp y').2 - (ofLp y).2| ≤ S / 2 := le_trans hl heA
    have hdom2 : ‖((ofLp y').1 - (ofLp y).1)
        - (((ofLp y').2 - (ofLp y).2) / (1 + lam j * q')) • p'‖ ≤ S := by
      have hsh : ‖(((ofLp y').2 - (ofLp y).2) / (1 + lam j * q')) • p'‖
          ≤ 2 * eta * C := by
        rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_pos hAp]
        have hAb : |(ofLp y').2 - (ofLp y).2| / (1 + lam j * q')
            ≤ 2 * |(ofLp y').2 - (ofLp y).2| := by
          rw [div_le_iff₀ hAp]
          nlinarith only [hA, abs_nonneg ((ofLp y').2 - (ofLp y).2)]
        have h1 : |(ofLp y').2 - (ofLp y).2| / (1 + lam j * q') ≤ 2 * eta := by
          linarith only [hAb, hl]
        have h2 : (0 : ℝ) ≤ |(ofLp y').2 - (ofLp y).2| / (1 + lam j * q') :=
          div_nonneg (abs_nonneg _) (le_of_lt hAp)
        calc |(ofLp y').2 - (ofLp y).2| / (1 + lam j * q') * ‖p'‖
            ≤ |(ofLp y').2 - (ofLp y).2| / (1 + lam j * q') * C :=
              mul_le_mul_of_nonneg_left hp'C h2
          _ ≤ 2 * eta * C := mul_le_mul_of_nonneg_right h1 hC0
      have htri := norm_sub_le ((ofLp y').1 - (ofLp y).1)
        ((((ofLp y').2 - (ofLp y).2) / (1 + lam j * q')) • p')
      nlinarith only [htri, hh, hsh, heBm, heta0, hC0]
    -- the increment estimate, and the two coefficient terms
    have hkey := hinc ((ofLp y').1 - (ofLp y).1) ((ofLp y').2 - (ofLp y).2) hdom1 hdom2
    rw [hsum] at hkey
    have hinn : |(inner ℝ p' ((ofLp y').1 - (ofLp y).1) : ℝ)| ≤ C * eta := by
      have hcs := abs_real_inner_le_norm p' ((ofLp y').1 - (ofLp y).1)
      have h1 : ‖p'‖ * ‖(ofLp y').1 - (ofLp y).1‖ ≤ C * eta :=
        mul_le_mul hp'C hh (norm_nonneg _) hC0
      linarith only [hcs, h1]
    have hql : |q' * ((ofLp y').2 - (ofLp y).2)| ≤ C * eta := by
      rw [abs_mul]
      exact mul_le_mul hq'C hl (abs_nonneg _) hC0
    have hcoef : 2 * (C * eta) ≤ eps / 2 := by
      nlinarith only [heCm, heta0, hC0, heps]
    have hb1 := abs_le.mp hkey
    have hb2 := abs_le.mp hinn
    have hb3 := abs_le.mp hql
    rw [abs_le]
    constructor
    · linarith only [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hcoef, h64S]
    · linarith only [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2, hcoef, h64S]
