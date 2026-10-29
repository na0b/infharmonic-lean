module

public import InfHarmonic.NormalizedInfFamily
public import InfHarmonic.LinearLift
public import InfHarmonic.InfHarmonicLocLipschitz

@[expose] public section
open Metric Set WithLp

/-- The normalized family `𝒰` is uniformly bounded and has one common
Lipschitz constant on `closedBall 0 (7/8)`. -/
theorem NormalizedFamilyLipschitz (d : ℕ) (hd : 1 ≤ d) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ U : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) → ℝ, NormalizedInfFamily d U →
        (∀ z ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7/8), |U z| ≤ L) ∧
        (∀ a ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7/8),
          ∀ b ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7/8),
            |U a - U b| ≤ L * ‖a - b‖) := by
  -- `hd` is carried by the statement because the paper fixes `d ≥ 1`; the constant
  -- `L = 64` is dimension-free, so the body only has to reference it.
  have _hd : 1 ≤ d := hd
  refine ⟨64, by norm_num, ?_⟩
  intro U hU
  obtain ⟨u, hinf, hu0, hba, hbb, hoscle, hUeq⟩ := hU
  -- The two projection bounds, both from `‖z‖² = ‖y‖² + b²`.  `prod_norm_sq_eq_of_L2`
  -- states the identity in the `z.fst`/`z.snd` form, so each goal is opened with a
  -- `show` in that form: `(ofLp z).1` is definitionally equal but is a distinct atom
  -- for `nlinarith`.
  have hfst : ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖(ofLp z).1‖ ≤ ‖z‖ := by
    intro z
    show ‖z.fst‖ ≤ ‖z‖
    have h := WithLp.prod_norm_sq_eq_of_L2 z
    nlinarith [norm_nonneg z.fst, norm_nonneg z, sq_nonneg ‖z.snd‖]
  have hsnd : ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), |(ofLp z).2| ≤ ‖z‖ := by
    intro z
    show |z.snd| ≤ ‖z‖
    have h := WithLp.prod_norm_sq_eq_of_L2 z
    rw [Real.norm_eq_abs z.snd] at h
    nlinarith [abs_nonneg z.snd, norm_nonneg z, sq_nonneg ‖z.fst‖]
  -- Step 1: `|u| ≤ 1` on `ball 0 1`.  Both suprema are genuine: `NormalizedInfFamily`
  -- carries `BddAbove` and `BddBelow` as explicit conjuncts, so they are destructured
  -- rather than re-derived.
  have hosc : sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1)
      - sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ 1 := by
    simpa only [OscOn] using hoscle
  have hu1 : ∀ y ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1, |u y| ≤ 1 := by
    intro y hy
    have h0mem : (0 : EuclideanSpace ℝ (Fin d)) ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 :=
      mem_ball_self one_pos
    have hsupy : u y ≤ sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      le_csSup hba ⟨y, hy, rfl⟩
    have hsup0 : u 0 ≤ sSup (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) :=
      le_csSup hba ⟨0, h0mem, rfl⟩
    have hinfy : sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ u y :=
      csInf_le hbb ⟨y, hy, rfl⟩
    have hinf0 : sInf (u '' ball (0 : EuclideanSpace ℝ (Fin d)) 1) ≤ u 0 :=
      csInf_le hbb ⟨0, h0mem, rfl⟩
    rw [abs_le]
    constructor <;> linarith
  -- Step 2: the pointwise bound `|U| ≤ 2` on the closed ball of radius `15/16`.
  have hstep2 : ∀ z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ), ‖z‖ ≤ 15/16 → |U z| ≤ 2 := by
    intro z hz
    have hy : (ofLp z).1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      rw [mem_ball, dist_zero_right]
      have := hfst z
      linarith
    have ha := abs_le.mp (hu1 _ hy)
    have hb := abs_le.mp (hsnd z)
    rw [hUeq z, abs_le]
    constructor <;> linarith
  refine ⟨?_, ?_⟩
  · -- the uniform bound on `closedBall 0 (7/8)`, since `7/8 ≤ 15/16` and `2 ≤ 64`
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    have := hstep2 z (by linarith)
    linarith
  · -- Step 3: `U` is infinity-harmonic on the lifted domain `B₁ × ℝ`.
    have hUfun : (fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) =>
        u (ofLp z).1 + (ofLp z).2) = U := funext (fun z => (hUeq z).symm)
    have hUinf : IsInfHarmonicOn
        ((fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp z).1) ⁻¹'
          ball (0 : EuclideanSpace ℝ (Fin d)) 1) U := by
      rw [← hUfun]
      exact LinearLift (ball (0 : EuclideanSpace ℝ (Fin d)) 1) u hinf
    -- Step 4: `InfHarmonicLocLipschitz` at `z₀ = 0`, `ρ = 7/8`, `σ = 1/16`, `Λ = 64`.
    have hsub : closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7/8 + 1/16) ⊆
        (fun z : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ) => (ofLp z).1) ⁻¹'
          ball (0 : EuclideanSpace ℝ (Fin d)) 1 := by
      intro z hz
      rw [mem_closedBall, dist_zero_right] at hz
      show (ofLp z).1 ∈ ball (0 : EuclideanSpace ℝ (Fin d)) 1
      rw [mem_ball, dist_zero_right]
      have := hfst z
      linarith
    -- the oscillation hypothesis, and the arithmetic is exactly tight: `4 = 64 * (1/16)`
    have hoscH : ∀ a ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7/8 + 1/16),
        ∀ b ∈ closedBall (0 : WithLp 2 (EuclideanSpace ℝ (Fin d) × ℝ)) (7/8 + 1/16),
        |U a - U b| ≤ 64 * (1/16) := by
      intro a ha b hb
      rw [mem_closedBall, dist_zero_right] at ha hb
      have h1 := abs_le.mp (hstep2 a (by linarith))
      have h2 := abs_le.mp (hstep2 b (by linarith))
      rw [abs_le]
      constructor <;> linarith
    exact InfHarmonicLocLipschitz _ U hUinf 0 (7/8) (1/16) 64 (by norm_num) (by norm_num)
      hsub hoscH
