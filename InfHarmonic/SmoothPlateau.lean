module

public import InfHarmonic.Preamble
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

@[expose] public section
open Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A `C²` radial plateau: a function on `E` with values in `[m, M]` that is
constantly `m` on the closed ball of radius `ρ₁` and constantly `M` outside the
ball of radius `ρ₂`.  This is the localizing factor `B` of the three-point
estimate, which must be `C²` so that it can enter a `C²` test, be bounded below
by its inner value everywhere, and take a large value far from the origin. -/
theorem SmoothPlateau (m M ρ₁ ρ₂ : ℝ) (hρ₁ : 0 < ρ₁) (hρ : ρ₁ < ρ₂) (hmM : m ≤ M) :
    ∃ B : E → ℝ, ContDiff ℝ 2 B ∧
      (∀ c : E, m ≤ B c ∧ B c ≤ M) ∧
      (∀ c : E, ‖c‖ ≤ ρ₁ → B c = m) ∧
      (∀ c : E, ρ₂ ≤ ‖c‖ → B c = M) := by
  set φ : ContDiffBump (0 : E) := ⟨ρ₁, ρ₂, hρ₁, hρ⟩ with hφ
  refine ⟨fun c => M + (m - M) * φ c, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.add (contDiff_const.mul φ.contDiff)
  · intro c
    have h0 := φ.nonneg' c
    have h1 := φ.le_one (x := c)
    exact ⟨by nlinarith, by nlinarith⟩
  · intro c hc
    have h : φ c = 1 := φ.one_of_mem_closedBall (by simpa [mem_closedBall, dist_eq_norm] using hc)
    simp [h]
  · intro c hc
    have h : φ c = 0 := φ.zero_of_le_dist (by simpa [dist_eq_norm] using hc)
    simp [h]
