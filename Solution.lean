module

public import InfHarmonic

/-!
# Proofs of the Challenge statements

Each declaration below has exactly the statement of its counterpart in `Challenge.lean`
and is proved by the corresponding result of the `InfHarmonic` development. Comparator
checks the statements agree and that only `propext`, `Classical.choice` and `Quot.sound`
are used.
-/

@[expose] public section

open Metric Set

namespace InfHarmonic

theorem main_estimate (d : ℕ) (hd : 3 ≤ d) :
    ∃ α C : ℝ, 0 < α ∧ α ≤ 1 / 3 ∧ 0 < C ∧
      ∀ u : EuclideanSpace ℝ (Fin d) → ℝ,
        IsInfHarmonicOn (ball 0 1) u →
        BddAbove (u '' ball 0 1) → BddBelow (u '' ball 0 1) →
        ∃ g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
          (∀ x ∈ ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2), HasGradientAt u (g x) x) ∧
          BddAbove ((fun x => ‖g x‖) '' ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2)) ∧
          BddAbove (HolderQuotSet g α (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))) ∧
          sSup ((fun x => ‖g x‖) '' ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
              + HolderSeminormOn g α (ball (0 : EuclideanSpace ℝ (Fin d)) (1 / 2))
            ≤ C * OscOn u (ball 0 1) :=
  MainEstimate d hd

theorem interior_C1 (d : ℕ) (hd : 3 ≤ d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hconn : IsConnected Ω) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : IsInfHarmonicOn Ω u) : ContDiffOn ℝ 1 u Ω :=
  InteriorC1 d hd Ω hconn u hu

theorem liouville {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : IsFitClass C₀ v) : IsSpaceTimeAffine v :=
  Liouville C₀ hC₀ v hv

end InfHarmonic
