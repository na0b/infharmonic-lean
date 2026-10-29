module

public import InfHarmonic.Preamble

@[expose] public section
open Set

/-- An attained partial supremum of a jointly concave function is concave.  Let `Φ` be
concave on a product of two real vector spaces and let `Λ` be an upper bound for `Φ(x, ·)`
that is attained at each `x`.  Then `Λ` is concave.  Attainment is exactly the hypothesis
available in the intended use -- the supremum defining a quadratic envelope is attained at
every centre -- and it is what lets the proof apply joint concavity to a pair of
maximizing points rather than argue with suprema. -/
theorem PartialSupConcaveOfAttained {E G : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup G] [Module ℝ G]
    (Φ : E × G → ℝ) (hΦ : ConcaveOn ℝ (Set.univ : Set (E × G)) Φ) (Λ : E → ℝ)
    (hle : ∀ (x : E) (y : G), Φ (x, y) ≤ Λ x)
    (hat : ∀ x : E, ∃ y : G, Λ x = Φ (x, y)) :
    ConcaveOn ℝ (Set.univ : Set E) Λ := by
  refine ⟨convex_univ, fun x₀ _ x₁ _ a b ha hb hab => ?_⟩
  -- pick a maximizing second coordinate over each endpoint
  obtain ⟨y₀, hy₀⟩ := hat x₀
  obtain ⟨y₁, hy₁⟩ := hat x₁
  -- joint concavity along the segment joining the two maximizing pairs
  have hjoint := hΦ.2 (Set.mem_univ (x₀, y₀)) (Set.mem_univ (x₁, y₁)) ha hb hab
  have hpt : a • (x₀, y₀) + b • (x₁, y₁) = ((a • x₀ + b • x₁ : E), (a • y₀ + b • y₁ : G)) :=
    rfl
  rw [hpt] at hjoint
  -- the combined pair is one competitor for the partial supremum at the combined point
  calc a • Λ x₀ + b • Λ x₁ = a • Φ (x₀, y₀) + b • Φ (x₁, y₁) := by rw [hy₀, hy₁]
    _ ≤ Φ ((a • x₀ + b • x₁ : E), (a • y₀ + b • y₁ : G)) := hjoint
    _ ≤ Λ (a • x₀ + b • x₁) := hle _ _
