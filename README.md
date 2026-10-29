# Uniform interior C<sup>1,α</sup> estimates for infinity-harmonic functions, in Lean 4

This repository contains a Lean 4 formalization, built on [Mathlib](https://github.com/leanprover-community/mathlib4), of the main results of

> OpenAI,
> *Uniform Interior C<sup>1,α</sup> Estimates for Infinity-Harmonic Functions*,
> OpenAI Math Release preprint, 4 October 2026,
> [openai/math](https://github.com/openai/math/blob/main/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/interior-c1-infinity-harmonic.pdf).

**Formalization:** Juan J. Manfredi, 2026. The paper is by OpenAI; this repository contains only its formalization.

Theorem 1.1, Corollary 1.2 and Theorem 3.1 of the paper are stated and proved, together with everything their proofs use. The development contains no `sorry` and no axioms: every result depends only on the three standard axioms of Lean (`propext`, `Classical.choice`, `Quot.sound`). The formalization follows the paper's argument; no deviation from it was needed.

## Results

| Paper | Lean declaration | File |
|---|---|---|
| Theorem 1.1, the uniform interior estimate | `MainEstimate` (`InfHarmonic.main_estimate` in `Challenge.lean`) | [`MainEstimate.lean`](InfHarmonic/MainEstimate.lean) |
| Corollary 1.2, interior C<sup>1</sup> regularity | `InteriorC1` (`InfHarmonic.interior_C1`) | [`InteriorC1.lean`](InfHarmonic/InteriorC1.lean) |
| Theorem 3.1, the Liouville theorem | `Liouville` (`InfHarmonic.liouville`) | [`Liouville.lean`](InfHarmonic/Liouville.lean) |

## The main theorem

`IsInfHarmonicOn Ω u` says that `u` is continuous on `Ω` and is a viscosity solution of the infinity-Laplace equation Δ<sub>∞</sub>u = 0 there. Theorem 1.1 says that in every dimension d ≥ 3 there are α ∈ (0, 1/3] and C < ∞, depending only on d, such that every bounded infinity-harmonic function on the unit ball has a gradient on the half ball whose supremum and α-Hölder seminorm add up to at most C times the oscillation of the function:

```lean
theorem MainEstimate (d : ℕ) (hd : 3 ≤ d) :
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
            ≤ C * OscOn u (ball 0 1)
```

The two `BddAbove` conclusions are the C<sup>1,α</sup>(B<sub>1/2</sub>) membership: they say that the supremum and the Hölder seminorm, which are defined with `sSup`, are finite. Corollary 1.2 follows:

```lean
theorem InteriorC1 (d : ℕ) (hd : 3 ≤ d) (Ω : Set (EuclideanSpace ℝ (Fin d)))
    (hconn : IsConnected Ω) (u : EuclideanSpace ℝ (Fin d) → ℝ)
    (hu : IsInfHarmonicOn Ω u) : ContDiffOn ℝ 1 u Ω
```

Here `IsConnected Ω` includes nonemptiness, and `Ω` is open because `IsInfHarmonicOn` requires it. Theorem 3.1 is stated for an arbitrary finite-dimensional real inner-product space `F` (the paper's ℝ<sup>m</sup>), with `IsFitClass C₀` the class A<sub>m,C₀</sub> of the paper:

```lean
theorem Liouville (C₀ : ℝ) (hC₀ : 0 ≤ C₀) (v : WithLp 2 (F × ℝ) → ℝ)
    (hv : IsFitClass C₀ v) : IsSpaceTimeAffine v
```

## What is and is not checked by Lean

The Lean kernel checks that the three theorems above follow from their definitions and Mathlib, using only the three standard axioms. Lean does not check that the definitions (`IsInfHarmonicOn`, `HolderSeminormOn`, `OscOn`, `IsFitClass`, …) and the three statements say what the paper says. That was reviewed during the formalization (see below), but readers who rely on the result should compare the statements and the definitions they use against the paper themselves. The definitions are listed in Section 1 of the blueprint.

## Blueprint

The directory [`blueprint/`](blueprint) contains a natural-language statement and a detailed proof for every Lean declaration, cross-referenced to the paper and to each other. They are collected, in dependency order, in [`blueprint/blueprint.pdf`](blueprint/blueprint.pdf). To rebuild it, run `pdflatex blueprint.tex` three times in that directory. The paper itself, in the form that was formalized, is in [`paper/`](paper).

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan), then:

```sh
git clone <repository URL> infharmonic-lean
cd infharmonic-lean
lake exe cache get        # download prebuilt Mathlib
lake build
lake env lean Axioms.lean # print the axioms used by each main result
```

The project is pinned to Lean `v4.35.0-rc2` and the matching Mathlib release `v4.35.0-rc2`, and every file uses Lean's module system. Continuous integration rebuilds the project and checks the axioms on every push.

## Palomar

The repository is laid out for the [Palomar](https://palomar-registry.org/) registry. [`Challenge.lean`](Challenge.lean) is the statement of record: it imports only Mathlib, restates the definitions the main results use, and states the three results with `sorry`. [`Solution.lean`](Solution.lean) proves the same three statements from the development. [`comparator.json`](comparator.json) tells [Comparator](https://github.com/leanprover/comparator) to check that the two agree and that only the three standard axioms are used, and [`formalization.yaml`](formalization.yaml) records provenance, authorship, automation and review. To run the check locally (Linux, needs `bwrap`):

```sh
./scripts/verify-comparator.sh
ruby scripts/validate-formalization.rb
```

The definitions in `Challenge.lean` are copied verbatim into [`InfHarmonic/Defs.lean`](InfHarmonic/Defs.lean), which the development uses; keeping the two textually identical is what makes them elaborate to the same terms.

## Layout

```
InfHarmonic.lean           root module, imports the main results
InfHarmonic/               one file per lemma or theorem; the definitions used in the main
                           statements are in InfHarmonic/Defs.lean
Challenge.lean             Palomar statement of record (Mathlib imports only)
Solution.lean              proofs of the Challenge statements
comparator.json            Comparator configuration
formalization.yaml         Palomar metadata
Axioms.lean                #print axioms for the main results
blueprint/blueprint.tex    natural-language companion (inputs blueprint/nodes/*.tex)
paper/paper.tex            the paper, as formalized
```

## How this formalization was produced

The formalization was produced with [Trellis](https://github.com/wpegden/trellis), an AI-assisted formalization pipeline; the Lean proofs and the blueprint were written by AI agents (Claude, by Anthropic) under the Trellis protocol. Each node was reviewed automatically for soundness of its natural-language proof, for faithfulness to the paper, and for agreement between its Lean statement and its natural-language statement. The Lean kernel checks every proof.

## Citation

Please cite the paper; see [`CITATION.cff`](CITATION.cff).

## License

Apache License 2.0, the license of Mathlib and of [openai/math](https://github.com/openai/math). See [`LICENSE`](LICENSE).
