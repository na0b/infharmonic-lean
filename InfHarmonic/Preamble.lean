module

-- Preamble: shared Mathlib imports for all files.
-- Imports and comments only (see FILESPEC.md); never `import Mathlib`.

-- Second-order calculus, gradients and C^2 test functions.
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

-- Euclidean and L^2-product inner-product structures; space-time is
-- `WithLp 2 (F x R)` and the jet product space is `PiLp 2`.
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.ProdL2

-- The extended reals, used for the envelope Hamiltonian `H_f` with values
-- in `[-infinity, infinity)`, and upper semicontinuity.
public import Mathlib.Data.EReal.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas
public import Mathlib.Topology.Semicontinuity.Defs

-- Locally uniform convergence of blow-up and rescaled families.
public import Mathlib.Topology.UniformSpace.UniformConvergence

-- Distance to the boundary of the admissible region `G`.
public import Mathlib.Topology.MetricSpace.HausdorffDistance

-- Real powers, logarithms and square roots appearing in the flatness
-- modulus, the logarithmic parameter bounds and the anisotropic scaling.
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.Real.Sqrt

-- Convexity: convex functions on a set, used for semiconvexity and for the
-- sup-convolution regularization behind the theorem of sums.
public import Mathlib.Analysis.Convex.Function
public import Mathlib.Analysis.Convex.Continuous

-- Rademacher's theorem and the area-formula inequality, the two analytic
-- engines behind the a.e. second-order expansion of a semiconvex function and
-- behind Jensen's lemma.
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.Analysis.Convex.Approximation

-- The mean value / fundamental theorem of calculus along a segment, used to
-- integrate the gradient of the Moreau envelope.
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- Second-order Taylor expansion with Peano remainder, and the symmetry of the
-- second derivative of a twice continuously differentiable function.
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- Section 6.2 probability: filtrations, martingales and submartingales,
-- Doob's weak-type maximal inequality, optional stopping and sampling, the
-- fair-sign product measure, weak convergence (Portmanteau) and tightness
-- (Prokhorov), the layer-cake identity, and conditional Jensen for the norm.
public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.OptionalStopping
public import Mathlib.Probability.ProductMeasure
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Prokhorov
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.MeasureTheory.Integral.Layercake
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

-- The finite-dimensional spectral theorem and the Neumann series, used in the
-- sup-convolution regularization behind the theorem of sums.
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section
