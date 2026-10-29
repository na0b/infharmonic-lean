-- Preamble: shared Mathlib imports for all files.
-- Imports and comments only (see FILESPEC.md); never `import Mathlib`.

-- Second-order calculus, gradients and C^2 test functions.
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

-- Euclidean and L^2-product inner-product structures; space-time is
-- `WithLp 2 (F x R)` and the jet product space is `PiLp 2`.
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.ProdL2

-- The extended reals, used for the envelope Hamiltonian `H_f` with values
-- in `[-infinity, infinity)`, and upper semicontinuity.
import Mathlib.Data.EReal.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Defs

-- Locally uniform convergence of blow-up and rescaled families.
import Mathlib.Topology.UniformSpace.UniformConvergence

-- Distance to the boundary of the admissible region `G`.
import Mathlib.Topology.MetricSpace.HausdorffDistance

-- Real powers, logarithms and square roots appearing in the flatness
-- modulus, the logarithmic parameter bounds and the anisotropic scaling.
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Sqrt

-- Convexity: convex functions on a set, used for semiconvexity and for the
-- sup-convolution regularization behind the theorem of sums.
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Continuous

-- Rademacher's theorem and the area-formula inequality, the two analytic
-- engines behind the a.e. second-order expansion of a semiconvex function and
-- behind Jensen's lemma.
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Convex.Approximation

-- The mean value / fundamental theorem of calculus along a segment, used to
-- integrate the gradient of the Moreau envelope.
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

-- Second-order Taylor expansion with Peano remainder, and the symmetry of the
-- second derivative of a twice continuously differentiable function.
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

-- Section 6.2 probability: filtrations, martingales and submartingales,
-- Doob's weak-type maximal inequality, optional stopping and sampling, the
-- fair-sign product measure, weak convergence (Portmanteau) and tightness
-- (Prokhorov), the layer-cake identity, and conditional Jensen for the norm.
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.OptionalStopping
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

-- The finite-dimensional spectral theorem and the Neumann series, used in the
-- sup-convolution regularization behind the theorem of sums.
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.SpecificLimits.Normed
