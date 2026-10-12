/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Comparison
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Computations
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Fiber.Projection

/-!
# Fibres of based pseudo-pullbacks

This aggregate imports the explicit comparison between a fibre of a based pseudo-pullback and
the categorical pullback of the two corresponding fibres.

The implementation is organized by mathematical layer:

* Comparison.Forward and Comparison.Inverse: the two concrete comparison functors, with
  construction and object/map computations available as separate leaves;
* Equivalence: the explicit unit/counit, `Fiber.comparison.quasiInverse`, canonical equivalence
  instances, and `Fiber.comparison.equivalence`;
* Computations: thin readouts of the quasi-inverse and packaged equivalence;
* Projection.Forward: primitive first- and second-projection isomorphisms for `comparison`;
* Projection.Inverse: inverse-direction isomorphisms derived by equivalence calculus.

The owner-first API is `Fiber.comparison.{unitIso,counitIso,quasiInverse,equivalence}` together
with `Fiber.comparisonInverse`. Projection comparisons are
`Fiber.comparison.{fstIso,sndIso}`; the inverse-direction comparisons are
`Fiber.comparison.equivalence.{inverseFstIso,inverseSndIso}`. Indexed consumers that only need the
actual-to-modeled direction should use `Fiber.comparison` directly rather than unpacking
`Fiber.comparison.equivalence.functor`.

New developments should import the smallest leaf that supplies the required API. This aggregate
remains the stable broad entry point.
-/
