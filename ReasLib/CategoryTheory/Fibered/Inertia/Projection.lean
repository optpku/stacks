/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fiberedness
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Objects
public import ReasLib.CategoryTheory.Fibered.Inertia.Projection.Fixed

/-!
# Fibred projections of inertia

Aggregate for fibredness of relative-inertia projections, bundled fibred inertia
objects, and the fixed-owner relative-diagonal comparison equivalence. New clients can import the
smallest leaf matching their required layer.
The fibredness layer is further split into `Projection.Fiberedness.{Relative,Based,FiberedCategory}`;
the bundled object owner consumes only the last of these.
Fixed-owner comparison computations are exposed below
`FiberedCategoryOver.RelativeInertia.{relativeDiagonal,diagonalComparison,
diagonalComparison.inverse,diagonalComparisonEquivalence}`.
The neutral fibredness readout is
`RelativeInertia.Projection.Fibered.{ofCartesian,self}`; the historical theorem names and
typeclass instances remain available for compatibility and inference. Based and bundled clients
can use `BasedCategory.Inertia.Projection.Fibered.self` and
`FiberedCategoryOver.RelativeInertia.Projection.Fibered.ofHom` when an explicit term is needed.
-/

@[expose] public section
