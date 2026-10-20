module

public import stacks_project.Chap66.Definition_66_9_2_Dimension
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Dimension
import StacksCheckRecall

/-!
# Dimension of decent algebraic spaces

On a decent algebraic space, étale-local dimension agrees with the topological
Krull dimension of the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.12.5 (1): Dimension at a point of a decent algebraic space equals
the local topological Krull dimension of its space of points. -/
@[stacks 0A4J]
#check (AlgebraicGeometry.AlgebraicSpace.dimensionAt_eq_topologicalKrullDimAt_of_isDecent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X] (x : Points X),
    dimensionAt x = topologicalKrullDimAt x)

/- Lemma 68.12.5 (2): Dimension of a decent algebraic space equals the
topological Krull dimension of its space of points. -/
@[stacks 0A4J]
#check (AlgebraicGeometry.AlgebraicSpace.dimension_eq_topologicalKrullDim_of_isDecent :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X],
    dimension X = topologicalKrullDim (Points X))

end AlgebraicGeometry.AlgebraicSpace
