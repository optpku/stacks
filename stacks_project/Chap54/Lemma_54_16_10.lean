module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.QuasiProjective

/-- Lemma 54.16.10: for a Noetherian scheme `S`, a separated finite-type morphism
`f : X ⟶ S` with regular source of topological Krull dimension `2` is quasi-projective. -/
@[stacks 0C5N]
theorem instOfRegularDimensionTwo
    {X S : Scheme.{u}} [IsNoetherian S] (f : X ⟶ S) [IsSeparated f]
    [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (h_dim : topologicalKrullDim X = 2) : QuasiProjective f := sorry

end AlgebraicGeometry.QuasiProjective
