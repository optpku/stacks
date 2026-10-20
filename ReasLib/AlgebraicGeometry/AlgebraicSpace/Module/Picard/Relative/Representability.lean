module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Picard.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StructureSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Representability
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative Picard functor of a flat, finitely presented, proper morphism
of algebraic spaces is an algebraic space if the canonical structure-sheaf map
`O_T ⟶ f_{T,*} O_{X_T}` is an isomorphism for every scheme over the base. -/
theorem picardFunctor_isAlgebraicSpaceOver {S : Scheme.{u}} {X B : AlgebraicSpace S}
    (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Hom.IsIsoBaseChangeStructurePushforward f] :
    IsAlgebraicSpaceOver (picardFunctor f).obj := sorry

end AlgebraicGeometry.AlgebraicSpace
