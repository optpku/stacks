module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Finite presentation morphisms of algebraic spaces are of finite type
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces which is locally of finite presentation is
locally of finite type. -/
instance locallyOfFiniteType_of_locallyOfFinitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f :=
  sorry

/-- A morphism of algebraic spaces of finite presentation is of finite type. -/
instance finiteType_of_finitePresentation {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [FinitePresentation f] :
    FiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
