module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType

/-!
# Local finite type of unramified morphisms of algebraic spaces

Every unramified morphism of algebraic spaces is locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An unramified morphism of algebraic spaces is locally of finite type. -/
instance locallyOfFiniteType_of_unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Unramified f] : LocallyOfFiniteType f where
  of_etale a b h ha hb w :=
    AlgebraicGeometry.Unramified.locallyOfFiniteType (Unramified.spec f a b h ha hb w)

end AlgebraicGeometry.AlgebraicSpace
