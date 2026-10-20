module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation

/-!
# Representability of locally quasi-finite separated morphisms

A separated morphism of algebraic spaces that is locally of finite type and
chartwise locally quasi-finite is representable by schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated morphism of algebraic spaces that is locally of finite type and
chartwise locally quasi-finite is representable by schemes. Local finite type
together with chartwise local quasi-finiteness expresses the usual locally
quasi-finite condition. -/
theorem relativelyRepresentable_of_locallyQuasiFinite_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [Separated f] :
    yoneda.relativelyRepresentable f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
