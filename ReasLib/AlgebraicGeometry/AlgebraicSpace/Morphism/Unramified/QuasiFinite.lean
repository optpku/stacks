module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

/-!
# Quasi-finiteness of unramified morphisms of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UnramifiedAt

/-- A morphism of algebraic spaces that is unramified at a point is
quasi-finite at that point. -/
theorem quasiFiniteAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (h : UnramifiedAt f x) : FiniteType.QuasiFiniteAt f x :=
  sorry

end UnramifiedAt

/-- An unramified morphism of algebraic spaces is locally quasi-finite. -/
instance locallyQuasiFinite_of_unramified {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Unramified f] :
    LocallyQuasiFinite f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
