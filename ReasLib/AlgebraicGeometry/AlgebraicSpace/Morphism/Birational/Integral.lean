module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Birational
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Normal

/-!
# Integral birational morphisms of algebraic spaces

An integral birational morphism of decent algebraic spaces with finitely many
irreducible components is an isomorphism when the target is normal and the
source is reduced.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsBirational

/-- An integral birational morphism between decent algebraic spaces with finitely
many irreducible components is an isomorphism if its source is reduced and its
target is normal. -/
@[stacks 0B4E]
instance (priority := 100) isIso_of_isIntegralHom_of_isNormal
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y]
    [HasFiniteIrreducibleComponents X] [HasFiniteIrreducibleComponents Y]
    [IsReduced X] [IsNormal Y] (f : X ⟶ Y) [IsBirational f] [IsIntegralHom f] :
    IsIso f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsBirational
