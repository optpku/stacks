module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Descent of local finite type for morphisms of algebraic stacks

Local finite type descends along surjective, flat, locally of finite
presentation morphisms from algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- Local finite type of a morphism of algebraic stacks follows from local
finite type of the second projection of a bilimit `PseudoPullbackCone` against
a surjective, flat, locally of finite presentation morphism from an algebraic
space. -/
theorem of_isBilimit_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    {W : AlgebraicSpace S} {g : W.toGroupoids ⟶ Y}
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit)
    [LocallyOfFiniteType c.snd] :
    LocallyOfFiniteType f :=
  sorry

/-- A morphism of algebraic stacks is locally of finite type if its base
change along a surjective, flat, locally of finite presentation morphism from
an algebraic space is locally of finite type. -/
theorem of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Groupoids.Hom.Surjective g] [Groupoids.Hom.Flat g]
    [Groupoids.Hom.LocallyOfFinitePresentation g]
    [LocallyOfFiniteType (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g)] :
    LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
