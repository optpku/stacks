/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction

/-!
# Comparison computations for forgetting fibred pseudo-comma squares

This leaf exposes the endpoint projections of the identity and composition
comparisons of `FiberedCategoryOver.RelativeInertia.pseudoComma.toBased`.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- The forward identity comparison of the forgetful arrow action is the
forward identity comparison of the underlying forgetful pseudofunctor on the
left endpoint. -/
@[simp]
theorem toBased.mapId.hom.left
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    Bicategory.PseudoComma.left₂ ((toBased C).mapId S).hom =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapId
        (Bicategory.ColaxComma.left S)).hom := sorry

/-- The forward identity comparison of the forgetful arrow action is the
forward identity comparison of the underlying forgetful pseudofunctor on the
right endpoint. -/
@[simp]
theorem toBased.mapId.hom.right
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    Bicategory.PseudoComma.right₂ ((toBased C).mapId S).hom =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapId
        (Bicategory.ColaxComma.right S)).hom := sorry

/-- The inverse identity comparison of the forgetful arrow action is the
inverse identity comparison of the underlying forgetful pseudofunctor on the
left endpoint. -/
@[simp]
theorem toBased.mapId.inv.left
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    Bicategory.PseudoComma.left₂ ((toBased C).mapId S).inv =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapId
        (Bicategory.ColaxComma.left S)).inv := sorry

/-- The inverse identity comparison of the forgetful arrow action is the
inverse identity comparison of the underlying forgetful pseudofunctor on the
right endpoint. -/
@[simp]
theorem toBased.mapId.inv.right
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    Bicategory.PseudoComma.right₂ ((toBased C).mapId S).inv =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapId
        (Bicategory.ColaxComma.right S)).inv := sorry

/-- The forward composition comparison of the forgetful arrow action is the
forward composition comparison of the underlying forgetful pseudofunctor on
the left endpoint. -/
@[simp]
theorem toBased.mapComp.hom.left
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.left₂ ((toBased C).mapComp f g).hom =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
        (Bicategory.PseudoComma.left f)
        (Bicategory.PseudoComma.left g)).hom := sorry

/-- The forward composition comparison of the forgetful arrow action is the
forward composition comparison of the underlying forgetful pseudofunctor on
the right endpoint. -/
@[simp]
theorem toBased.mapComp.hom.right
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.right₂ ((toBased C).mapComp f g).hom =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
        (Bicategory.PseudoComma.right f)
        (Bicategory.PseudoComma.right g)).hom := sorry

/-- The inverse composition comparison of the forgetful arrow action is the
inverse composition comparison of the underlying forgetful pseudofunctor on
the left endpoint. -/
@[simp]
theorem toBased.mapComp.inv.left
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.left₂ ((toBased C).mapComp f g).inv =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
        (Bicategory.PseudoComma.left f)
        (Bicategory.PseudoComma.left g)).inv := sorry

/-- The inverse composition comparison of the forgetful arrow action is the
inverse composition comparison of the underlying forgetful pseudofunctor on
the right endpoint. -/
@[simp]
theorem toBased.mapComp.inv.right
    {S T U : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    (f : S ⟶ T) (g : T ⟶ U) :
    Bicategory.PseudoComma.right₂ ((toBased C).mapComp f g).inv =
      ((FiberedCategoryOver.toBased C).toPseudofunctor.mapComp
        (Bicategory.PseudoComma.right f)
        (Bicategory.PseudoComma.right g)).inv := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
