module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Bicategory.HomotopyCategory.Map
public import ReasLib.CategoryTheory.Fibered.Setoids.Components.Map

/-!
# The presheaf-valued fibrewise-components functor

The map on fibrewise isomorphism classes is invariant under `2`-morphisms, hence defines a
pseudofunctor into a locally discrete bicategory and an ordinary functor from the homotopy
`1`-category. This file owns both constructions and their computation rules.
-/

@[expose] public section

universe u v

namespace CategoryTheory

open Opposite
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Setoids

variable (C) in
/-- Taking fibrewise connected components as a pseudofunctor to the locally discrete bicategory
of set-valued presheaves. The base category is explicit because this global construction has no
value input from which Lean can recover it. -/
@[stacks 04SC "presheaf-valued fibrewise components pseudofunctor"]
noncomputable def componentsPresheaf.pseudofunctor :
    FiberedCategoryOver.Setoids C ⥤ᵖ
      LocallyDiscrete (Cᵒᵖ ⥤ Type (max u v)) where
  obj X := LocallyDiscrete.mk (Functor.fiberIsoClassPresheaf X.p)
  map F := (componentsMap F).toLoc
  map₂ η := eqToHom (congrArg Quiver.Hom.toLoc (componentsMap.eq_of_hom η))
  mapId X := eqToIso (congrArg Quiver.Hom.toLoc (componentsMap.id X))
  mapComp F G := eqToIso (congrArg Quiver.Hom.toLoc (componentsMap.comp F G))

variable (C) in
/-- The ordinary functor from the homotopy `1`-category to set-valued presheaves obtained by
descending the fibrewise-component pseudofunctor. Its base category is explicit for the same
reason as `componentsPresheaf.pseudofunctor`. -/
@[stacks 04SC "presheaf-valued fibrewise components"]
noncomputable def componentsPresheaf :
    Bicategory.HomotopyCategory (FiberedCategoryOver.Setoids C) ⥤
      (Cᵒᵖ ⥤ Type (max u v)) :=
  Bicategory.HomotopyCategory.lift (componentsPresheaf.pseudofunctor C)

/-- The descended presheaf functor sends a represented object to its explicit
fibre-isomorphism-class presheaf. -/
@[simp]
theorem componentsPresheaf.obj (X : FiberedCategoryOver.Setoids C) :
    (componentsPresheaf C).obj (Bicategory.HomotopyCategory.mk X) =
      Functor.fiberIsoClassPresheaf X.p := sorry

/-- On a represented morphism, the descended presheaf functor is the explicit map on fibrewise
connected components. -/
@[simp]
theorem componentsPresheaf.map_mkHom
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    (componentsPresheaf C).map
        (Bicategory.HomotopyCategory.mkHom F) =
      componentsMap F := sorry

/-- The presheaf-valued component pseudofunctor sends an object to its
fibre-isomorphism-class presheaf. -/
@[simp]
theorem componentsPresheaf.pseudofunctor.obj
    (X : FiberedCategoryOver.Setoids C) :
    (componentsPresheaf.pseudofunctor C).obj X =
      LocallyDiscrete.mk (Functor.fiberIsoClassPresheaf X.p) := sorry

/-- The presheaf-valued component pseudofunctor sends a `1`-morphism to its
explicit map on fibrewise isomorphism classes. -/
@[simp]
theorem componentsPresheaf.pseudofunctor.map
    {X Y : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) :
    (componentsPresheaf.pseudofunctor C).map F =
      (componentsMap F).toLoc := sorry

/-- The `2`-cell action of the presheaf-valued component pseudofunctor is the
locally discrete transport induced by `componentsMap.eq_of_hom`. -/
@[simp]
theorem componentsPresheaf.pseudofunctor.map₂
    {X Y : FiberedCategoryOver.Setoids C} {F G : X ⟶ Y} (η : F ⟶ G) :
    (componentsPresheaf.pseudofunctor C).map₂ η =
      eqToHom (congrArg Quiver.Hom.toLoc (componentsMap.eq_of_hom η)) := sorry

/-- The identity comparison of the presheaf-valued component pseudofunctor is induced by the
identity formula for `componentsMap`. -/
@[simp]
theorem componentsPresheaf.pseudofunctor.mapId
    (X : FiberedCategoryOver.Setoids C) :
    (componentsPresheaf.pseudofunctor C).mapId X =
      eqToIso (congrArg Quiver.Hom.toLoc (componentsMap.id X)) := sorry

/-- The composition comparison of the presheaf-valued component pseudofunctor is induced by the
composition formula for `componentsMap`. -/
@[simp]
theorem componentsPresheaf.pseudofunctor.mapComp
    {X Y Z : FiberedCategoryOver.Setoids C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    (componentsPresheaf.pseudofunctor C).mapComp F G =
      eqToIso (congrArg Quiver.Hom.toLoc (componentsMap.comp F G)) := sorry

end FiberedCategoryOver.Setoids

end CategoryTheory
