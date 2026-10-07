module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Pseudofunctor

/-!
# Cat-level local action for inertia

This leaf exposes the bundled hom-functor and the object-level projections of the strict inertia
pseudofunctor.
-/

@[expose] public section

open CategoryTheory
open Bicategory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace Inertia

/-- On objects, the bundled hom functor sends a functor to its induced inertia functor. -/
@[simp]
theorem catHomFunctor.obj
    {C D : Cat.{v, u}} (F : C ⟶ D) :
    (catHomFunctor C D).obj F =
      (Inertia.map F.toFunctor).toCatHom := sorry

/-- On morphisms, the bundled hom functor sends a natural transformation to its induced inertia
transformation. -/
@[simp]
theorem catHomFunctor.map
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    (catHomFunctor C D).map η =
      (Inertia.map₂ η.toNatTrans).toCatHom₂ := sorry

/-- Forgetting the Cat wrapper from the hom-functor action on a `2`-morphism recovers the induced
inertia natural transformation. -/
@[simp]
theorem catHomFunctor.map.toNatTrans
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    ((catHomFunctor C D).map η).toNatTrans =
      Inertia.map₂ η.toNatTrans := sorry

/-- The component of the hom-functor action on a `2`-morphism is the canonical intertwined
component. -/
@[simp]
theorem catHomFunctor.map.app
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (X : Inertia C) :
    ((catHomFunctor C D).map η).toNatTrans.app X =
      Inertia.map₂.component η.toNatTrans X := sorry

/-- The ambient arrow underlying a hom-functor `2`-cell component is the original component. -/
@[simp]
theorem catHomFunctor.map.app.underlying
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) (X : Inertia C) :
    Inertia.hom (((catHomFunctor C D).map η).toNatTrans.app X) =
      η.toNatTrans.app X.obj := sorry

/-- The hom-functor action on a `2`-morphism is natural in inertia morphisms. -/
@[reassoc]
theorem catHomFunctor.map.naturality
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G)
    {X Y : Inertia C} (f : X ⟶ Y) :
    ((catHomFunctor C D).obj F).toFunctor.map f ≫
        ((catHomFunctor C D).map η).toNatTrans.app Y =
      ((catHomFunctor C D).map η).toNatTrans.app X ≫
        ((catHomFunctor C D).obj G).toFunctor.map f := sorry

/-- The object action of the strict inertia pseudofunctor is the bundled inertia category. -/
@[simp]
theorem strictPseudofunctor.obj (C : Cat.{v, u}) :
    strictPseudofunctor.obj C = Cat.of (Inertia C) := sorry

/-- The local functor of the strict inertia pseudofunctor is the bundled inertia hom functor. -/
@[simp]
theorem strictPseudofunctor.mapFunctor (C D : Cat.{v, u}) :
    strictPseudofunctor.mapFunctor C D = catHomFunctor C D := sorry

/-- The `1`-cell action of the strict inertia pseudofunctor is the bundled induced inertia
functor. -/
@[simp]
theorem strictPseudofunctor.map {C D : Cat.{v, u}} (F : C ⟶ D) :
    strictPseudofunctor.map F =
      (Inertia.map F.toFunctor).toCatHom := sorry

/-- The local functor of the strict inertia pseudofunctor acts by the canonical inertia map. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.obj
    {C D : Cat.{v, u}} (F : C ⟶ D) :
    ((strictPseudofunctor).mapFunctor C D).obj F =
      (Inertia.map F.toFunctor).toCatHom := sorry

/-- The local functor of the strict inertia pseudofunctor acts on `2`-cells by the canonical
induced inertia transformation. -/
@[simp]
theorem strictPseudofunctor.mapFunctor.map
    {C D : Cat.{v, u}} {F G : C ⟶ D} (η : F ⟶ G) :
    ((strictPseudofunctor).mapFunctor C D).map η =
      (Inertia.map₂ η.toNatTrans).toCatHom₂ := sorry

end Inertia
end CategoryTheory
