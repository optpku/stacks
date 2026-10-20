/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Inertia.Functoriality.NatTrans.Construction

/-!
# Computations for the natural-transformation action of inertia

This leaf exposes component, underlying-arrow, naturality, extensionality, local-functor, and
induced-isomorphism formulas without unfolding the concrete action.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory
namespace Inertia

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Evaluation of the induced inertia transformation is the canonical intertwined component. -/
@[simp]
theorem map₂.app {F G : C ⥤ D} (η : F ⟶ G) (X : Inertia C) :
    (map₂ η).app X = map₂.component η X := sorry

/-- Forgetting an induced inertia component recovers the original natural-transformation
component. -/
@[simp]
theorem map₂.app.underlying {F G : C ⥤ D} (η : F ⟶ G) (X : Inertia C) :
    Inertia.hom ((map₂ η).app X) = η.app X.obj := sorry

/-- The underlying arrow of an explicit inertia transformation component is the original
natural-transformation component. -/
@[simp]
theorem map₂.component.underlying {F G : C ⥤ D} (η : F ⟶ G) (X : Inertia C) :
    Inertia.hom (map₂.component η X) = η.app X.obj := sorry

/-- Naturality of the transformation induced on inertia categories, exposed without unfolding
the natural-transformation structure. -/
@[reassoc]
theorem map₂.naturality {F G : C ⥤ D} (η : F ⟶ G)
    {X Y : Inertia C} (f : X ⟶ Y) :
    (map F).map f ≫ (map₂ η).app Y =
      (map₂ η).app X ≫ (map G).map f := sorry

/-- Two induced inertia transformations agree when all of their components agree. -/
theorem map₂.ext {F G : C ⥤ D} {η θ : F ⟶ G}
    (h : ∀ X : Inertia C, (map₂ η).app X = (map₂ θ).app X) :
    map₂ η = map₂ θ := sorry

/-- The object action of the inertia local functor is the induced inertia functor. -/
@[simp]
theorem mapFunctor.obj (F : C ⥤ D) :
    (mapFunctor C D).obj F = map F := sorry

/-- The morphism action of the inertia local functor is the induced inertia natural
transformation. -/
@[simp]
theorem mapFunctor.map {F G : C ⥤ D} (η : F ⟶ G) :
    (mapFunctor C D).map η = map₂ η := sorry

/-- The forward transformation of an induced inertia isomorphism is induced by the forward
transformation of the original isomorphism. -/
@[simp]
theorem mapIso.hom {F G : C ⥤ D} (e : F ≅ G) :
    (mapIso e).hom = map₂ e.hom := sorry

/-- The inverse transformation of an induced inertia isomorphism is induced by the inverse
transformation of the original isomorphism. -/
@[simp]
theorem mapIso.inv {F G : C ⥤ D} (e : F ≅ G) :
    (mapIso e).inv = map₂ e.inv := sorry

/-- The forward component of an induced inertia isomorphism is the canonical intertwined
component. -/
@[simp]
theorem mapIso.hom.app {F G : C ⥤ D} (e : F ≅ G) (X : Inertia C) :
    (mapIso e).hom.app X = map₂.component e.hom X := sorry

/-- The inverse component of an induced inertia isomorphism is the canonical reverse
intertwined component. -/
@[simp]
theorem mapIso.inv.app {F G : C ⥤ D} (e : F ≅ G) (X : Inertia C) :
    (mapIso e).inv.app X = map₂.component e.inv X := sorry

/-- The arrow underlying a forward induced-isomorphism component is the original forward
component. -/
@[simp]
theorem mapIso.hom.app.underlying
    {F G : C ⥤ D} (e : F ≅ G) (X : Inertia C) :
    Inertia.hom ((mapIso e).hom.app X) = e.hom.app X.obj := sorry

/-- The arrow underlying an inverse induced-isomorphism component is the original inverse
component. -/
@[simp]
theorem mapIso.inv.app.underlying
    {F G : C ⥤ D} (e : F ≅ G) (X : Inertia C) :
    Inertia.hom ((mapIso e).inv.app X) = e.inv.app X.obj := sorry

/-- The inertia action sends a reflexive natural isomorphism to a reflexive inertia isomorphism. -/
@[simp]
theorem mapIso.refl (F : C ⥤ D) :
    mapIso (Iso.refl F) = Iso.refl (map F) := sorry

/-- The inertia action commutes with taking the inverse of a natural isomorphism. -/
@[simp]
theorem mapIso.symm {F G : C ⥤ D} (e : F ≅ G) :
    mapIso e.symm = (mapIso e).symm := sorry

/-- The inertia action commutes with composing natural isomorphisms. -/
@[simp]
theorem mapIso.trans {F G H : C ⥤ D} (e : F ≅ G) (e' : G ≅ H) :
    mapIso (e ≪≫ e') = mapIso e ≪≫ mapIso e' := sorry

end Inertia
end CategoryTheory
