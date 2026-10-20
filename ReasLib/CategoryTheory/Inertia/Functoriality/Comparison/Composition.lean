module

public import ReasLib.CategoryTheory.Inertia.Functoriality.Comparison.IdentityComposition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition comparison for inertia functoriality

This leaf owns the explicit composition comparison of the raw inertia action and its componentwise
computation and naturality API.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD uE vE

namespace CategoryTheory
namespace Inertia

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]
variable {E : Type uE} [Category.{vE} E]

namespace mapCompIso

/-- The identity underlying arrow intertwines the two canonical automorphisms obtained by mapping
through a composite functor. -/
theorem app.comm (F : C ⥤ D) (G : D ⥤ E) (X : Inertia C) :
    ((map (F ⋙ G)).obj X).aut.hom ≫
        𝟙 (((map F ⋙ map G).obj X).obj) =
      𝟙 (((map F ⋙ map G).obj X).obj) ≫
        ((map F ⋙ map G).obj X).aut.hom := sorry

/-- The objectwise composition comparison for inertia. Its underlying ambient isomorphism is the
identity between the two explicit composite images. -/
def app (F : C ⥤ D) (G : D ⥤ E) (X : Inertia C) :
    (map (F ⋙ G)).obj X ≅ (map F ⋙ map G).obj X :=
  Inertia.isoMk (Iso.refl _) (app.comm F G X)

/-- The underlying forward arrow of the inertia composition comparison is the identity. -/
@[simp]
theorem app.hom.underlying (F : C ⥤ D) (G : D ⥤ E) (X : Inertia C) :
    Inertia.hom (app F G X).hom =
      𝟙 (((map F ⋙ map G).obj X).obj) := sorry

/-- The underlying inverse arrow of the inertia composition comparison is the identity. -/
@[simp]
theorem app.inv.underlying (F : C ⥤ D) (G : D ⥤ E) (X : Inertia C) :
    Inertia.hom (app F G X).inv =
      𝟙 (((map F ⋙ map G).obj X).obj) := sorry

/-- The explicit composition-comparison components for inertia are natural in inertia morphisms. -/
@[reassoc]
theorem app.naturality
    (F : C ⥤ D) (G : D ⥤ E) {X Y : Inertia C} (f : X ⟶ Y) :
    (map (F ⋙ G)).map f ≫ (app F G Y).hom =
      (app F G X).hom ≫ (map F ⋙ map G).map f := sorry

/-- The inverse composition-comparison components are natural in inertia morphisms. -/
@[reassoc]
theorem app.inv.naturality
    (F : C ⥤ D) (G : D ⥤ E) {X Y : Inertia C} (f : X ⟶ Y) :
    (map F ⋙ map G).map f ≫ (app F G Y).inv =
      (app F G X).inv ≫ (map (F ⋙ G)).map f := sorry

end mapCompIso

/-- The canonical componentwise natural isomorphism witnessing composition preservation by
inertia. -/
def mapCompIso (F : C ⥤ D) (G : D ⥤ E) :
    map (F ⋙ G) ≅ map F ⋙ map G :=
  NatIso.ofComponents
    (mapCompIso.app F G)
    (fun f ↦ mapCompIso.app.naturality F G f)

namespace mapCompIso

/-- The forward component of the inertia composition comparison is its explicit objectwise
comparison. -/
@[simp]
theorem hom.app (F : C ⥤ D) (G : D ⥤ E) (X : Inertia C) :
    (mapCompIso F G).hom.app X = (app F G X).hom := sorry

/-- The inverse component of the inertia composition comparison is the inverse explicit
objectwise comparison. -/
@[simp]
theorem inv.app (F : C ⥤ D) (G : D ⥤ E) (X : Inertia C) :
    (mapCompIso F G).inv.app X = (app F G X).inv := sorry

end mapCompIso

end Inertia
end CategoryTheory
