module

public import ReasLib.CategoryTheory.Inertia.Category
import Mathlib.Tactic.CrossRefAttribute

/-!
# Construction of the natural-transformation action of inertia

This leaf owns the component, natural-transformation, local-functor, and isomorphism data for the
ordinary inertia action. Projection formulas and whiskering laws are provided by sibling leaves.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory
namespace Inertia

variable {C : Type uC} [Category.{vC} C]
variable {D : Type uD} [Category.{vD} D]

/-- Naturality of a transformation on an automorphism gives the intertwining equation required
for its component in the inertia category. -/
theorem map₂.component.comm {F G : C ⥤ D} (η : F ⟶ G) (X : Inertia C) :
    ((map F).obj X).aut.hom ≫ η.app X.obj =
      η.app X.obj ≫ ((map G).obj X).aut.hom := sorry

/-- The component on an inertia object of the transformation induced by \`η : F ⟶ G\`. Its
underlying arrow is exactly \`η.app X.obj\`. -/
def map₂.component {F G : C ⥤ D} (η : F ⟶ G) (X : Inertia C) :
    (map F).obj X ⟶ (map G).obj X :=
  homMk (η.app X.obj) (map₂.component.comm η X)

/-- The inertia components induced by a natural transformation are natural in inertia
morphisms. -/
@[reassoc]
theorem map₂.component.naturality {F G : C ⥤ D} (η : F ⟶ G)
    {X Y : Inertia C} (f : X ⟶ Y) :
    (map F).map f ≫ map₂.component η Y =
      map₂.component η X ≫ (map G).map f := sorry

/-- A natural transformation induces a natural transformation between the corresponding
inertia functors. -/
@[stacks 04Z4 "abstract inertia action on natural transformations"]
def map₂ {F G : C ⥤ D} (η : F ⟶ G) : map F ⟶ map G where
  app := map₂.component η
  naturality := fun {_ _} f ↦ map₂.component.naturality η f

/-- The inertia action sends identity natural transformations to identity transformations. -/
@[simp]
theorem map₂.id (F : C ⥤ D) :
    map₂ (𝟙 F) = 𝟙 (map F) := sorry

/-- The inertia action preserves vertical composition of natural transformations. -/
@[simp]
theorem map₂.comp {F G H : C ⥤ D} (η : F ⟶ G) (θ : G ⟶ H) :
    map₂ (η ≫ θ) = map₂ η ≫ map₂ θ := sorry

/-- Inertia is functorial on each functor category. -/
@[stacks 04Z4 "abstract inertia local hom functor"]
def mapFunctor (C : Type uC) [Category.{vC} C]
    (D : Type uD) [Category.{vD} D] :
    (C ⥤ D) ⥤ (Inertia C ⥤ Inertia D) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- A natural isomorphism induces a natural isomorphism between inertia functors. -/
@[stacks 04Z4 "abstract inertia action on natural isomorphisms"]
def mapIso {F G : C ⥤ D} (e : F ≅ G) : map F ≅ map G :=
  (mapFunctor C D).mapIso e

end Inertia
end CategoryTheory
