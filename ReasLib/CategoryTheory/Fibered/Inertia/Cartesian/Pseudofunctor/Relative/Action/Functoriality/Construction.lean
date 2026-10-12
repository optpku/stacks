/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Action.Construction

/-!
# Functoriality construction for fibred relative inertia

This file packages the local `map₂` action as a hom-category functor and
derives the corresponding map isomorphisms.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}

noncomputable section

/-- Fibred relative inertia acts functorially on each hom category of pseudo-comma squares. -/
def mapFunctor
    (S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    (S ⟶ T) ⥤
      (FiberedCategoryOver.relativeInertia S.hom ⟶
        FiberedCategoryOver.relativeInertia T.hom) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- An invertible pseudo-comma `2`-morphism induces an isomorphism between the corresponding
fibred relative-inertia maps. -/
def mapIso {f g : S ⟶ T} (e : f ≅ g) : map f ≅ map g :=
  (mapFunctor S T).mapIso e

end

end FiberedCategoryOver.RelativeInertia.pseudoComma
end CategoryTheory
