module

public import ReasLib.CategoryTheory.Fibered.Inertia.Functoriality.Relative.Action.TwoCell

/-!
# Local hom action of relative inertia

This leaf owns the hom-category functor and the action on invertible pseudo-comma `2`-cells.
-/

@[expose] public section

universe u v u₁ v₁

namespace CategoryTheory
namespace BasedCategory

open BasedCategory BasedFunctor BasedNatIso BasedNatTrans
open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace RelativeInertia
namespace pseudoComma

variable
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
      (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))}

noncomputable section

/-- Relative inertia acts functorially on the hom category of pseudo-comma squares. -/
@[stacks 04Z4 "pseudo-comma relative-inertia local hom functor"]
def mapFunctor (S T : Bicategory.PseudoComma
    (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))
    (Pseudofunctor.id (BasedCategory.{v₁, u₁} C))) :
    (S ⟶ T) ⥤ (relativeInertia S.hom ⥤ᵇ relativeInertia T.hom) where
  obj := map
  map := map₂
  map_id := map₂.id
  map_comp := map₂.comp

/-- An invertible pseudo-comma `2`-morphism induces an isomorphism between the corresponding
relative-inertia maps. -/
@[stacks 04Z4 "pseudo-comma relative-inertia action on invertible 2-morphisms"]
def mapIso {f g : S ⟶ T} (e : f ≅ g) : map f ≅ map g :=
  (mapFunctor S T).mapIso e

end

end pseudoComma
end RelativeInertia
end BasedCategory
end CategoryTheory
