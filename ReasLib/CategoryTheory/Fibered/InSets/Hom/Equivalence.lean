module

public import ReasLib.CategoryTheory.Fibered.InSets.Hom.OneCell
public import ReasLib.CategoryTheory.Bicategory.InducedBicategory.Iso
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Comparison isomorphisms of set-fibred morphisms

The explicit comparison between composite total functors and the total functor of a composite.
-/

@[expose] public section

universe u v w vS

namespace CategoryTheory

open ObjectProperty

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

variable {X Y : FiberedCategoryOver.Sets C}

/-- The explicit natural isomorphism from the composite of the total functors underlying two
set-fibred morphisms to the total functor underlying their composite. -/
@[stacks 04S8 "total-functor composition for categories fibred in sets"]
def toFunctor.compIso
    {Z : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (G : Y ⟶ Z) :
    toFunctor F ⋙ toFunctor G ≅ toFunctor (F ≫ G) :=
  ObjectProperty.FullSubbicategory.toFunctor.compIso F G

/-- The forward components of `toFunctor.compIso` are identities. -/
@[simp, stacks 04S8 "set-fibred total-functor composition forward component"]
theorem toFunctor.compIso.hom.app
    {Z : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (G : Y ⟶ Z) (x : X.total) :
    (toFunctor.compIso F G).hom.app x =
      𝟙 ((toFunctor G).obj ((toFunctor F).obj x)) := sorry

/-- The inverse components of `toFunctor.compIso` are identities. -/
@[simp, stacks 04S8 "set-fibred total-functor composition inverse component"]
theorem toFunctor.compIso.inv.app
    {Z : FiberedCategoryOver.Sets C} (F : X ⟶ Y) (G : Y ⟶ Z) (x : X.total) :
    (toFunctor.compIso F G).inv.app x =
      𝟙 ((toFunctor G).obj ((toFunctor F).obj x)) := sorry

end FiberedCategoryOver.Sets

end CategoryTheory
