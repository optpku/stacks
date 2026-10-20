module
public import ReasLib.CategoryTheory.Fibered.Inertia.Sets.RelativeFunctoriality.Map.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Set-fibred relative inertia square comparison

The normalized total-functor isomorphism associated to an invertibly commuting square,
together with its component readouts.
-/
@[expose] public section
universe u v vS w
namespace CategoryTheory
open BasedCategory BasedFunctor
open scoped Bicategory
namespace FiberedCategoryOver.Sets.RelativeInertia
variable {C : Type u} [Category.{v} C]
/-- The total-functor comparison attached to an invertible square (`04Z4`). -/
@[stacks 04Z4 "set-fibred relative-inertia square comparison"]
def map.squareNatIso
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) :
    FiberedCategoryOver.Sets.toFunctor F₁ ⋙ FiberedCategoryOver.Sets.toFunctor G' ≅
      FiberedCategoryOver.Sets.toFunctor G ⋙ FiberedCategoryOver.Sets.toFunctor F₂ :=
  FiberedCategoryOver.Sets.toFunctor.compIso F₁ G' ≪≫
    BasedNatIso.toNatIso (Bicategory.InducedBicategory.Iso.toAmbient comm) ≪≫
      (FiberedCategoryOver.Sets.toFunctor.compIso G F₂).symm
/-- The forward component of the total-functor square comparison is the ambient forward
component of the supplied invertible square. -/
@[simp] theorem map.squareNatIso.hom.app
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) (A : X₁.total) :
    (map.squareNatIso G G' comm).hom.app A =
      (Bicategory.InducedBicategory.Iso.toAmbient comm).hom.toNatTrans.app A := sorry
/-- The inverse component of the total-functor square comparison is the ambient inverse
component of the supplied invertible square. -/
@[simp] theorem map.squareNatIso.inv.app
    {X₁ X₁' X₂ X₂' : FiberedCategoryOver.Sets.{u, v, w, vS} C}
    {F₁ : X₁ ⟶ X₁'} {F₂ : X₂ ⟶ X₂'}
    (G : X₁ ⟶ X₂) (G' : X₁' ⟶ X₂') (comm : F₁ ≫ G' ≅ G ≫ F₂) (A : X₁.total) :
    (map.squareNatIso G G' comm).inv.app A =
      (Bicategory.InducedBicategory.Iso.toAmbient comm).inv.toNatTrans.app A := sorry
end FiberedCategoryOver.Sets.RelativeInertia
end CategoryTheory
