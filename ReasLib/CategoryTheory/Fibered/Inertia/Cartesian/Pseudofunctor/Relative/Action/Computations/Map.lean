/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Action.Construction

/-!
# Map computations for fibred relative inertia
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

namespace map

/-- Forgetting fibred structure from the pseudo-comma relative-inertia map recovers the based
map induced by the same square. -/
@[simp]
theorem toBasedFunctor (f : S ⟶ T) :
    FiberedCategoryOver.toBasedFunctor (map f) =
      BasedCategory.RelativeInertia.map
        (FiberedCategoryOver.toBasedFunctor (Bicategory.PseudoComma.left f))
        (FiberedCategoryOver.toBasedFunctor (Bicategory.PseudoComma.right f))
        (FiberedCategoryOver.toBasedFunctorIso
          (Bicategory.PseudoComma.cellIso f).symm) := sorry

/-- The total functor of a pseudo-comma relative-inertia map is the neutral relative-inertia
map induced by the underlying square of total functors. -/
@[simp]
theorem toFunctor (f : S ⟶ T) :
    FiberedCategoryOver.toFunctor (map f) =
      CategoryTheory.RelativeInertia.map
        (FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left f))
        (FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.right f))
        (BasedNatIso.toNatIso
          (FiberedCategoryOver.toBasedFunctorIso
            (Bicategory.PseudoComma.cellIso f).symm)) := sorry

/-- A pseudo-comma relative-inertia map applies its left endpoint to the underlying object. -/
@[simp]
theorem obj (f : S ⟶ T)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    ((FiberedCategoryOver.toFunctor (map f)).obj A).obj =
      (FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left f)).obj A.obj := sorry

/-- A pseudo-comma relative-inertia map applies its left endpoint to the selected
automorphism. -/
@[simp]
theorem aut (f : S ⟶ T)
    (A : (FiberedCategoryOver.relativeInertia S.hom).total) :
    ((FiberedCategoryOver.toFunctor (map f)).obj A).aut =
      (FiberedCategoryOver.toFunctor
        (Bicategory.PseudoComma.left f)).mapIso A.aut := sorry

/-- A pseudo-comma relative-inertia map applies its left endpoint to the arrow underlying a
morphism. -/
@[simp]
theorem hom (f : S ⟶ T)
    {A B : (FiberedCategoryOver.relativeInertia S.hom).total} (phi : A ⟶ B) :
    CategoryTheory.RelativeInertia.hom
        ((FiberedCategoryOver.toFunctor (map f)).map phi) =
      (FiberedCategoryOver.toFunctor (Bicategory.PseudoComma.left f)).map
        (CategoryTheory.RelativeInertia.hom phi) := sorry

end map

end FiberedCategoryOver.RelativeInertia.pseudoComma
end CategoryTheory
