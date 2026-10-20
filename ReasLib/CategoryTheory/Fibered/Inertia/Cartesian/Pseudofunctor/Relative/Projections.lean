module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.Construction

/-!
# Projections of the fibred relative-inertia pseudofunctor

These owner-level formulas identify the lifted pseudofunctor with relative inertia on objects
and with the based relative-inertia pseudofunctor after forgetting fibred structure.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- Before restoring fibred structure, the two-stage construction sends a fibred
pseudo-comma object to the based relative inertia of its structural arrow. -/
@[simp]
theorem basedPseudofunctor.obj
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    (basedPseudofunctor C).obj S =
      BasedCategory.relativeInertia
        (FiberedCategoryOver.toBasedFunctor S.hom) := sorry

/-- The fibred relative-inertia pseudofunctor sends a pseudo-comma object to the relative
inertia of its structural arrow. -/
@[simp]
theorem pseudofunctor.obj
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    (pseudofunctor C).obj S =
      FiberedCategoryOver.relativeInertia S.hom := sorry

/-- The based category underlying the value of fibred relative inertia is the based relative
inertia of the underlying structural functor. -/
@[simp]
theorem pseudofunctor.obj.toBasedCategory
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    ((pseudofunctor C).obj S).toBasedCategory =
      BasedCategory.relativeInertia
        (FiberedCategoryOver.toBasedFunctor S.hom) := sorry

/-- The total category underlying the value of fibred relative inertia is the neutral
relative-inertia category of the total structural functor. -/
@[simp]
theorem pseudofunctor.obj.total
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    ((pseudofunctor C).obj S).total =
      CategoryTheory.RelativeInertia
        (FiberedCategoryOver.toFunctor S.hom) := sorry

/-- The projection underlying the value of fibred relative inertia retains the source
projection on the object underlying each relative-inertia object. -/
@[simp]
theorem pseudofunctor.obj.p
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    ((pseudofunctor C).obj S).p =
      CategoryTheory.RelativeInertia.projection
        (FiberedCategoryOver.toFunctor S.hom)
        (Bicategory.ColaxComma.left S).p := sorry

/-- Forgetting fibred structure after applying fibred relative inertia is exactly the based
relative-inertia pseudofunctor constructed before the two property lifts. -/
@[simp]
theorem pseudofunctor.comp_toBased :
    (pseudofunctor C).comp
        ((FiberedCategoryOver.toBased C :
          StrictPseudofunctor
            (FiberedCategoryOver.{u, v, max w vS, vS} C)
            (BasedCategory.{vS, max w vS} C)).toPseudofunctor) =
      basedPseudofunctor C := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma
end CategoryTheory
