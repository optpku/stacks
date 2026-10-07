module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.StrongTrans.Forget.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Relative.Maps

/-!
# Computations for the stable relative-inertia forgetful transformation

This leaf exposes the object component of the strong transformation.  The underlying functor and
object/morphism formulas are inherited from the neutral relative-inertia forgetful map.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma.forget.strongTrans

variable {C : Type u} [Category.{v} C]

variable
    {S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, max w vS, vS} C))}

/-- The stable relative-inertia forgetful component is the canonical fibred forgetful map. -/
@[simp]
theorem app :
    (FiberedCategoryOver.RelativeInertia.pseudoComma.forget.strongTrans C).app S =
      FiberedCategoryOver.RelativeInertia.forget S.hom := sorry

/-- The underlying based functor of the stable forgetful component is the neutral one. -/
@[simp]
theorem app.toBasedFunctor :
    FiberedCategoryOver.toBasedFunctor
        ((FiberedCategoryOver.RelativeInertia.pseudoComma.forget.strongTrans C).app S) =
      BasedCategory.RelativeInertia.forget
        (FiberedCategoryOver.toBasedFunctor S.hom) := sorry

/-- The total functor of the stable forgetful component is the neutral one. -/
@[simp]
theorem app.toFunctor :
    FiberedCategoryOver.toFunctor
        ((FiberedCategoryOver.RelativeInertia.pseudoComma.forget.strongTrans C).app S) =
      CategoryTheory.RelativeInertia.forget
        (FiberedCategoryOver.toFunctor S.hom) := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma.forget.strongTrans

end CategoryTheory
