module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.MapArrow.Computations

/-!
# `2`-cell computations for the fibred-to-based pseudo-comma facade
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- Forgetting a pseudo-comma `2`-morphism applies `toBased` to its left endpoint cell. -/
@[simp]
theorem toBased.map₂.left
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    Bicategory.PseudoComma.left₂ ((toBased C).map₂ eta) =
      (FiberedCategoryOver.toBased C).map₂ (Bicategory.PseudoComma.left₂ eta) := sorry

/-- Forgetting a pseudo-comma `2`-morphism applies `toBased` to its right endpoint cell. -/
@[simp]
theorem toBased.map₂.right
    {S T : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))}
    {f g : S ⟶ T} (eta : f ⟶ g) :
    Bicategory.PseudoComma.right₂ ((toBased C).map₂ eta) =
      (FiberedCategoryOver.toBased C).map₂ (Bicategory.PseudoComma.right₂ eta) := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
