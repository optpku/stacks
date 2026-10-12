/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.Relative.ToBased.Construction
public import ReasLib.CategoryTheory.Bicategory.Comma.Pseudo.MapArrow.Computations

/-!
# Object computations for the fibred-to-based pseudo-comma facade
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace FiberedCategoryOver.RelativeInertia.pseudoComma

variable {C : Type u} [Category.{v} C]

/-- Forgetting a fibred pseudo-comma object forgets its left endpoint. -/
@[simp]
theorem toBased.obj.left
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    Bicategory.ColaxComma.left ((toBased C).obj S) =
      (FiberedCategoryOver.toBased C).obj (Bicategory.ColaxComma.left S) := sorry

/-- Forgetting a fibred pseudo-comma object forgets its right endpoint. -/
@[simp]
theorem toBased.obj.right
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    Bicategory.ColaxComma.right ((toBased C).obj S) =
      (FiberedCategoryOver.toBased C).obj (Bicategory.ColaxComma.right S) := sorry

/-- Forgetting a fibred pseudo-comma object retains its structural arrow as the underlying
based functor. -/
@[simp]
theorem toBased.obj.hom
    (S : Bicategory.PseudoComma
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))
      (Pseudofunctor.id (FiberedCategoryOver.{u, v, w, vS} C))) :
    ((toBased C).obj S).hom =
      (FiberedCategoryOver.toBased C).map S.hom := sorry

end FiberedCategoryOver.RelativeInertia.pseudoComma

end CategoryTheory
