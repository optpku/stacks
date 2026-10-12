/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap88.Definition_88_21_1_Formal

/-!
# Cancellation of local finite type against postcomposition

If a composite morphism of formal algebraic spaces is locally of finite type,
then so is the first factor. No hypothesis is imposed on the second factor.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace LocallyOfFiniteType

/-- If a composite morphism of formal algebraic spaces is locally of finite type,
then so is the first factor. -/
theorem of_comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ g)] : LocallyOfFiniteType f := sorry

end LocallyOfFiniteType

end AlgebraicGeometry.FormalAlgebraicSpace
