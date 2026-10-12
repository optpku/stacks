/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat

/-!
# Descent of local finite type along representable fppf morphisms of algebraic stacks

If `X ⟶ Z` is locally of finite type and `X ⟶ Y` is representable by algebraic
spaces, surjective, flat, and locally of finite presentation, then `Y ⟶ Z` is
locally of finite type.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType

/-- Lemma 101.17.7: Let `X ⟶ Y ⟶ Z` be morphisms of algebraic stacks. Assume
`X ⟶ Z` is locally of finite type and that `X ⟶ Y` is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Then
`Y ⟶ Z` is locally of finite type. -/
@[stacks 06U8]
theorem of_comp_of_fppf {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [LocallyOfFiniteType (f ≫ g)]
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f] :
    LocallyOfFiniteType g :=
  sorry

end AlgebraicGeometry.AlgebraicStack.LocallyOfFiniteType
