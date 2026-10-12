/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap100.Definition_100_5_1_Surjective
public import stacks_project.Chap101.Definition_101_37_1_Proper

/-!
# Cancellation of universal closedness along a surjection

If a morphism of algebraic stacks over a base is surjective and the composite
to the base is universally closed, then the second factor is universally
closed. In particular, a separated finite type second factor is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyClosed

/-- Lemma 101.37.6 (1): if `f : X ⟶ Y` is a surjective morphism of algebraic
stacks over `Z` and `X` is universally closed over `Z`, then `Y` is
universally closed over `Z`. -/
@[stacks 0CQK]
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed (f ≫ g)] [Surjective f] :
    UniversallyClosed g :=
  sorry

end UniversallyClosed

namespace Proper

/-- Lemma 101.37.6 (2): if `f : X ⟶ Y` is a surjective morphism of algebraic
stacks over `Z`, `X` is universally closed over `Z`, and `Y` is separated and
of finite type over `Z`, then `Y` is proper over `Z`. -/
@[stacks 0CQK]
theorem of_comp_surjective {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [UniversallyClosed (f ≫ g)] [Surjective f]
    [Separated g] [FiniteType g] : Proper g :=
  sorry

end Proper

end AlgebraicGeometry.AlgebraicStack
