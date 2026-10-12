/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Definition_87_25_1_Surjective

/-!
# Composition of surjective morphisms of formal algebraic spaces

The composition of two surjective morphisms of formal algebraic spaces is
again surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Surjective

/-- Lemma 87.25.2: The composition of two surjective morphisms of formal
algebraic spaces is a surjective morphism. -/
@[stacks 0GHQ]
instance comp {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y] [IsFormalAlgebraicSpace Z]
    [Reduction X] [Reduction Y] [Reduction Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [Surjective g] :
    Surjective (f ≫ g) :=
  sorry

end Surjective

end AlgebraicGeometry.FormalAlgebraicSpace
