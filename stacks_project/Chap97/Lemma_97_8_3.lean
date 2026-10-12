/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap97.Definition_97_8_1_Algebraic

/-!
# Algebraic morphisms out of algebraic stacks

A 1-morphism of stacks in groupoids over `(Sch/S)_fppf` out of an algebraic
stack is algebraic when the target diagonal is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 97.8.3: Let `S` be a scheme. Let `F : X ⟶ Y` be a 1-morphism of
stacks in groupoids over `(Sch/S)_fppf`. If `X` is an algebraic stack and
`Δ : Y ⟶ Y × Y` is representable by algebraic spaces, then `F` is algebraic. -/
@[stacks 06CG]
theorem Algebraic.of_algebraicStack
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X]
    [IsStack.InGroupoids (Scheme.fppfTopology.over S) Y.p]
    (F : X ⟶ Y)
    (hY : relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)) :
    Algebraic F :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
