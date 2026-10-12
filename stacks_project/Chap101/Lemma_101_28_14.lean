/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap94.Lemma_94_14_3_Pullback
public import stacks_project.Chap101.Definition_101_7_2_QuasiCompact
public import stacks_project.Chap101.Definition_101_28_1_Gerbe

/-!
# Quasi-compactness of object diagonals along gerbes

If a morphism of algebraic stacks makes the source a gerbe over the target,
then quasi-compactness of the object diagonal of the source implies
quasi-compactness of the object diagonal of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.QuasiCompact

/-- Lemma 101.28.14: Let `f : X ⟶ Y` be a morphism of algebraic stacks such
that `X` is a gerbe over `Y`. If the object diagonal `diagonal X` is
quasi-compact, then so is `diagonal Y`. -/
@[stacks 0DQL]
theorem diagonal_of_gerbe {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    [AlgebraicStack (base.{u + 1, u, u + 1} (Over S))]
    (f : X ⟶ Y) [Gerbe f]
    [QuasiCompact (diagonal.{u + 1, u, u + 1} X)] :
    QuasiCompact (diagonal.{u + 1, u, u + 1} Y) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.QuasiCompact
