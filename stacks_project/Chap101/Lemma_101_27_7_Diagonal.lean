/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap101.Lemma_101_17_5_LocallyOfFiniteType
public import stacks_project.Chap101.Definition_101_27_1_FinitePresentation
public import stacks_project.Chap94.Lemma_94_14_3_Pullback

/-!
# Diagonals of finite presentation morphisms of algebraic stacks

The relative 2-diagonal of a locally of finite type morphism of algebraic
stacks is locally of finite presentation. Under quasi-separatedness, the
diagonal is of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace LocallyOfFinitePresentation

/-- The relative 2-diagonal of a locally of finite type morphism of algebraic
stacks is locally of finite presentation. -/
instance diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) := sorry

end LocallyOfFinitePresentation

namespace FinitePresentation

/-- The relative 2-diagonal of a quasi-separated locally of finite type morphism
of algebraic stacks is of finite presentation. -/
instance diagonal {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [QuasiSeparated f] [LocallyOfFiniteType f] :
    FinitePresentation (Hom.diagonal.{u + 1, u, u + 1} f) := sorry

end FinitePresentation

end AlgebraicGeometry.AlgebraicStack
