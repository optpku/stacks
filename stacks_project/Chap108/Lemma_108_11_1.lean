/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap99.Lemma_99_14_8_Groupoids
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty

/-!
# Lemma 108.11.1

The object diagonal of Polarized is separated and of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 108.11.1 (1): the object diagonal
`Δ : Polarized ⟶ Polarized × Polarized` is separated as a morphism
representable by algebraic spaces. -/
@[stacks 0DPT]
theorem has_separated_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.Separated specZ)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

/-- Lemma 108.11.1 (2): the object diagonal
`Δ : Polarized ⟶ Polarized × Polarized` is of finite presentation as a morphism
representable by algebraic spaces. -/
@[stacks 0DPT]
theorem has_finitePresentation_diagonal :
    Groupoids.Hom.has (@AlgebraicSpace.FinitePresentation specZ)
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

end AlgebraicGeometry.Polarized
