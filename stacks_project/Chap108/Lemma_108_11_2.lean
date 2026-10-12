/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import stacks_project.Chap99.Theorem_99_14_15_Algebraicity_of_the_stack_of_polarized_schemes
public import stacks_project.Chap101.Definition_101_4_1_Separation
public import stacks_project.Chap106.Lemma_106_10_1_LocallyOfFinitePresentation
public import stacks_project.Chap107.Situation_107_2_1_Instances

/-!
# Lemma 108.11.2

The structure morphism Polarized ⟶ specZ is quasi-separated and locally of
finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- Lemma 108.11.2 (1): the structure morphism Polarized ⟶ specZ is
quasi-separated. -/
@[stacks 0DPU]
instance instQuasiSeparated_baseProjection :
    AlgebraicStack.QuasiSeparated
      (baseProjection.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

/-- Lemma 108.11.2 (2): the structure morphism Polarized ⟶ specZ is locally of
finite presentation. -/
@[stacks 0DPU]
instance instLocallyOfFinitePresentation_baseProjection :
    AlgebraicStack.LocallyOfFinitePresentation
      (baseProjection.{u + 1, u, u + 1} toGroupoidsOverSpecZ) :=
  sorry

end AlgebraicGeometry.Polarized
