/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap99.Lemma_99_12_1_Mor
public import stacks_project.Chap108.Lemma_108_5_1_ClosedImmersion

/-!
# Lemma 108.10.1

The relative diagonal of the functor of relative morphisms `Mor_B(Y, X)` over
`B` is a closed immersion of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- Lemma 108.10.1 (1): the diagonal of Mor_B(Y, X) ⟶ B is a closed immersion. -/
@[stacks 0DPM]
theorem isClosedImmersion_diagonal (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    Quot.IsClosedImmersionOnSchemesOver (Limits.diag (mor y x)) :=
  sorry

/-- Lemma 108.10.1 (2): the diagonal of Mor_B(Y, X) ⟶ B is of finite
presentation. -/
@[stacks 0DPM]
theorem finitePresentation_diagonal (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [Separated x] [FinitePresentation x] :
    Quot.IsFinitePresentationOnSchemesOver (Limits.diag (mor y x)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
