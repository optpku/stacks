/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_15_2
public import stacks_project.Chap108.Lemma_108_4_8_Algebraic
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation

/-!
# Lemma 109.5.3

The structure morphism of `Curves` is quasi-separated and locally of finite
presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

/-- Lemma 109.5.3 (1): the structure morphism
`CohStack.toIdentitySlice (toGroupoids S) : toGroupoids S ⟶
Classifying.slice (Over.mk (𝟙 S))` of `Curves`, the source morphism
`Curves ⟶ Spec(Z)`, is quasi-separated. -/
@[stacks 0DSS]
instance instQuasiSeparated_toIdentitySlice (S : Scheme.{u}) :
    CohStack.Hom.QuasiSeparated (CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

/-- Lemma 109.5.3 (2): the structure morphism
`CohStack.toIdentitySlice (toGroupoids S) : toGroupoids S ⟶
Classifying.slice (Over.mk (𝟙 S))` of `Curves`, the source morphism
`Curves ⟶ Spec(Z)`, is locally of finite presentation. -/
@[stacks 0DSS]
instance instLocallyOfFinitePresentation_toIdentitySlice (S : Scheme.{u}) :
    CohStack.Hom.LocallyOfFinitePresentation
      (CohStack.toIdentitySlice (toGroupoids S)) :=
  sorry

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
