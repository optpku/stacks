/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap108.Lemma_108_4_1_Diagonal
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated
public import stacks_project.Chap108.Lemma_108_4_3_Map

/-!
# Lemma 108.4.2

The structure morphism of the stack of coherent sheaves over `B` is
quasi-separated and locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.4.2 (1): the structure morphism `forget f : toGroupoids f ⟶
Classifying.toGroupoids B` of the stack of coherent sheaves is
quasi-separated. -/
@[stacks 0DLZ]
instance instQuasiSeparated_forget (f : X ⟶ B) [FinitePresentation f]
    [Separated f] : Hom.QuasiSeparated (forget f) :=
  sorry

/-- Lemma 108.4.2 (2): the structure morphism `forget f : toGroupoids f ⟶
Classifying.toGroupoids B` of the stack of coherent sheaves is locally of
finite presentation. -/
@[stacks 0DLZ]
instance instLocallyOfFinitePresentation_forget (f : X ⟶ B)
    [FinitePresentation f] [Separated f] :
    Hom.LocallyOfFinitePresentation (forget f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
