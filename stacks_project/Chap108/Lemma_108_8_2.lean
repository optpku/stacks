module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap108.Lemma_108_4_2_LocallyOfFinitePresentation
public import stacks_project.Chap108.Lemma_108_4_2_QuasiSeparated
public import stacks_project.Chap108.Lemma_108_8_3_Map

/-!
# Lemma 108.8.2

The structure morphism of the Picard stack over `B` is quasi-separated and
locally of finite presentation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.8.2 (1): the structure morphism `toBase f : (picardStack f).toGroupoids ⟶
Classifying.toGroupoids B` of the Picard stack is quasi-separated. -/
@[stacks 0DMB]
instance instQuasiSeparated_toBase (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] : CohStack.Hom.QuasiSeparated (toBase f) :=
  sorry

/-- Lemma 108.8.2 (2): the structure morphism `toBase f : (picardStack f).toGroupoids ⟶
Classifying.toGroupoids B` of the Picard stack is locally of finite
presentation. -/
@[stacks 0DMB]
instance instLocallyOfFinitePresentation_toBase (f : X ⟶ B) [Flat f]
    [FinitePresentation f] [Proper f] :
    CohStack.Hom.LocallyOfFinitePresentation (toBase f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
