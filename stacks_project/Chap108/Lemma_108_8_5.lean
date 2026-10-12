/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_33_2_RelativeDimension
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap108.Lemma_108_8_3_Map
public import stacks_project.Chap108.Lemma_108_8_5_Smooth

/-!
# Lemma 108.8.5

If `f : X ⟶ B` is flat, proper, and of finite presentation and has relative
dimension at most `1`, then the structure morphism of the Picard stack over `B`
is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.8.5: if `f : X ⟶ B` is flat, proper, and of finite presentation
and has relative dimension at most `1`, then the structure morphism
`toBase f : (picardStack f).toGroupoids ⟶ Classifying.toGroupoids B` of the
Picard stack is smooth. -/
@[stacks 0DPJ]
instance instSmooth_toBase (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] [RelativeDimensionLE f 1] : CohStack.Hom.Smooth (toBase f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
