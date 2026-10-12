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
public import stacks_project.Chap99.Lemma_99_11_7_Pushforward
public import stacks_project.Chap108.Lemma_108_8_5_Smooth
public import stacks_project.Chap108.Lemma_108_9_5_Map

/-!
# Lemma 108.9.5

If `f : X ⟶ B` is flat, proper, and of finite presentation, the structure-sheaf
maps `O_T ⟶ f_{T,*} O_{X_T}` are isomorphisms, and `f` has relative dimension at
most `1`, then the structure morphism of the Picard functor over `B` is smooth.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativePicard
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.9.5: if `f : X ⟶ B` is flat, proper, and of finite presentation,
the maps `O_T ⟶ f_{T,*} O_{X_T}` are isomorphisms for every scheme `T` over `B`,
and `f` has relative dimension at most `1`, then the structure morphism
`toBase f : toGroupoids f ⟶ Classifying.toGroupoids B` of the Picard functor is
smooth. -/
@[stacks 0DPK]
instance instSmooth_toBase (f : X ⟶ B) [Flat f] [FinitePresentation f]
    [Proper f] [Hom.IsIsoBaseChangeStructurePushforward f]
    [RelativeDimensionLE f 1] : CohStack.Hom.Smooth (toBase f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
