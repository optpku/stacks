module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_37_4_Smooth
public import stacks_project.Chap108.Lemma_108_8_3_Map
public import stacks_project.Chap108.Lemma_108_8_3_Valuative

/-!
# Lemma 108.8.3

If `f : X ⟶ B` is smooth in addition to being proper (and, in the standing
setup, flat and of finite presentation), then the structure morphism of the
Picard stack satisfies the existence part of the valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Picard
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.8.3: assume `f : X ⟶ B` is smooth in addition to being proper
(and, in the standing setup of this section, flat and of finite presentation).
Then `toBase f : (picardStack f).toGroupoids ⟶ Classifying.toGroupoids B`
satisfies the existence part of the valuative criterion of Morphisms of
Stacks, Definition 101.39.10. -/
@[stacks 0DNG]
instance toBase.existence (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    [Smooth f] : ValuativeCriterion.Existence (toBase f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
