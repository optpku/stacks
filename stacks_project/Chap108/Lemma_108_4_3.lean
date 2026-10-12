/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap108.Lemma_108_4_3_Existence
public import stacks_project.Chap108.Lemma_108_4_3_Map

/-!
# Lemma 108.4.3

If `f : X ⟶ B` is proper and of finite presentation, then the structure
morphism of the stack of coherent sheaves satisfies the existence part of the
valuative criterion.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.CohStack
open AlgebraicGeometry.GroupScheme
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- Lemma 108.4.3: if `f : X ⟶ B` is proper as well as of finite presentation,
then `forget f : toGroupoids f ⟶ Classifying.toGroupoids B` satisfies the
existence part of the valuative criterion (Morphisms of Stacks,
Definition 101.39.10). -/
@[stacks 0DM0]
instance instExistence_forget (f : X ⟶ B) [FinitePresentation f] [Proper f] :
    Hom.ValuativeCriterion.Existence (forget f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
