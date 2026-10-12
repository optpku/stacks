/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_27_1_FiberStalk
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 76.27.1: The property of morphisms of germs of schemes that the local
ring of the fibre is Noetherian and Gorenstein is étale local on the
source-and-target. -/
@[stacks 0E13]
#check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkGorenstein_isEtaleLocal :
    AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
      AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkGorenstein)
