module

public import stacks_project.Chap76.Lemma_76_26_1_FiberStalkCohenMacaulay
import StacksCheckRecall

/-!
# Étale locality of Cohen--Macaulay fibre stalks of scheme germs
-/

/- Lemma 76.26.1: The property of morphisms of germs of schemes that the local
ring of the fibre is Noetherian and Cohen--Macaulay is étale local on the
source-and-target. -/
@[stacks 0E0U] #check
  (AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkCohenMacaulay_isEtaleLocal :
    AlgebraicGeometry.Scheme.Germ.MorphismProperty.IsEtaleLocal
      AlgebraicGeometry.Scheme.Germ.MorphismProperty.fiberStalkCohenMacaulay)
