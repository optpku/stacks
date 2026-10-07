module

public import stacks_project.Chap76.Lemma_76_26_1_FiberStalkCohenMacaulay

/-!
# Étale locality of Cohen--Macaulay fibre stalks of scheme germs
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Germ
namespace MorphismProperty

/-- Lemma 76.26.1: The property of morphisms of germs of schemes that the local
ring of the fibre is Noetherian and Cohen--Macaulay is étale local on the
source-and-target. -/
@[stacks 0E0U]
theorem fiberStalkCohenMacaulay_isEtaleLocal :
    IsEtaleLocal fiberStalkCohenMacaulay := sorry

end MorphismProperty
end AlgebraicGeometry.Scheme.Germ
