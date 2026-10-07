module

public import ReasLib.AlgebraicTopology.SimplexCategory.Truncated.KanExtension.FiniteInstances
import StacksCheckRecall

/-!
@stack 0185

# Lemma 14.19.4 compatibility facade

Finite limits supply the pointwise right Kan extensions through the neutral truncated-simplex API;
the source map is exactly the counit of the truncation-coskeleton adjunction.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.SimplicialObject

noncomputable section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C] {n : ℕ}
variable (U : SimplicialObject.Truncated C n)

/- Lemma 14.19.4: with finite limits, the counit
`truncation n ((Truncated.cosk n).obj U) ⟶ U` is an isomorphism. -/
@[stacks 0185]
#check (inferInstance : IsIso ((coskAdj n).counit.app U))

/- The componentwise statement is induced by this natural-isomorphism owner. -/
#check (inferInstance : IsIso (coskAdj n).counit)

end CategoryTheory
