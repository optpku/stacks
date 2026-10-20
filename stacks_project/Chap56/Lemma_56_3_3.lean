module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.EilenbergWatts.Linear
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra TensorProduct

universe u

namespace ModuleCat
namespace EilenbergWatts

/- Lemma 56.3.3

The Stacks Project uses commutative rings and writes modules on the right.  In the
library this convention is represented by `ModuleCat Aᵐᵒᵖ` and `ModuleCat Bᵐᵒᵖ`,
while the coefficient module is viewed through the canonical restriction from
`A ⊗[R] B` to `A ⊗[R] Bᵐᵒᵖ`.
-/
@[stacks 0GNV] #check
  (ModuleCat.EilenbergWatts.commutativeTensorFunctorIsEquivalence :
    ∀ (R A B : Type u) [CommRing R] [CommRing A] [Algebra R A]
      [CommRing B] [Algebra R B],
      (commutativeTensorFunctor R A B).IsEquivalence)

end EilenbergWatts
end ModuleCat
