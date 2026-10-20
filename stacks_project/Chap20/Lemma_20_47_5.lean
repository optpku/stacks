module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.PseudoCoherent.Tensor
import StacksCheckRecall

@[expose] public section

/- Lemma 20.47.5: pseudo-coherent derived `𝒪_X`-modules are closed under the canonical derived
tensor product.  The reusable statements live in the ringed-space ReasLib owner. -/

open AlgebraicGeometry CategoryTheory
open scoped RingedTensor

universe u

namespace AlgebraicGeometry.RingedSpace

/- The two independent source clauses are recalled separately at their shared canonical owner. -/
@[stacks 09J3 "(1) bounded pseudo-coherent tensor closure"]
#check @ModuleDerived.IsMPseudoCoherent.tensor

@[stacks 09J3 "(2) pseudo-coherent tensor closure"]
#check @ModuleDerived.IsPseudoCoherent.tensor

end AlgebraicGeometry.RingedSpace

end
