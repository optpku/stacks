/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Monoidal.Closed.Braided
import StacksCheckRecall

@[expose] public section

namespace AlgebraicGeometry.RingedSpace

/- Lemma 20.42.2 (08DJ): the canonical isomorphism
`RHom(K, RHom(L, M)) ≅ RHom(K ⊗ L, M)` is source-order currying in a braided closed
monoidal category. -/
@[stacks 08DJ]
#check @CategoryTheory.MonoidalClosed.internalHomTensorIso

#check @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_left
#check @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_middle
#check @CategoryTheory.MonoidalClosed.internalHomTensorIso_natural_right
#check @CategoryTheory.MonoidalClosed.braidedHomEquiv
#check @CategoryTheory.MonoidalClosed.braidedHomEquiv_symm_apply

end AlgebraicGeometry.RingedSpace
