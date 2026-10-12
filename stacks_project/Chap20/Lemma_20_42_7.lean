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

/- Lemma 20.42.7 (0A8W): the canonical map
`K ⟶ RHom(L, K ⊗ L)` is the tensor/internal-Hom unit in any braided closed monoidal
category. -/
@[stacks 0A8W]
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit

#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_spec
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_left
#check @CategoryTheory.MonoidalClosed.tensorInternalHomUnit_natural_right

end AlgebraicGeometry.RingedSpace
