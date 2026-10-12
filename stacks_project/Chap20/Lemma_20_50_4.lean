/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]
variable [MonoidalClosed (ModuleDerived X)]

/- Lemma 20.50.4: if `K` is perfect, then the canonical map
`RHom(L, M) ⊗ K ⟶ RHom(RHom(K, L), M)` is an isomorphism. -/
@[stacks 0G40]
#check fun {K : ModuleDerived X} (hK : IsPerfect K) (L M : ModuleDerived X) ↦
  hK.isIso_compTranspose
    (RightInternalHom.ofBraidedClosed (C := ModuleDerived X)) L M

end AlgebraicGeometry.RingedSpace.ModuleDerived
