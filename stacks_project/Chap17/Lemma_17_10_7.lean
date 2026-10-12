/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Associated.BaseChange
import StacksCheckRecall

/-!
# Pullback of associated module sheaves

The reusable result is the functorial base-change isomorphism in
`RingedSpace.Module.Associated`. This file records its identity-scalar specialization from the
source.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

open RingedSpace.Module

/- Lemma 17.10.7 (01BJ): after pullback along `g : Y ⟶ X`, the module sheaf associated to
`M` is the associated sheaf of the scalar extension of `M` from `Γ(X, O_X)` to
`Γ(Y, O_Y)`. -/
@[stacks 01BJ]
#check fun {X Y : RingedSpace.{u}} (g : Y ⟶ X)
    (M : ModuleCat X.globalSectionsRing) =>
  Associated.obj.baseChangeIso g (RingHom.id X.globalSectionsRing) M

#check @Associated.functor.baseChangeIso

end AlgebraicGeometry
