/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.DescentDatum.Effectivity
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct.Right

universe u

/- Definition 35.3.4: a module descent datum `D : Module.DescentDatum R A N`
is effective when there is an `R`-module `M` and an isomorphism of descent data
from the canonical datum on `M ⊗[R] A` to `D`. -/
@[stacks 023J] #check (@Module.DescentDatum.IsEffective :
  (R A N : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup N] → [Module R N] → [Module A N] →
    [IsScalarTower R A N] → [SMulCommClass R A N] →
    Module.DescentDatum R A N → Prop)

#check (@Module.DescentDatum.isEffective_iff :
  (R A N : Type u) → [CommRing R] → [CommRing A] → [Algebra R A] →
    [AddCommGroup N] → [Module R N] → [Module A N] →
    [IsScalarTower R A N] → [SMulCommClass R A N] →
    (D : Module.DescentDatum R A N) →
      Module.DescentDatum.IsEffective D ↔
        ∃ M : ModuleCat.{u} R,
          Nonempty (Module.DescentDatum.Iso (Module.DescentDatum.canonical R A M) D))
