/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 29.14.6: if `P` is a local property of ring maps and is stable under base change, then
the base change of a morphism locally of type `P` is again locally of type `P`. -/
@[stacks 01SW]
#check (@AlgebraicGeometry.locallyOfType_pullback_snd :
  ∀ {X S : Scheme.{u}} {f : X ⟶ S}
    (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
    {S' : Scheme.{u}},
    RingHom.PropertyIsLocal P → RingHom.IsStableUnderBaseChange P →
      LocallyOfType P f → ∀ g : S' ⟶ S, LocallyOfType P (pullback.snd f g))
