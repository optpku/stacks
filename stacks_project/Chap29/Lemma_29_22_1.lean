/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Constructible
import StacksCheckRecall

@[expose] public section

open Topology

universe u

/- Lemma 29.22.1 (1): the inverse image of a constructible subset under a morphism of schemes is
constructible. -/
@[stacks 054I] #check (AlgebraicGeometry.Scheme.Hom.isConstructible_preimage :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {E : Set Y},
    IsConstructible E → IsConstructible (f ⁻¹' E))

/- Lemma 29.22.1 (2): the inverse image of a locally constructible subset under a morphism of
schemes is locally constructible. -/
@[stacks 054I]
#check (AlgebraicGeometry.Scheme.Hom.isLocallyConstructible_preimage :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {E : Set Y},
    IsLocallyConstructible E → IsLocallyConstructible (f ⁻¹' E))
