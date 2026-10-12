/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible
import StacksCheckRecall

@[expose] public section

open Topology

universe u v

/- Lemma 28.2.7: a partition of a scheme into locally closed retrocompact parts is locally finite
if and only if every part is locally constructible. -/
@[stacks 0F2M] #check
  (AlgebraicGeometry.Scheme.locallyFinite_iff_forall_isLocallyConstructible_of_retrocompact :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : Type v} {parts : I → Set X},
      IndexedPartition parts →
      (∀ i, IsLocallyClosed (parts i)) →
      (∀ i, IsRetrocompact (parts i)) →
      (LocallyFinite parts ↔ ∀ i, IsLocallyConstructible (parts i)))
