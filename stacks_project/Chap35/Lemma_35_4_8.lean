/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.UniversallyInjective.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

universe u v w

/- Lemma 35.4.8 (08WP): any faithfully flat ring map is universally injective. -/
@[stacks 08WP] #check
  (@Module.FaithfullyFlat.universallyInjective_algebraLinearMap :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Module.FaithfullyFlat R S],
      LinearMap.UniversallyInjective.{u, u, v, w} (Algebra.linearMap R S))
