/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.Topology.WeaklyAdmissible.Taut

/-!
# Lemma 87.5.8

A continuous taut homomorphism of linearly topologized rings sends a
weakly pre-admissible source to a weakly pre-admissible target.
-/

@[expose] public section

universe u v

/- Lemma 87.5.8: Let `φ : A →+* B` be a continuous homomorphism of linearly
topologized rings. If `φ` is taut and `A` is weakly pre-admissible, then `B` is
weakly pre-admissible. -/
@[stacks 0GX7] #check
  (RingHom.IsTaut.isWeaklyPreadmissibleRing :
    ∀ {A : Type u} {B : Type v}
      [CommRing A] [TopologicalSpace A] [TopologicalRing.IsWeaklyPreadmissibleRing A]
      [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
      {φ : A →+* B}, Continuous φ → φ.IsTaut →
        TopologicalRing.IsWeaklyPreadmissibleRing B)
