/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Topology.Adic.Taut
import StacksCheckRecall

/-!
# Lemma 87.5.9

A continuous taut homomorphism of linearly topologized rings sends a
pre-admissible source to a pre-admissible target.
-/

@[expose] public section

universe u v

open TopologicalRing

/- Lemma 87.5.9: A continuous taut homomorphism of linearly topologized rings
from a pre-admissible ring has a pre-admissible target. -/
@[stacks 0GX8] #check (RingHom.IsTaut.isPreadmissibleRing :
  ∀ {A : Type u} {B : Type v}
    [CommRing A] [TopologicalSpace A] [IsPreadmissibleRing A]
    [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsLinearTopology B B]
    {φ : A →+* B}, Continuous φ → φ.IsTaut → IsPreadmissibleRing B)
