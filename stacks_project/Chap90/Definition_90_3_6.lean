/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.LocalRing.Cotangent.Relative
import StacksCheckRecall

@[expose] public section

universe u v

/- Definition 90.3.6: for a local homomorphism of local rings R → S, the relative
cotangent space of S over R is the ResidueField S-vector space
maximalIdeal S ⧸ (Ideal.map (algebraMap R S) (maximalIdeal R) ⊔ maximalIdeal S ^ 2).
This is owned by IsLocalRing.RelativeCotangentSpace. -/
@[stacks 06GY] #check (IsLocalRing.RelativeCotangentSpace :
  (R : Type u) → (S : Type v) → [CommRing R] → [CommRing S] →
    [IsLocalRing R] → [IsLocalRing S] → [Algebra R S] →
    [IsLocalHom (algebraMap R S)] → Type v)
