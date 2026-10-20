module

public import ReasLib.RingTheory.Ideal.RigClosed
import StacksCheckRecall

/-!
# Residue fields of rig-closed primes in a relative setting
-/

@[expose] public section

universe u v

/- Lemma 88.14.3: for a continuous homomorphism of Noetherian adic rings,
finite type of the induced map on topological-nilradical quotients implies
finite type of the induced map to the residue field of a rig-closed quotient. -/
@[stacks 0GGA] #check (Ideal.IsRigClosed.residueFieldHom_finiteType :
  ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B],
    (φ : A →+* B) → (hφ : Continuous φ) →
    (φ.topologicalNilradicalQuotient hφ).FiniteType →
    (q : Ideal B) → [q.IsRigClosed] →
    (Ideal.IsRigClosed.residueFieldHom φ hφ q).FiniteType)
