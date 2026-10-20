module

public import ReasLib.RingTheory.Regular.RingMap
public import ReasLib.RingTheory.RingHom.IndSmooth.Factorization
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Popescu's theorem

Popescu's theorem belongs to the explicit ring homomorphism rather than to a
temporarily chosen algebra structure.
-/

universe u v

namespace RingHom.Regular

/-- The finite-presentation factorisation form of Popescu's theorem. -/
@[stacks 07GC "Popescu smooth factorisations"]
theorem hasFactorisations
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing R] [IsNoetherianRing S]
    [f.Regular] :
    RingHom.IndSmooth.HasFactorisations f := sorry

/-- Theorem 16.12.1 (Popescu): a regular homomorphism between Noetherian
commutative rings is a filtered colimit of smooth ring maps. -/
@[stacks 07GC]
theorem indSmooth
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) [IsNoetherianRing R] [IsNoetherianRing S]
    [f.Regular] :
    f.IndSmooth := sorry

end RingHom.Regular
