module

public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.RingHom.ULift

/-!
# Universe Lifts of Local Rings

This leaf owns the canonical local-ring instance and local-hom transport for
universe lifts.  They are structural consequences of the `ULift` ring
equivalence, not chapter-specific comparison data.
-/

@[expose] public section

universe u v w

namespace ULift

/-- A universe lift of a local commutative semiring is canonically local. -/
@[stacks 0523 "local rings under universe lift"]
instance instIsLocalRing {R : Type u} [CommSemiring R] [IsLocalRing R] :
    IsLocalRing (ULift.{v} R) := sorry

variable {R : Type u} {S : Type v} [CommSemiring R] [Semiring S] [Algebra R S]

/-- Lifting only the target of a local algebra map through the canonical `ULift` algebra
structure preserves locality. -/
theorem algebraMap_isLocalHom [IsLocalHom (algebraMap R S)] :
    IsLocalHom (algebraMap R (ULift.{w} S)) := sorry

end ULift

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The two-sided universe lift of a local ring homomorphism is local. -/
@[stacks 0523 "local homomorphisms under universe lift"]
theorem ulift_isLocalHom (f : R →+* S) [IsLocalHom f] :
    IsLocalHom (RingHom.ulift f) := sorry

/-- A codomain-only universe lift of a local ring homomorphism is local. -/
@[stacks 0523 "local homomorphisms under codomain universe lift"]
theorem uliftCodomain_isLocalHom (f : R →+* S)
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom f] :
    IsLocalHom f.uliftCodomain := sorry

end RingHom
