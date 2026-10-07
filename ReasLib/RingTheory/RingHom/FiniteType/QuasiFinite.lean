module

public import Mathlib.RingTheory.RingHom.FiniteType
public import ReasLib.RingTheory.QuasiFinite.FiniteType

/-!
# Finite-type quasi-finite ring homomorphisms

This module defines the conjunction of finite type and finite-fibre
quasi-finiteness for commutative-ring homomorphisms and records its locality.
-/

@[expose] public section

namespace RingHom.FiniteType

/-- A ring homomorphism is finite-type quasi-finite when it is of finite type
and quasi-finite in the finite-fibre sense. -/
def QuasiFinite {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  f.FiniteType ∧ f.QuasiFinite

namespace QuasiFinite

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A finite-type quasi-finite ring homomorphism is of finite type. -/
theorem finiteType {f : R →+* S} (h : RingHom.FiniteType.QuasiFinite f) :
    f.FiniteType := sorry

/-- A finite-type quasi-finite ring homomorphism is quasi-finite in the
finite-fibre sense. -/
theorem toQuasiFinite {f : R →+* S} (h : RingHom.FiniteType.QuasiFinite f) :
    f.QuasiFinite := sorry

/-- For an algebra map, finite-type quasi-finiteness of the ring homomorphism
is equivalent to finite-type quasi-finiteness of the algebra. -/
theorem algebraMap_iff [Algebra R S] :
    RingHom.FiniteType.QuasiFinite (algebraMap R S) ↔
      Algebra.FiniteType.QuasiFinite R S := sorry

/-- Finite-type quasi-finiteness is a local property of ring homomorphisms. -/
theorem propertyIsLocal :
    RingHom.PropertyIsLocal RingHom.FiniteType.QuasiFinite := sorry

end QuasiFinite

end RingHom.FiniteType
