/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.RingHom
public import Mathlib.LinearAlgebra.FreeModule.Basic

@[expose] public section

universe u v

namespace RingHom

/-- A ring homomorphism is free when its target is a free module over its source via the
module structure induced by the homomorphism. -/
def Free {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) : Prop :=
  @Module.Free R A _ _ f.toModule

/-- Freeness relative to a ring homomorphism is equivalent to the existence of a basis for
the induced module structure. -/
theorem free_iff_exists_basis {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    (f : R →+* A) :
    f.Free ↔ ∃ I : Type v, Nonempty (@Module.Basis I R A _ _ f.toModule) := sorry

/-- For an algebra structure map, map-relative freeness agrees with the usual module
freeness predicate. -/
theorem free_algebraMap {R : Type u} {A : Type v} [CommRing R] [CommRing A]
    [Algebra R A] :
    (algebraMap R A).Free ↔ Module.Free R A := sorry

end RingHom
