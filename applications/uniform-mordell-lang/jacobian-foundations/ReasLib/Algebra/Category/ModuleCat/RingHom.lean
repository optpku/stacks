module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The target module of a ring homomorphism

This leaf packages the target of a commutative-ring homomorphism as a module
over its source. Keeping this as explicit data avoids installing a
proof-indexed algebra structure as a global instance.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The target of `f : R →+* S`, regarded as an `R`-module through `f`. -/
@[reducible]
def targetModule (f : R →+* S) : ModuleCat R :=
  -- Local instance justification (noncanonical choice): the explicit map `f`
  -- selects the scalar action; the two carrier rings do not determine it.
  letI : Algebra R S := f.toAlgebra
  ModuleCat.of R S

/-- The carrier of `f.targetModule` is definitionally the target ring. -/
@[simp]
theorem targetModule_carrier (f : R →+* S) :
    (f.targetModule : Type v) = S := rfl

/-- For an ambient algebra, the target module of its structure map is the
usual underlying module. -/
theorem targetModule_algebraMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S] :
    (algebraMap R S).targetModule = ModuleCat.of R S := sorry

end RingHom
