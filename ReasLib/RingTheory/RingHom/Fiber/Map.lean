module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Fibers of explicit ring homomorphisms

The fiber of a commutative-ring homomorphism over a source prime is obtained
after extension to the prime's residue field. It carries the canonical algebra
structure over that residue field.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The residue-field fiber of an explicit ring homomorphism over a source
prime.  It uses exactly the canonical algebra structure `f.toAlgebra`. -/
@[stacks 07F2 "fiber of an explicit ring map"]
abbrev Fiber (f : R →+* S) (p : Ideal R) [p.IsPrime] : Type _ :=
  let _ : Algebra R S := f.toAlgebra
  p.Fiber S

end RingHom

namespace RingHom.Fiber

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- The canonical residue-field algebra structure on the fiber of an explicit ring homomorphism.
It is named because Mathlib intentionally keeps the overlapping tensor-product algebra structures
out of global instance search. -/
@[implicit_reducible, stacks 07F2 "canonical residue-field algebra on a ring-map fiber"]
noncomputable def residueFieldAlgebra (f : R →+* S) (p : Ideal R) [p.IsPrime] :
    Algebra p.ResidueField (f.Fiber p) :=
  @Algebra.TensorProduct.leftAlgebra R p.ResidueField p.ResidueField S
    inferInstance inferInstance inferInstance inferInstance f.toAlgebra
    inferInstance inferInstance inferInstance

end RingHom.Fiber
