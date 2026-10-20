module

public import Mathlib.Algebra.Algebra.Epi
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotient algebras are epimorphisms

@stack 00TT

The canonical algebra map from a commutative semiring to a quotient by an ideal is surjective,
and hence is an epimorphism of commutative algebras.
-/

@[expose] public section

universe u

namespace Ideal.Quotient

variable {R : Type u} [CommRing R]

/-- A quotient by an ideal is canonically an epimorphic algebra over its source. -/
@[stacks 00TT "quotient algebra epimorphism"]
instance instIsEpi (I : Ideal R) : Algebra.IsEpi R (R ⧸ I) :=
  Algebra.isEpi_of_surjective_algebraMap R (R ⧸ I) Ideal.Quotient.mk_surjective

end Ideal.Quotient

example {R : Type u} [CommRing R] (I : Ideal R) : Algebra.IsEpi R (R ⧸ I) :=
  inferInstance
