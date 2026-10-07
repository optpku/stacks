module

public import Mathlib.RingTheory.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.31.3

@stack 00FO
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section FieldCase

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/- Lemma 10.31.3 (field case; Stacks tag `00FO`): any finite type algebra over a field is
Noetherian. This is the field-specialized use of the owner theorem
`Algebra.FiniteType.isNoetherianRing`. -/
@[stacks 00FO "field case"]
#check (Algebra.FiniteType.isNoetherianRing k A : IsNoetherianRing A)

end FieldCase

section IntCase

variable {A : Type u} [CommRing A] [Algebra ℤ A] [Algebra.FiniteType ℤ A]

/- Lemma 10.31.3 (`ℤ`-case): any finite type algebra over `ℤ` is Noetherian. This is the
`ℤ`-specialized use of the same owner theorem, with the base Noetherian hypothesis supplied by the
canonical instance on `ℤ`. -/
@[stacks 00FO "integer-base case"]
#check (Algebra.FiniteType.isNoetherianRing ℤ A : IsNoetherianRing A)

end IntCase
