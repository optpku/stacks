module

public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import ReasLib.LinearAlgebra.QuotientByIdeal

/-!
# Quotient maps and reduction modulo an ideal

This leaf records the canonical comparison between the quotient-map API and
Mathlib's `LinearMap.reduceModIdeal` presentation.  Keeping the comparison
separate from the basic quotient construction avoids making the latter depend
on adic-completion functoriality.
-/

@[expose] public section

universe u v w

namespace LinearMap

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {M' : Type w} [AddCommGroup M'] [Module R M']

/-- The canonical quotient map agrees with `reduceModIdeal` after the latter is viewed again as
an `R`-linear map. -/
theorem quotientMapByIdeal_eq_reduceModIdeal_restrictScalars
    (f : M →ₗ[R] M') (I : Ideal R) :
    f.quotientMapByIdeal I = (f.reduceModIdeal I).restrictScalars R := by
  apply LinearMap.ext
  rintro ⟨x⟩
  rfl

end LinearMap
