module

public import ReasLib.RingTheory.Localization.TotalQuotient

@[expose] public section

/-!
# Flat algebra maps of total quotient rings

This leaf upgrades the total-quotient-ring map induced by a flat algebra map to an algebra
homomorphism over the source ring.  It is deliberately independent of normalization and can be
used by every flat base-change construction.
-/

universe u v

open scoped nonZeroDivisors

namespace Localization

section

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S] [Module.Flat R S]

/-- The flat total-quotient algebra map commutes with the structure map from `R`. -/
theorem totalQuotientAlgMap_commutes (r : R) :
    totalQuotientMap (algebraMap R S) algebraMap_nonZeroDivisors_le_comap_of_flat
        (algebraMap R (totalQuotientRing R) r) =
      algebraMap R (totalQuotientRing S) r := sorry

/-- The total-quotient-ring map induced by a flat `R`-algebra `S`, viewed as an `R`-algebra
homomorphism. -/
noncomputable def totalQuotientAlgMap :
    totalQuotientRing R →ₐ[R] totalQuotientRing S :=
  { totalQuotientMap (algebraMap R S) algebraMap_nonZeroDivisors_le_comap_of_flat with
    commutes' := totalQuotientAlgMap_commutes }

/-- Compute the flat total-quotient algebra map on an element of `R`. -/
theorem totalQuotientAlgMap_apply (r : R) :
    totalQuotientAlgMap (R := R) (S := S)
        (algebraMap R (totalQuotientRing R) r) =
      algebraMap R (totalQuotientRing S) r :=
  totalQuotientAlgMap_commutes r

end

end Localization
