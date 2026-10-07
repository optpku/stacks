module

public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Module.QuotSMulTop

@[expose] public section

/-!
# Transport of Regular Sequences

This leaf contains functorial transport lemmas for the canonical predicate
`RingTheory.Sequence.IsRegular`.  It deliberately contains no presentation or
complete-intersection data, so it can be imported by either layer directly.
-/

universe u v

namespace RingEquiv

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring equivalence transports a regular sequence to the entrywise mapped sequence. -/
@[stacks 00SC "regular sequences under ring equivalence"]
theorem isRegular_iff (e : R ≃+* S) (xs : List R) :
    RingTheory.Sequence.IsRegular R xs ↔ RingTheory.Sequence.IsRegular S (xs.map e) := sorry

end RingEquiv

universe w

namespace RingTheory.Sequence

variable {R : Type u} {S : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]

include S

/-- A scalar-compatible `S`-module has the same regular sequences over `R` as over `S` after
mapping the entries along `algebraMap R S`. -/
@[stacks 00MG "regular-sequence scalar restriction"]
theorem isRegular_map_algebraMap_iff (xs : List R) :
    IsRegular M (xs.map (algebraMap R S)) ↔ IsRegular M xs := sorry

omit S

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Regularity on `QuotSMulTop r M` may be read either over `R` or over the principal quotient
ring after mapping every sequence entry to that quotient. -/
@[stacks 00MG "regularity on a principal quotient module"]
theorem isRegular_quotSMulTop_iff (r : R) (xs : List R) :
    IsRegular (QuotSMulTop r M) xs ↔
      IsRegular (QuotSMulTop r M)
        (xs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set R)))) := sorry

/-- Regularity on the principal quotient module of the regular module is equivalent to
regularity on the corresponding principal quotient ring. -/
@[stacks 00MG "regularity on a principal quotient ring"]
theorem isRegular_quotSMulTop_self_iff_quotient (r : R) (xs : List R) :
    IsRegular (QuotSMulTop r R) xs ↔
      IsRegular (R ⧸ Ideal.span ({r} : Set R))
        (xs.map (Ideal.Quotient.mk (Ideal.span ({r} : Set R)))) := sorry

end RingTheory.Sequence
