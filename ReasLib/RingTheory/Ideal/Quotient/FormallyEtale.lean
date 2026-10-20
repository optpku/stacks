module

public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

universe u

namespace Ideal.Quotient

/-- The quotient map `R →+* R ⧸ J` is formally étale if and only if `J` is an
idempotent ideal. -/
theorem formallyEtale_mk_iff {R : Type u} [CommRing R] (J : Ideal R) :
    (mk J).FormallyEtale ↔ IsIdempotentElem J := sorry

/-- If `R` is local and `J` is a nonzero proper ideal, then the quotient map
`R →+* R ⧸ J` is not flat. -/
theorem not_flat_mk_of_isLocalRing {R : Type u} [CommRing R] [IsLocalRing R]
    {J : Ideal R} (h_bot : J ≠ ⊥) (h_top : J ≠ ⊤) :
    ¬ (mk J).Flat := sorry

end Ideal.Quotient
