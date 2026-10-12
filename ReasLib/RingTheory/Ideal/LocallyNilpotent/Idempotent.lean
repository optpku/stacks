/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Idempotents
public import ReasLib.Algebra.Group.Idempotent.Map
public import ReasLib.RingTheory.Ideal.LocallyNilpotent
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Idempotents Modulo Locally Nilpotent Ideals

Idempotents lift uniquely across a ring homomorphism with locally nilpotent kernel.  The
map-level results are the reusable core; the quotient results are their standard specialization.
-/

universe u v

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [Ring S]

/-- An idempotent in the range of a ring homomorphism with locally nilpotent kernel has a unique
idempotent preimage. -/
@[stacks 00J9 "unique idempotent lifting across a locally nilpotent kernel"]
theorem existsUnique_idempotent_lift_of_ker_isLocallyNilpotent
    (f : R →+* S) (hker : (ker f).IsLocallyNilpotent)
    (e : S) (he : e ∈ f.range) (he_idem : IsIdempotentElem e) :
    ∃! e' : R, IsIdempotentElem e' ∧ f e' = e := sorry

/-- A ring homomorphism with locally nilpotent kernel induces an injection on idempotents. -/
@[stacks 00J9 "injectivity on idempotents across a locally nilpotent kernel"]
theorem idempotentMap_injective_of_ker_isLocallyNilpotent
    (f : R →+* S) (hker : (ker f).IsLocallyNilpotent) :
    Function.Injective f.idempotentMap := sorry

/-- A surjective ring homomorphism with locally nilpotent kernel induces a surjection on
idempotents. -/
@[stacks 00J9 "surjectivity on idempotents across a locally nilpotent kernel"]
theorem idempotentMap_surjective_of_surjective_of_ker_isLocallyNilpotent
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hker : (ker f).IsLocallyNilpotent) :
    Function.Surjective f.idempotentMap := sorry

/-- A surjective ring homomorphism with locally nilpotent kernel induces a bijection on
idempotents. -/
@[stacks 00J9 "bijectivity on idempotents across a locally nilpotent kernel"]
theorem idempotentMap_bijective_of_surjective_of_ker_isLocallyNilpotent
    (f : R →+* S) (hsurj : Function.Surjective f)
    (hker : (ker f).IsLocallyNilpotent) :
    Function.Bijective f.idempotentMap := sorry

end RingHom

namespace Ideal.IsLocallyNilpotent

variable {R : Type u} [CommRing R]

/-- A quotient by a locally nilpotent ideal induces a bijection on idempotent elements. -/
@[stacks 00J9 "idempotents modulo a locally nilpotent ideal"]
theorem quotient_idempotentMap_bijective
    {I : Ideal R} (hI : I.IsLocallyNilpotent) :
    Function.Bijective (Ideal.Quotient.mk I).idempotentMap := sorry

/-- Every idempotent modulo a locally nilpotent ideal has a unique idempotent lift. -/
@[stacks 00J9 "unique idempotent lift modulo a locally nilpotent ideal"]
theorem existsUnique_idempotent_lift_quotient
    {I : Ideal R} (hI : I.IsLocallyNilpotent)
    (e : R ⧸ I) (he_idem : IsIdempotentElem e) :
    ∃! e' : R, IsIdempotentElem e' ∧ Ideal.Quotient.mk I e' = e := sorry

end Ideal.IsLocallyNilpotent
