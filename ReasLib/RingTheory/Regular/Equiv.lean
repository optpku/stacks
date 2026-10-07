module

public import ReasLib.RingTheory.Regular.RingMap

@[expose] public section

/-!
# Regular ring maps and ring equivalences

Regularity belongs to the morphism, so it is invariant under an isomorphism of either endpoint.
The commuting-square theorem is the general transport API; the composition lemmas are its
ergonomic specializations.

@stack 07BZ
-/

namespace RingHom.Regular

universe u v w x

variable {A : Type u} {B : Type v} {A' : Type w} {B' : Type x}
variable [CommRing A] [CommRing B] [CommRing A'] [CommRing B']

/-- Regularity is transported across a commuting square of ring equivalences. -/
@[stacks 07BZ "regularity under a square of ring equivalences"]
theorem of_ringEquiv {f : A →+* B} {f' : A' →+* B'}
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcomm : ∀ a : A, eB (f a) = f' (eA a)) (hf : f.Regular) :
    f'.Regular := sorry

/-- Regularity is invariant under a commuting square of ring equivalences. -/
theorem ringEquiv_iff {f : A →+* B} {f' : A' →+* B'}
    (eA : A ≃+* A') (eB : B ≃+* B')
    (hcomm : ∀ a : A, eB (f a) = f' (eA a)) :
    f.Regular ↔ f'.Regular := sorry

/-- Postcomposition with a ring equivalence preserves regularity. -/
theorem comp_equiv {f : A →+* B} (hf : f.Regular) (e : B ≃+* B') :
    (e.toRingHom.comp f).Regular := sorry

/-- Precomposition with a ring equivalence preserves regularity. -/
theorem equiv_comp (e : A' ≃+* A) {f : A →+* B} (hf : f.Regular) :
    (f.comp e.toRingHom).Regular := sorry

end RingHom.Regular

namespace RingEquiv

universe u v

/-- Every ring equivalence is a regular ring map. -/
@[stacks 07BZ "ring equivalences are regular"]
instance instRegular {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) : e.toRingHom.Regular := sorry

/-- A ring equivalence, viewed as a ring homomorphism, is regular. -/
theorem regular {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (e : A ≃+* B) : e.toRingHom.Regular := sorry

end RingEquiv
