module

public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u

/-- A commutative ring is Noetherian exactly when every ideal is spanned by a finite set. -/
theorem isNoetherianRing_iff_exists_finset_span (R : Type u) [CommRing R] :
    IsNoetherianRing R ↔
      ∀ ideal : Ideal R, ∃ generators : Finset R, Ideal.span (generators : Set R) = ideal := sorry
