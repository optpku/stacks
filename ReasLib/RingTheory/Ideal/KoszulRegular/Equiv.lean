module

public import ReasLib.RingTheory.Ideal.KoszulRegular.FaithfullyFlat

@[expose] public section

/-!
# Ring Equivalences and Koszul-Regular Ideals

This leaf owns transport of the Zariski-local Koszul-regular ideal condition
along ring equivalences.
-/

universe u v

namespace Ideal.IsKoszulRegularIdeal

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

/-- Koszul-regularity of an ideal is invariant under transport by a ring equivalence. -/
theorem map_ringEquiv_iff (e : A ≃+* B) {I : Ideal A} :
    I.IsKoszulRegularIdeal ↔ (I.map e.toRingHom).IsKoszulRegularIdeal := sorry

end Ideal.IsKoszulRegularIdeal
