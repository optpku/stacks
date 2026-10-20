module

import ReasLib.RingTheory.Ideal.RigClosed.Comap
import StacksCheckRecall

universe u v

open Ideal.IsRigClosed

/- Lemma 88.14.4. For an adic, topologically finite type homomorphism of
Noetherian adic rings and a rig-closed prime of the target, residue-field
finiteness, rig-closedness of the contraction, and quotient-map finiteness
are equivalent. -/
@[stacks 0GGB] #check (Ideal.IsRigClosed.comap_tfae :
    ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed],
    List.TFAE
      [(residueFieldHom φ (h_adic.continuous) q).Finite,
        (q.comap φ).IsRigClosed,
        (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite])
