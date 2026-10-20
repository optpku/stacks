module

import ReasLib.RingTheory.Ideal.RigClosed.Image
import ReasLib.RingTheory.Ideal.RigClosed.Comap
import StacksCheckRecall

universe u v

open Ideal.IsRigClosed

/- Lemma 88.14.6: let `φ : A →+* B` be an adic, topologically finite type,
flat homomorphism of Noetherian adic rings, and let `p ⊂ A` be rig-closed.
The closed point of `A ⧸ p`, as a point of
`PrimeSpectrum (A ⧸ topologicalNilradical A)`, lies in the image of
`PrimeSpectrum.comap (φ.topologicalNilradicalQuotient _)` if and only if
there exists a rig-closed prime `q ⊂ B` with `q.comap φ = p`.
For every such `q`, the equality `q.comap φ = p` and `p.IsRigClosed`
supply the rig-closed contraction condition in the two criteria checked
below. These stronger criteria recover both final finiteness conclusions
without requiring flatness. -/
@[stacks 0GGD] #check (Ideal.IsRigClosed.exists_comap_iff :
    ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (p : Ideal A) [p.IsRigClosed],
    closedPointReduction p ∈
        Set.range (PrimeSpectrum.comap (φ.topologicalNilradicalQuotient h_adic.continuous)) ↔
      ∃ q : Ideal B, q.IsRigClosed ∧ q.comap φ = p)

#check (Ideal.IsRigClosed.residueFieldHom_finite_iff_comap :
    ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed],
    (residueFieldHom φ h_adic.continuous q).Finite ↔
      (q.comap φ).IsRigClosed)

#check (Ideal.IsRigClosed.comap_iff_quotientMap_finite :
    ∀ {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed],
    (q.comap φ).IsRigClosed ↔
      (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite)
