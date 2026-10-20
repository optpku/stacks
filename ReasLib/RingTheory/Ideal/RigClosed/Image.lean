module

public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Rig-closed primes in the image of a reduction morphism
-/

@[expose] public section

universe u v

open IsLocalRing
open Ideal.IsRigClosed

/-- The closed point of `A ⧸ p`, viewed as a point of
`PrimeSpectrum (A ⧸ topologicalNilradical A)` via the residue-field map
induced by `RingHom.id A` at a rig-closed prime `p`. -/
noncomputable def Ideal.IsRigClosed.closedPointReduction {A : Type u}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    [IsNoetherianRing A] (p : Ideal A) [p.IsRigClosed] :
    PrimeSpectrum (A ⧸ topologicalNilradical A) :=
  PrimeSpectrum.comap (residueFieldHom (RingHom.id A) continuous_id p)
    (closedPoint (IsLocalRing.ResidueField (A ⧸ p)))

/-- Contracting `closedPointReduction p` along the quotient by the
topological nilradical of `A` recovers the image of the closed point of
`A ⧸ p` in `PrimeSpectrum A`. -/
theorem Ideal.IsRigClosed.closedPointReduction_comap {A : Type u}
    [CommRing A] [TopologicalSpace A] [TopologicalRing.IsAdicRing A]
    [IsNoetherianRing A] (p : Ideal A) [p.IsRigClosed] :
    PrimeSpectrum.comap (Ideal.Quotient.mk (topologicalNilradical A))
        (closedPointReduction p) =
      PrimeSpectrum.comap (Ideal.Quotient.mk p) (closedPoint (A ⧸ p)) :=
  sorry

/-- Let `φ : A →+* B` be an adic, topologically finite type,
flat homomorphism of Noetherian adic rings, and let `p ⊂ A` be rig-closed.
The closed point of `A ⧸ p`, as a point of
`PrimeSpectrum (A ⧸ topologicalNilradical A)`, lies in the image of
`PrimeSpectrum.comap (φ.topologicalNilradicalQuotient _)` if and only if
there exists a rig-closed prime `q ⊂ B` with `q.comap φ = p`. -/
theorem Ideal.IsRigClosed.exists_comap_iff {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (p : Ideal A) [p.IsRigClosed] :
    closedPointReduction p ∈
        Set.range (PrimeSpectrum.comap (φ.topologicalNilradicalQuotient h_adic.continuous)) ↔
      ∃ q : Ideal B, q.IsRigClosed ∧ q.comap φ = p :=
  sorry
