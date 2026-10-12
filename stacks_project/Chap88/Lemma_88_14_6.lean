/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_14_3_RigClosed

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

/-- Lemma 88.14.6: let `φ : A →+* B` be an adic, topologically finite type,
flat homomorphism of Noetherian adic rings, and let `p ⊂ A` be rig-closed.
The closed point of `A ⧸ p`, as a point of
`PrimeSpectrum (A ⧸ topologicalNilradical A)`, lies in the image of
`PrimeSpectrum.comap (φ.topologicalNilradicalQuotient _)` if and only if
there exists a rig-closed prime `q ⊂ B` with `q.comap φ = p`. -/
@[stacks 0GGD]
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

/-- Along an adic, topologically finite type, flat homomorphism of Noetherian
adic rings, a rig-closed prime `q` contracting to a given rig-closed prime `p`
has residue field finite over `A ⧸ topologicalNilradical A`. -/
theorem Ideal.IsRigClosed.residueFieldHom_finite_of_comap_eq
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (p : Ideal A) [p.IsRigClosed]
    (q : Ideal B) [q.IsRigClosed] (hq : q.comap φ = p) :
    (residueFieldHom φ h_adic.continuous q).Finite :=
  sorry

/-- Along an adic, topologically finite type, flat homomorphism of Noetherian
adic rings, a rig-closed prime `q` contracting to a given rig-closed prime `p`
makes `A ⧸ q.comap φ →+* B ⧸ q` a finite ring extension. -/
theorem Ideal.IsRigClosed.quotientMap_finite_of_comap_eq
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (h_flat : φ.Flat) (p : Ideal A) [p.IsRigClosed]
    (q : Ideal B) [q.IsRigClosed] (hq : q.comap φ = p) :
    (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite :=
  sorry
