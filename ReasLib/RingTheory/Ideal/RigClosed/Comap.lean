/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.RingTheory.Ideal.RigClosed
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Relative criteria for contracting a rig-closed prime
-/

@[expose] public section

universe u v

open Ideal.IsRigClosed

/-- Let `φ : A →+* B` be an adic, topologically finite type homomorphism of
Noetherian adic rings, let `q ⊂ B` be rig-closed, and write `p = q.comap φ`
and `a = topologicalNilradical A`. The following are equivalent: the residue
field of `B ⧸ q` is finite over `A ⧸ a`; `p` is rig-closed in `A`; and the
canonical map `A ⧸ p →+* B ⧸ q` is a finite ring extension. -/
theorem Ideal.IsRigClosed.comap_tfae {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    List.TFAE
      [(residueFieldHom φ (h_adic.continuous) q).Finite,
        (q.comap φ).IsRigClosed,
        (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite] :=
  sorry

/-- Along an adic, topologically finite type homomorphism of Noetherian adic
rings, the residue field of `B ⧸ q` is finite over `A ⧸ topologicalNilradical A`
if and only if `q.comap φ` is rig-closed. -/
theorem Ideal.IsRigClosed.residueFieldHom_finite_iff_comap
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ (h_adic.continuous) q).Finite ↔
      (q.comap φ).IsRigClosed :=
  (comap_tfae φ h_adic h_tft q).out 0 1

/-- Along an adic, topologically finite type homomorphism of Noetherian adic
rings, `q.comap φ` is rig-closed if and only if the canonical map
`A ⧸ q.comap φ →+* B ⧸ q` is a finite ring extension. -/
theorem Ideal.IsRigClosed.comap_iff_quotientMap_finite
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (q.comap φ).IsRigClosed ↔
      (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite :=
  (comap_tfae φ h_adic h_tft q).out 1 2

/-- Along an adic, topologically finite type homomorphism of Noetherian adic
rings, the residue field of `B ⧸ q` is finite over `A ⧸ topologicalNilradical A`
if and only if the canonical map `A ⧸ q.comap φ →+* B ⧸ q` is a finite ring
extension. -/
theorem Ideal.IsRigClosed.residueFieldHom_finite_iff_quotientMap_finite
    {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalRing.IsAdicRing A] [TopologicalRing.IsAdicRing B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType)
    (q : Ideal B) [q.IsRigClosed] :
    (residueFieldHom φ (h_adic.continuous) q).Finite ↔
      (Ideal.quotientMap q φ (le_rfl : q.comap φ ≤ q.comap φ)).Finite :=
  (comap_tfae φ h_adic h_tft q).out 0 2
