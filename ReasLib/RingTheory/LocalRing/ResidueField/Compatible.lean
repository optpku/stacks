/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Compatible prescribed maps of residue fields

This leaf owns the compatibility condition for a prescribed residue-field map
over a local cospan.  It is stated for arbitrary local maps, without imposing
algebra structures, scalar towers, strict henselizations, or tensor products.
More structured comparison APIs should consume this predicate rather than
repeat its induced-residue-field equation.

@stack 04GU
-/

universe u v w x y z

namespace IsLocalRing.ResidueField

section

variable {R : Type u} {S : Type v} {A : Type w} {B : Type x}
variable [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalRing A] [IsLocalRing B]

/-- A prescribed residue-field map is compatible with a square of local ring
homomorphisms when it intertwines the three induced residue-field maps. -/
noncomputable def Compatible
    (base : R →+* S) (source : R →+* A) (target : S →+* B)
    (residueMap : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    [IsLocalHom base] [IsLocalHom source] [IsLocalHom target] : Prop :=
  residueMap.comp (map source) = (map target).comp (map base)

namespace Compatible

/-- Unfold the compatibility condition for a prescribed residue-field map. -/
theorem iff
    (base : R →+* S) (source : R →+* A) (target : S →+* B)
    (residueMap : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B)
    [IsLocalHom base] [IsLocalHom source] [IsLocalHom target] :
    Compatible base source target residueMap ↔
      residueMap.comp (map source) = (map target).comp (map base) := sorry

/-- A commuting square of local ring homomorphisms induces a compatible map
on residue fields. -/
theorem of_comm
    (base : R →+* S) (source : R →+* A) (target : S →+* B)
    (right : A →+* B)
    [IsLocalHom base] [IsLocalHom source] [IsLocalHom target] [IsLocalHom right]
    (comm : right.comp source = target.comp base) :
    Compatible base source target (map right) := sorry

section Coordinates

variable {K : Type y} {L : Type z}
variable [NonAssocSemiring K] [NonAssocSemiring L]

/-- Tag 04GU: transport a commuting square written in arbitrary residue-field
coordinates back to the native residue-field compatibility predicate.  No
algebra structure, scalar tower, or henselization data is needed on the
coordinate rings. -/
@[stacks 04GU "residue-field compatibility in chosen coordinates"]
theorem ofEquiv
    (base : R →+* S) (source : R →+* A) (target : S →+* B)
    [IsLocalHom base] [IsLocalHom source] [IsLocalHom target]
    (eA : IsLocalRing.ResidueField A ≃+* K)
    (eB : IsLocalRing.ResidueField B ≃+* L)
    (sourceCoordinate : IsLocalRing.ResidueField R →+* K)
    (targetCoordinate : IsLocalRing.ResidueField S →+* L)
    (h_source : eA.toRingHom.comp (map source) = sourceCoordinate)
    (h_target : eB.toRingHom.comp (map target) = targetCoordinate)
    (φ : K →+* L)
    (h_coordinates :
      φ.comp sourceCoordinate = targetCoordinate.comp (map base)) :
    Compatible base source target
      (eB.symm.toRingHom.comp (φ.comp eA.toRingHom)) := sorry

end Coordinates

end Compatible

end

end IsLocalRing.ResidueField
