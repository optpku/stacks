/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

/-!
# Henselizations of Local Rings

This module owns the reusable proposition that a local algebra is a henselization of its base,
the existence theorem, and its residue-field interface.  Particular filtered-colimit
constructions are proof infrastructure rather than competing public owners.
-/

open IsLocalRing

universe u v

section

variable (R : Type u) [CommRing R] [IsLocalRing R]
variable (S : Type v) [CommRing S] [Algebra R S]

/-- A local `R`-algebra `S` is a henselization of `R` when its structural map is local and
ind-etale, its target is henselian, it identifies maximal ideals, and it induces an isomorphism
on residue fields. -/
@[stacks 04GN "henselization owner"]
class IsHenselizationOf : Prop extends HenselianLocalRing S, IsLocalHom (algebraMap R S) where
  isFilteredColimitOfEtale : RingHom.IndEtale (algebraMap R S)
  map_maximalIdeal :
    Ideal.map (algebraMap R S) (maximalIdeal R) = maximalIdeal S
  residueField_bijective :
    Function.Bijective (ResidueField.map (algebraMap R S))

namespace IsHenselizationOf

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : Type v} [CommRing S] [Algebra R S] [IsHenselizationOf R S]

/-- A henselization of a Noetherian local ring is Noetherian.  This remains a
named theorem because the target ring does not determine its base ring for
typeclass search. -/
@[stacks 06LJ]
theorem isNoetherianRing [IsNoetherianRing R] : IsNoetherianRing S := sorry

/-- The structural map of a henselization is local. -/
@[stacks 04GN "locality of a henselization map"]
instance isLocalHom : IsLocalHom (algebraMap R S) :=
  IsHenselizationOf.toIsLocalHom

/-- The structural map of a henselization is ind-etale. -/
@[stacks 04GN "ind-etaleness of a henselization map"]
theorem indEtale : RingHom.IndEtale (algebraMap R S) := sorry

/-- The structural map of a henselization maps the base maximal ideal onto
the maximal ideal of the henselization. -/
@[stacks 04GN "maximal-ideal compatibility of a henselization map"]
theorem mapsMaximalIdeal :
    RingHom.MapsMaximalIdeal (algebraMap R S) := sorry

/-- The defining henselian, local, ind-etale, closed-point, and residue-field conditions of a
henselization. -/
@[stacks 04GN "henselization specification"]
theorem spec :
    HenselianLocalRing S ∧
      IsLocalHom (algebraMap R S) ∧
        RingHom.IndEtale (algebraMap R S) ∧
          RingHom.MapsMaximalIdeal (algebraMap R S) ∧
            Function.Bijective (ResidueField.map (algebraMap R S)) := sorry

/-- Every local ring admits a henselization represented by a local algebra
carrying the `IsHenselizationOf` structure. -/
@[stacks 04GN "existence of henselizations"]
theorem exists_henselization (R : Type u) [CommRing R] [IsLocalRing R] :
    ∃ (S : Type u) (_ : CommRing S) (_ : Algebra R S), IsHenselizationOf R S := sorry

/-- The canonical residue-field equivalence induced by a henselization. -/
@[stacks 04GN "henselization residue-field equivalence"]
noncomputable def residueFieldEquiv : ResidueField R ≃+* ResidueField S :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R S))
    IsHenselizationOf.residueField_bijective

/-- The henselization residue-field equivalence is induced by the structural map. -/
@[stacks 04GN "henselization residue-field map", simp]
theorem residueFieldEquiv_apply (x : ResidueField R) :
    residueFieldEquiv (R := R) (S := S) x = ResidueField.map (algebraMap R S) x := sorry

end IsHenselizationOf

end
