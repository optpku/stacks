/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.SeparableClosure.Map
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.LocalRing.ResidueField.MaximalIdeal

@[expose] public section

/-!
# Residue-field coordinates of strict henselizations

This leaf owns the neutral notion of a chosen identification between the
residue field of a strict henselization and an external field.  It is
independent of a presentation by pointed-etale algebras: those presentations
should supply a `Coordinate` rather than define a second coordinate notion.
-/

open IsLocalRing

universe u v w

noncomputable section

namespace IsStrictHenselizationOf.ResidueField

variable {L : Type u} [CommRing L] [IsLocalRing L]
variable {S : Type v} [CommRing S] [Algebra L S]
variable [IsStrictHenselizationOf L S]
variable {K : Type w} [Field K]
variable {baseMap : IsLocalRing.ResidueField L →+* K}

/-- A chosen coordinate from the residue field of a strict henselization to
an external field, compatible with a specified base residue-field map. -/
@[stacks 04GW "strict-henselization residue-field coordinate"]
structure Coordinate (baseMap : IsLocalRing.ResidueField L →+* K) where
  /-- The selected equivalence from the target residue field to the external
  field. -/
  equiv : IsLocalRing.ResidueField S ≃+* K
  /-- The selected coordinate agrees with the prescribed map out of the base
  residue field. -/
  commutes :
    equiv.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap L S)) =
      baseMap

namespace Coordinate

/-- Constructs a residue-field coordinate from an equivalence and its
compatibility equation. -/
def ofEquiv
    (equiv : IsLocalRing.ResidueField S ≃+* K)
    (commutes : equiv.toRingHom.comp (IsLocalRing.ResidueField.map (algebraMap L S)) =
      baseMap) : Coordinate (S := S) baseMap :=
  { equiv, commutes }

/-- The compatibility equation defining a residue-field coordinate. -/
@[stacks 04GW "specification of a strict-henselization residue-field coordinate"]
theorem spec (coordinate : Coordinate (S := S) baseMap) :
    coordinate.equiv.toRingHom.comp
        (IsLocalRing.ResidueField.map (algebraMap L S)) =
      baseMap := sorry

/-- Residue-field coordinates are determined by their target field
equivalence. -/
@[ext]
theorem ext {coordinate₁ coordinate₂ : Coordinate (S := S) baseMap}
    (hequiv : coordinate₁.equiv = coordinate₂.equiv) : coordinate₁ = coordinate₂ := sorry

/-- The target coordinate transported to the residue field of the target
maximal ideal. -/
@[stacks 04GW "maximal-ideal strict-henselization residue-field coordinate"]
noncomputable def maximalIdealEquiv (coordinate : Coordinate (S := S) baseMap) :
    (IsLocalRing.maximalIdeal S).ResidueField ≃+* K :=
  (IsLocalRing.ResidueField.maximalIdealAlgEquiv S).symm.toRingEquiv.trans
    coordinate.equiv

/-- The maximal-ideal form of the residue-coordinate compatibility equation. -/
@[stacks 04GW "maximal-ideal strict-henselization residue-coordinate compatibility"]
theorem maximalIdealEquiv_comp (coordinate : Coordinate (S := S) baseMap) :
    coordinate.maximalIdealEquiv.toRingHom.comp
        (Ideal.ResidueField.map
          (IsLocalRing.maximalIdeal L) (IsLocalRing.maximalIdeal S)
          (algebraMap L S)
          (IsLocalRing.maximalIdeal_comap (algebraMap L S)).symm) =
      baseMap.comp
        (IsLocalRing.ResidueField.maximalIdealAlgEquiv L).symm.toRingHom := sorry

/-- A map-oriented separable-closure target admits a compatible coordinate on
the residue field of every strict henselization.  The result is proposition-
valued so the neutral owner does not choose a noncanonical equivalence. -/
@[stacks 04GW "existence of a strict-henselization residue coordinate"]
theorem exists_of_isSepClosure
    (baseMap : IsLocalRing.ResidueField L →+* K)
    (h_sep : RingHom.IsSepClosure baseMap) :
    Nonempty (Coordinate (S := S) baseMap) := sorry

end Coordinate

end IsStrictHenselizationOf.ResidueField
