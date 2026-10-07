module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.FieldTheory.SeparableClosure.Map
public import ReasLib.RingTheory.LocalRing.ResidueField.Compatible

@[expose] public section

/-!
# Local residue-field specializations of relative separable-closure models

The field-theoretic owner is `RingHom.SeparableClosure.Realization`.  This
leaf specializes it to the map induced on residue fields by a local ring
homomorphism and provides the bridge from a source construction that begins
with a local map into a common field.

@stack 04GW
-/

universe u v w x y

namespace IsLocalRing.ResidueField

variable {L : Type u} {S : Type v} {K : Type w}
variable [CommRing L] [IsLocalRing L] [CommRing S] [IsLocalRing S] [Field K]

/-- A relative separable-closure realization for the residue-field map
induced by a local ring homomorphism.  The generic realization is the primary
owner; this abbreviation only fixes its base field map. -/
@[stacks 04GW "local residue-field separable-closure model"]
noncomputable abbrev LocalModel (a : L →+* S) [IsLocalHom a] :=
  RingHom.SeparableClosure.Realization (K := K)
    (IsLocalRing.ResidueField.map a)

namespace LocalModel

variable {a : L →+* S} [IsLocalHom a]

/-- The prescribed map from the base residue field in a local residue-field
model.  This is the source-facing name for the generic realization's
`baseMap` projection. -/
@[stacks 04GW "base residue map of a local residue-field model"]
noncomputable abbrev residueMap
    (model : LocalModel (K := K) a) :
    IsLocalRing.ResidueField L →+* K :=
  model.baseMap

/-- The realization of the target residue field in a local residue-field
model.  This is the source-facing name for the generic realization's `lift`
projection. -/
@[stacks 04GW "target residue lift of a local residue-field model"]
noncomputable abbrev residueLift
    (model : LocalModel (K := K) a) :
    IsLocalRing.ResidueField S →+* K :=
  model.lift

/-- Build a residue-field model from a local map of the target into the common
field.  This is a bridge for source constructions that begin before passage
to residue fields; the resulting model retains only the generic field-level
realization data. -/
@[stacks 04GW "local-map construction of a residue-field model"]
noncomputable def ofLocalMap
    (residueMap : IsLocalRing.ResidueField L →+* K) (toField : S →+* K)
    [IsLocalHom toField]
    (residue_comm :
      (IsLocalRing.ResidueField.lift toField).comp
        (IsLocalRing.ResidueField.map a) = residueMap)
    (fieldRange_eq :
      (IsLocalRing.ResidueField.lift toField).fieldRange =
        RingHom.separableClosure residueMap) :
    LocalModel (K := K) a where
  baseMap := residueMap
  lift := IsLocalRing.ResidueField.lift toField
  comm := residue_comm
  fieldRange_eq := fieldRange_eq

/-- The base residue-field map of `ofLocalMap` is the map supplied to that
source-facing bridge. -/
@[simp, stacks 04GW "base residue map of a local-map model"]
theorem ofLocalMap_residueMap
    (residueMap : IsLocalRing.ResidueField L →+* K) (toField : S →+* K)
    [IsLocalHom toField]
    (residue_comm :
      (IsLocalRing.ResidueField.lift toField).comp
        (IsLocalRing.ResidueField.map a) = residueMap)
    (fieldRange_eq :
      (IsLocalRing.ResidueField.lift toField).fieldRange =
        RingHom.separableClosure residueMap) :
    (ofLocalMap (a := a) residueMap toField residue_comm fieldRange_eq).residueMap =
      residueMap := sorry

/-- The residue-field realization of `ofLocalMap` is the canonical lift of
the supplied local map. -/
@[simp, stacks 04GW "residue lift of a local-map model"]
theorem ofLocalMap_residueLift
    (residueMap : IsLocalRing.ResidueField L →+* K) (toField : S →+* K)
    [IsLocalHom toField]
    (residue_comm :
      (IsLocalRing.ResidueField.lift toField).comp
        (IsLocalRing.ResidueField.map a) = residueMap)
    (fieldRange_eq :
      (IsLocalRing.ResidueField.lift toField).fieldRange =
        RingHom.separableClosure residueMap) :
    (ofLocalMap (a := a) residueMap toField residue_comm fieldRange_eq).residueLift =
      IsLocalRing.ResidueField.lift toField := sorry

/-- The local-ring map induced by a residue-field realization before passage
to the residue field. -/
@[stacks 04GW "local map induced by a residue-field model"]
noncomputable def toField
    (model : LocalModel (K := K) a) : S →+* K :=
  model.residueLift.comp (IsLocalRing.residue S)

/-- The local-ring map induced from a residue-field realization is local. -/
@[stacks 04GW "locality of the map induced by a residue-field model"]
instance isLocalHom_toField
    (model : LocalModel (K := K) a) :
    IsLocalHom model.toField := sorry

/-- Recover the supplied local map after constructing a model with
`ofLocalMap`. -/
@[simp, stacks 04GW "underlying local map of a local-map model"]
theorem ofLocalMap_toField
    (residueMap : IsLocalRing.ResidueField L →+* K) (toField : S →+* K)
    [IsLocalHom toField]
    (residue_comm :
      (IsLocalRing.ResidueField.lift toField).comp
        (IsLocalRing.ResidueField.map a) = residueMap)
    (fieldRange_eq :
      (IsLocalRing.ResidueField.lift toField).fieldRange =
        RingHom.separableClosure residueMap) :
    (ofLocalMap (a := a) residueMap toField residue_comm fieldRange_eq).toField =
      toField := sorry

/-- The field realization of a local model recovers its induced map from the
local target after the residue map. -/
@[stacks 04GW "residue-factorization of a local residue-field model"]
theorem residueLift_comp_residue
    (model : LocalModel (K := K) a) :
    model.residueLift.comp (IsLocalRing.residue S) = model.toField := sorry

/-- The field realization of a local model agrees with its induced map from
the local target on residue classes. -/
@[simp, stacks 04GW "residue-class evaluation of a local residue-field model"]
theorem residueLift_apply_residue
    (model : LocalModel (K := K) a) (x : S) :
    model.residueLift (IsLocalRing.residue S x) = model.toField x := sorry

end LocalModel

namespace LocalModel

section CommonField

variable {R : Type u} {S : Type v} {A : Type x} {B : Type y} {K : Type w}
variable [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
variable [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B] [Field K]
variable {base : R →+* S} [IsLocalHom base]
variable {source : R →+* A} [IsLocalHom source]
variable {target : S →+* B} [IsLocalHom target]

/-- The generic compatible field map between two realizations specializes to
a compatible prescribed residue-field map over a local cospan. -/
@[stacks 04GW "compatible map between local residue-field models"]
theorem existsUniqueCompatible
    (sourceModel : LocalModel (K := K) source)
    (targetModel : LocalModel (K := K) target)
    (base_comm :
      targetModel.residueMap.comp (IsLocalRing.ResidueField.map base) =
        sourceModel.residueMap) :
    ∃! residueMap : IsLocalRing.ResidueField A →+* IsLocalRing.ResidueField B,
      IsLocalRing.ResidueField.Compatible base source target residueMap ∧
        targetModel.residueLift.comp residueMap = sourceModel.residueLift := sorry

end CommonField

end LocalModel

end IsLocalRing.ResidueField
