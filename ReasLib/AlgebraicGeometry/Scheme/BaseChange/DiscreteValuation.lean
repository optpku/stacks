module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic

/-!
# Generic and special fibres under discrete valuation ring extensions

Affine base change along an extension of discrete valuation rings preserves
both the generic and closed points. Their residue-field maps give flat spectrum
morphisms, and point preservation identifies the corresponding fibres.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AffineBaseChange

/-- The spectrum map of a discrete valuation ring extension sends the generic
point of `Spec R'` to the generic point of `Spec R`. -/
theorem specMap_genericPoint (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R'] :
    specMap R R' (genericPoint (Spec (CommRingCat.of R'))) =
      genericPoint (Spec (CommRingCat.of R)) := sorry

/-- The spectrum map of a discrete valuation ring extension sends the closed
point of `Spec R'` to the closed point of `Spec R`. -/
theorem specMap_closedPoint (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R'] :
    specMap R R' (IsLocalRing.closedPoint R') = IsLocalRing.closedPoint R := sorry

/-- The residue-field spectrum map of `Spec R' ⟶ Spec R` at the generic point
of `Spec R'` is flat. -/
instance instFlat_specMap_residueFieldMap_genericPoint (R R' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R'] :
    Flat (Spec.map ((specMap R R').residueFieldMap
      (genericPoint (Spec (CommRingCat.of R'))))) :=
  (Flat.SpecMap_iff
      (f := (specMap R R').residueFieldMap
        (genericPoint (Spec (CommRingCat.of R'))))).2
    (RingHom.Flat.of_isField (Field.toIsField _)
      ((specMap R R').residueFieldMap
        (genericPoint (Spec (CommRingCat.of R')))).hom)

/-- The residue-field spectrum map of `Spec R' ⟶ Spec R` at the closed point
of `Spec R'` is flat. -/
instance instFlat_specMap_residueFieldMap_closedPoint (R R' : Type u)
    [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R'] :
    Flat (Spec.map ((specMap R R').residueFieldMap (IsLocalRing.closedPoint R'))) :=
  (Flat.SpecMap_iff
      (f := (specMap R R').residueFieldMap (IsLocalRing.closedPoint R'))).2
    (RingHom.Flat.of_isField (Field.toIsField _)
      ((specMap R R').residueFieldMap (IsLocalRing.closedPoint R')).hom)

/-- The comparison morphism of fibres of `f` along the identification of generic
points of `Spec R'` and `Spec R`. -/
noncomputable def genericFiberPointHom (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.genericFiber ⟶
      f.fiber (specMap R R' (genericPoint (Spec (CommRingCat.of R')))) :=
  eqToHom (congrArg f.fiber (specMap_genericPoint R R').symm)

/-- The generic-fibre comparison morphism is quasi-compact. -/
instance instQuasiCompact_genericFiberPointHom (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    QuasiCompact (genericFiberPointHom R R' f) :=
  inferInstanceAs (QuasiCompact (eqToHom (congrArg f.fiber (specMap_genericPoint R R').symm)))

/-- The comparison morphism of fibres of `f` along the identification of closed
points of `Spec R'` and `Spec R`. -/
noncomputable def specialFiberPointHom (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiber ⟶ f.fiber (specMap R R' (IsLocalRing.closedPoint R')) :=
  eqToHom (congrArg f.fiber (specMap_closedPoint R R').symm)

/-- The special-fibre comparison morphism is quasi-compact. -/
instance instQuasiCompact_specialFiberPointHom (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    QuasiCompact (specialFiberPointHom R R' f) :=
  inferInstanceAs (QuasiCompact (eqToHom (congrArg f.fiber (specMap_closedPoint R R').symm)))

/-- `genericFiberPointHom` is the `eqToHom` comparison of fibres at the generic
points. -/
theorem genericFiberPointHom_eq (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    genericFiberPointHom R R' f =
      eqToHom (congrArg f.fiber (specMap_genericPoint R R').symm) := sorry

/-- `specialFiberPointHom` is the `eqToHom` comparison of fibres at the closed
points. -/
theorem specialFiberPointHom_eq (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    specialFiberPointHom R R' f =
      eqToHom (congrArg f.fiber (specMap_closedPoint R R').symm) := sorry

end AlgebraicGeometry.Scheme.AffineBaseChange
