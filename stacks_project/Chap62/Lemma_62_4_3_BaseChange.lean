module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatBaseChange
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction.FlatCompatibility
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap62.Lemma_62_4_1_Specialization

/-!
# Field-extension base change of generic and special fibres

This file names the vertical arrows of the specialization square for an
extension of discrete valuation rings: pullback of `r`-cycles along the
residue-field maps of `Spec R' ⟶ Spec R` at the generic and closed points,
transported to the fibres of `X' = X_{R'}`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The structure morphism of a scheme-theoretic fibre is locally of finite type
when the ambient morphism is. -/
instance instLocallyOfFiniteType_fiberToSpecResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))

end AlgebraicGeometry.Scheme.Hom

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

/-- The spectrum of the residue field of any scheme point is `T₁`. -/
instance instT1Space_specResidueField {X : Scheme.{u}} (x : X) :
    T1Space (Spec (X.residueField x)) := sorry

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

/-- Residue-field spectrum maps at the generic point of `Spec R'` are compatible
with the constant-zero dimension functions, with shift `0`. -/
theorem isDimensionFunctionCompatible_specMap_residueFieldMap_genericPoint
    (R R' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R'] :
    IsDimensionFunctionCompatible
      (Spec.map ((specMap R R').residueFieldMap
        (genericPoint (Spec (CommRingCat.of R')))))
      (fun _ ↦ 0) (fun _ ↦ 0) 0 := sorry

/-- Residue-field spectrum maps at the closed point of `Spec R'` are compatible
with the constant-zero dimension functions, with shift `0`. -/
theorem isDimensionFunctionCompatible_specMap_residueFieldMap_closedPoint
    (R R' : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R'] :
    IsDimensionFunctionCompatible
      (Spec.map ((specMap R R').residueFieldMap (IsLocalRing.closedPoint R')))
      (fun _ ↦ 0) (fun _ ↦ 0) 0 := sorry

end AlgebraicGeometry.Scheme.AffineBaseChange

namespace AlgebraicGeometry.CycleGroup

open AlgebraicGeometry.Scheme.AffineBaseChange

/-- An isomorphism of schemes is quasi-compact. -/
instance instQuasiCompact_iso_hom {X Y : Scheme.{u}} (e : X ≅ Y) :
    QuasiCompact e.hom :=
  MorphismProperty.of_isIso (@QuasiCompact) e.hom

/-- The inverse of an isomorphism of schemes is quasi-compact. -/
instance instQuasiCompact_iso_inv {X Y : Scheme.{u}} (e : X ≅ Y) :
    QuasiCompact e.inv :=
  MorphismProperty.of_isIso (@QuasiCompact) e.inv

/-- Equalities of schemes induce quasi-compact comparison morphisms. -/
instance instQuasiCompact_eqToHom {X Y : Scheme.{u}} (h : X = Y) :
    QuasiCompact (eqToHom h) :=
  MorphismProperty.of_isIso (@QuasiCompact) (eqToHom h)

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

/-- Field-extension base change of `r`-cycles from the generic fibre `X_K` to
the generic fibre `X'_{K'}` of `X' = X_{R'}`. -/
noncomputable def genericFiberBaseChange (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    CycleGroup f.genericFiber
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r →+
      CycleGroup (toBase R R' f).genericFiber
        ((toBase R R' f).fiberDimensionFunction
          (genericPoint (Spec (CommRingCat.of R')))) r :=
  let g := specMap R R'
  let s' := genericPoint (Spec (CommRingCat.of R'))
  let dPull :=
    (pullback.snd (f.fiberToSpecResidueField (g s'))
        (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
      (fun _ ↦ 0)
  (mapHom
        (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
            (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
        dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
    ((reindex dPull (add_zero (r : ℤ))).comp
      ((baseChangePullback (Spec.map (g.residueFieldMap s'))
          (fun _ ↦ 0) (fun _ ↦ 0) 0
          (isDimensionFunctionCompatible_specMap_residueFieldMap_genericPoint R R')
          (f.fiberToSpecResidueField (g s')) r).comp
        (mapHom (genericFiberPointHom R R' f)
          (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
          (f.fiberDimensionFunction (g s')) r)))

/-- Field-extension base change of `r`-cycles from the special fibre `X_κ` to
the special fibre `X'_{κ'}` of `X' = X_{R'}`. -/
noncomputable def specialFiberBaseChange (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    CycleGroup f.specialFiber
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r →+
      CycleGroup (toBase R R' f).specialFiber
        ((toBase R R' f).fiberDimensionFunction (IsLocalRing.closedPoint R')) r :=
  let g := specMap R R'
  let s' := IsLocalRing.closedPoint R'
  let dPull :=
    (pullback.snd (f.fiberToSpecResidueField (g s'))
        (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
      (fun _ ↦ 0)
  (mapHom
        (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
            (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
        dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
    ((reindex dPull (add_zero (r : ℤ))).comp
      ((baseChangePullback (Spec.map (g.residueFieldMap s'))
          (fun _ ↦ 0) (fun _ ↦ 0) 0
          (isDimensionFunctionCompatible_specMap_residueFieldMap_closedPoint R R')
          (f.fiberToSpecResidueField (g s')) r).comp
        (mapHom (specialFiberPointHom R R' f)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R))
          (f.fiberDimensionFunction (g s')) r)))

/-- Unfolding `genericFiberBaseChange` as residue-field pullback, reindexing
`r + 0 = r`, and transport along the fibre identification. -/
theorem genericFiberBaseChange_eq (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    genericFiberBaseChange R R' f r =
      let g := specMap R R'
      let s' := genericPoint (Spec (CommRingCat.of R'))
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      (mapHom
            (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
                (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
            dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
        ((reindex dPull (add_zero (r : ℤ))).comp
          ((baseChangePullback (Spec.map (g.residueFieldMap s'))
              (fun _ ↦ 0) (fun _ ↦ 0) 0
              (isDimensionFunctionCompatible_specMap_residueFieldMap_genericPoint R R')
              (f.fiberToSpecResidueField (g s')) r).comp
            (mapHom (genericFiberPointHom R R' f)
              (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
              (f.fiberDimensionFunction (g s')) r))) := sorry

/-- Unfolding `specialFiberBaseChange` as residue-field pullback, reindexing
`r + 0 = r`, and transport along the fibre identification. -/
theorem specialFiberBaseChange_eq (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ) :
    specialFiberBaseChange R R' f r =
      let g := specMap R R'
      let s' := IsLocalRing.closedPoint R'
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      (mapHom
            (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
                (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
            dPull ((toBase R R' f).fiberDimensionFunction s') r).comp
        ((reindex dPull (add_zero (r : ℤ))).comp
          ((baseChangePullback (Spec.map (g.residueFieldMap s'))
              (fun _ ↦ 0) (fun _ ↦ 0) 0
              (isDimensionFunctionCompatible_specMap_residueFieldMap_closedPoint R R')
              (f.fiberToSpecResidueField (g s')) r).comp
            (mapHom (specialFiberPointHom R R' f)
              (f.fiberDimensionFunction (IsLocalRing.closedPoint R))
              (f.fiberDimensionFunction (g s')) r))) := sorry

/-- Evaluating generic-fibre field-extension base change on an `r`-cycle. -/
theorem genericFiberBaseChange_apply (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    genericFiberBaseChange R R' f r α =
      let g := specMap R R'
      let s' := genericPoint (Spec (CommRingCat.of R'))
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      mapHom
          (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
              (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
          dPull ((toBase R R' f).fiberDimensionFunction s') r
        (reindex dPull (add_zero (r : ℤ))
          (baseChangePullback (Spec.map (g.residueFieldMap s'))
            (fun _ ↦ 0) (fun _ ↦ 0) 0
            (isDimensionFunctionCompatible_specMap_residueFieldMap_genericPoint R R')
            (f.fiberToSpecResidueField (g s')) r
            (mapHom (genericFiberPointHom R R' f)
              (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
              (f.fiberDimensionFunction (g s')) r α))) := sorry

/-- Evaluating special-fibre field-extension base change on an `r`-cycle. -/
theorem specialFiberBaseChange_apply (R R' : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    [Algebra R R'] [IsExtensionOfDiscreteValuationRings R R']
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (r : ℕ)
    (α : CycleGroup f.specialFiber
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) :
    specialFiberBaseChange R R' f r α =
      let g := specMap R R'
      let s' := IsLocalRing.closedPoint R'
      let dPull :=
        (pullback.snd (f.fiberToSpecResidueField (g s'))
            (Spec.map (g.residueFieldMap s'))).relativeDimensionFunction
          (fun _ ↦ 0)
      mapHom
          (isPullback_baseChangeFiberMap f g (toSource R R' f) (toBase R R' f)
              (IsPullback.of_hasPullback f g) s').isoPullback.symm.hom
          dPull ((toBase R R' f).fiberDimensionFunction s') r
        (reindex dPull (add_zero (r : ℤ))
          (baseChangePullback (Spec.map (g.residueFieldMap s'))
            (fun _ ↦ 0) (fun _ ↦ 0) 0
            (isDimensionFunctionCompatible_specMap_residueFieldMap_closedPoint R R')
            (f.fiberToSpecResidueField (g s')) r
            (mapHom (specialFiberPointHom R R' f)
              (f.fiberDimensionFunction (IsLocalRing.closedPoint R))
              (f.fiberDimensionFunction (g s')) r α))) := sorry

end AlgebraicGeometry.CycleGroup
