module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import stacks_project.Chap62.Lemma_62_4_3_BaseChange
public import stacks_project.Chap62.Lemma_62_4_5_Specialization

/-!
# Fibrewise flat pullback of cycles over a discrete valuation ring

This file names the vertical arrows of the specialization square for a flat
morphism of relative dimension `e` over a discrete valuation ring: flat
pullback of cycles along the induced maps of generic and special fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The residue-field structure morphism of a fibre, viewed as an `Over` object,
is locally of finite type when the ambient morphism is. -/
instance instLocallyOfFiniteType_overMk_fiberToSpecResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (Over.mk (f.fiberToSpecResidueField s)).hom :=
  instLocallyOfFiniteType_fiberToSpecResidueField f s

/-- A flat morphism of schemes over a domain induces a flat morphism of generic
fibres. -/
instance instFlat_genericFiberMap {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [Flat f.left] :
    Flat (genericFiberMap f) := sorry

/-- A flat morphism of schemes over a local ring induces a flat morphism of
special fibres. -/
instance instFlat_specialFiberMap {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [Flat f.left] :
    Flat (specialFiberMap f) := sorry

/-- A morphism of schemes over a domain of relative dimension `e` induces a
morphism of generic fibres of the same relative dimension. -/
instance instRelativeDimension_genericFiberMap {R : Type u} [CommRing R]
    [IsDomain R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (e : ℕ)
    [RelativeDimension f.left e] :
    RelativeDimension (genericFiberMap f) e := sorry

/-- A morphism of schemes over a local ring of relative dimension `e` induces a
morphism of special fibres of the same relative dimension. -/
instance instRelativeDimension_specialFiberMap {R : Type u} [CommRing R]
    [IsLocalRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) (e : ℕ)
    [RelativeDimension f.left e] :
    RelativeDimension (specialFiberMap f) e := sorry

/-- The underlying map of `Over.homMk φ` is flat when `φ` is flat. -/
instance instFlat_overHomMk {S X Y : Scheme.{u}} {pX : X ⟶ S} {pY : Y ⟶ S}
    (φ : X ⟶ Y) (hφ : φ ≫ pY = pX) [Flat φ] :
    Flat (Over.homMk φ hφ : Over.mk pX ⟶ Over.mk pY).left := sorry

/-- The underlying map of `Over.homMk φ` has the same relative dimension as `φ`. -/
instance instRelativeDimension_overHomMk {S X Y : Scheme.{u}} {pX : X ⟶ S}
    {pY : Y ⟶ S} (φ : X ⟶ Y) (hφ : φ ≫ pY = pX) (e : ℕ)
    [RelativeDimension φ e] :
    RelativeDimension (Over.homMk φ hφ : Over.mk pX ⟶ Over.mk pY).left e :=
  sorry

/-- The morphism of generic fibres commutes with the residue-field structure
morphisms. -/
theorem genericFiberMap_fiberToSpecResidueField {R : Type u} [CommRing R]
    [IsDomain R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    genericFiberMap f ≫
        Y.hom.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R))) =
      X.hom.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R))) :=
  sorry

/-- The morphism of special fibres commutes with the residue-field structure
morphisms. -/
theorem specialFiberMap_fiberToSpecResidueField {R : Type u} [CommRing R]
    [IsLocalRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    specialFiberMap f ≫
        Y.hom.fiberToSpecResidueField (IsLocalRing.closedPoint R) =
      X.hom.fiberToSpecResidueField (IsLocalRing.closedPoint R) := sorry

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.CycleGroup

/-- Flat pullback of `r`-cycles along the map of generic fibres induced by a
morphism of relative dimension `e` over a discrete valuation ring. -/
noncomputable def genericFiberFlatPullback
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    CycleGroup X.hom.genericFiber
        (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r →+
      CycleGroup X'.hom.genericFiber
        (X'.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))))
        (r + e) :=
  let s := genericPoint (Spec (CommRingCat.of R))
  flatPullback (fun _ ↦ 0) (Over.mk (X'.hom.fiberToSpecResidueField s))
    (Over.mk (X.hom.fiberToSpecResidueField s))
    (Over.homMk (genericFiberMap f) (genericFiberMap_fiberToSpecResidueField f)) e r

/-- Flat pullback of `r`-cycles along the map of special fibres induced by a
morphism of relative dimension `e` over a discrete valuation ring. -/
noncomputable def specialFiberFlatPullback
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    CycleGroup X.hom.specialFiber
        (X.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) r →+
      CycleGroup X'.hom.specialFiber
        (X'.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) (r + e) :=
  let s := IsLocalRing.closedPoint R
  flatPullback (fun _ ↦ 0) (Over.mk (X'.hom.fiberToSpecResidueField s))
    (Over.mk (X.hom.fiberToSpecResidueField s))
    (Over.homMk (specialFiberMap f) (specialFiberMap_fiberToSpecResidueField f)) e r

/-- Unfolding `genericFiberFlatPullback` as flat pullback of `genericFiberMap`
over the residue field of the generic point. -/
theorem genericFiberFlatPullback_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    genericFiberFlatPullback f e r =
      let s := genericPoint (Spec (CommRingCat.of R))
      flatPullback (fun _ ↦ 0) (Over.mk (X'.hom.fiberToSpecResidueField s))
        (Over.mk (X.hom.fiberToSpecResidueField s))
        (Over.homMk (genericFiberMap f) (genericFiberMap_fiberToSpecResidueField f))
        e r := sorry

/-- Unfolding `specialFiberFlatPullback` as flat pullback of `specialFiberMap`
over the residue field of the closed point. -/
theorem specialFiberFlatPullback_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    specialFiberFlatPullback f e r =
      let s := IsLocalRing.closedPoint R
      flatPullback (fun _ ↦ 0) (Over.mk (X'.hom.fiberToSpecResidueField s))
        (Over.mk (X.hom.fiberToSpecResidueField s))
        (Over.homMk (specialFiberMap f) (specialFiberMap_fiberToSpecResidueField f))
        e r := sorry

/-- Evaluating generic-fibre flat pullback on an `r`-cycle. -/
theorem genericFiberFlatPullback_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ)
    (α : CycleGroup X.hom.genericFiber
      (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    genericFiberFlatPullback f e r α =
      let s := genericPoint (Spec (CommRingCat.of R))
      flatPullback (fun _ ↦ 0) (Over.mk (X'.hom.fiberToSpecResidueField s))
        (Over.mk (X.hom.fiberToSpecResidueField s))
        (Over.homMk (genericFiberMap f) (genericFiberMap_fiberToSpecResidueField f))
        e r α := sorry

/-- Evaluating special-fibre flat pullback on an `r`-cycle. -/
theorem specialFiberFlatPullback_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ)
    (α : CycleGroup X.hom.specialFiber
      (X.hom.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) :
    specialFiberFlatPullback f e r α =
      let s := IsLocalRing.closedPoint R
      flatPullback (fun _ ↦ 0) (Over.mk (X'.hom.fiberToSpecResidueField s))
        (Over.mk (X.hom.fiberToSpecResidueField s))
        (Over.homMk (specialFiberMap f) (specialFiberMap_fiberToSpecResidueField f))
        e r α := sorry

end AlgebraicGeometry.CycleGroup
