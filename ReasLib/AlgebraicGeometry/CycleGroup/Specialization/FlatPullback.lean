/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.GenericSpecialMap

/-!
# Specialization and fibrewise flat pullback

Flat pullback along the induced maps of generic and special fibres commutes
with specialization of cycles over a discrete valuation ring.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

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
  @flatPullback _ _ (fun _ ↦ 0) _
    (Over.mk (X'.hom.fiberToSpecResidueField s)) (Over.mk (X.hom.fiberToSpecResidueField s))
    (instLocallyOfFiniteType_fiberToSpecResidueField X'.hom s) (instLocallyOfFiniteType_fiberToSpecResidueField X.hom s)
    (Over.homMk (genericFiberMap f) (genericFiberMap_fiberToSpecResidueField f)) e
    (instFlat_genericFiberMap f) (instRelativeDimension_genericFiberMap f e) r

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
  @flatPullback _ _ (fun _ ↦ 0) _
    (Over.mk (X'.hom.fiberToSpecResidueField s)) (Over.mk (X.hom.fiberToSpecResidueField s))
    (instLocallyOfFiniteType_fiberToSpecResidueField X'.hom s) (instLocallyOfFiniteType_fiberToSpecResidueField X.hom s)
    (Over.homMk (specialFiberMap f) (specialFiberMap_fiberToSpecResidueField f)) e
    (instFlat_specialFiberMap f) (instRelativeDimension_specialFiberMap f e) r

/-- Generic-fibre flat pullback is flat pullback of the induced fibre morphism
over the residue field of the generic point. -/
theorem genericFiberFlatPullback_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    genericFiberFlatPullback f e r =
      let s := genericPoint (Spec (CommRingCat.of R))
      @flatPullback _ _ (fun _ ↦ 0) _
        (Over.mk (X'.hom.fiberToSpecResidueField s)) (Over.mk (X.hom.fiberToSpecResidueField s))
        (instLocallyOfFiniteType_fiberToSpecResidueField X'.hom s) (instLocallyOfFiniteType_fiberToSpecResidueField X.hom s)
        (Over.homMk (genericFiberMap f) (genericFiberMap_fiberToSpecResidueField f)) e
        (instFlat_genericFiberMap f) (instRelativeDimension_genericFiberMap f e) r := sorry

/-- Special-fibre flat pullback is flat pullback of the induced fibre morphism
over the residue field of the closed point. -/
theorem specialFiberFlatPullback_eq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    specialFiberFlatPullback f e r =
      let s := IsLocalRing.closedPoint R
      @flatPullback _ _ (fun _ ↦ 0) _
        (Over.mk (X'.hom.fiberToSpecResidueField s)) (Over.mk (X.hom.fiberToSpecResidueField s))
        (instLocallyOfFiniteType_fiberToSpecResidueField X'.hom s) (instLocallyOfFiniteType_fiberToSpecResidueField X.hom s)
        (Over.homMk (specialFiberMap f) (specialFiberMap_fiberToSpecResidueField f)) e
        (instFlat_specialFiberMap f) (instRelativeDimension_specialFiberMap f e) r := sorry

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
      @flatPullback _ _ (fun _ ↦ 0) _
        (Over.mk (X'.hom.fiberToSpecResidueField s)) (Over.mk (X.hom.fiberToSpecResidueField s))
        (instLocallyOfFiniteType_fiberToSpecResidueField X'.hom s) (instLocallyOfFiniteType_fiberToSpecResidueField X.hom s)
        (Over.homMk (genericFiberMap f) (genericFiberMap_fiberToSpecResidueField f)) e
        (instFlat_genericFiberMap f) (instRelativeDimension_genericFiberMap f e) r α := sorry

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
      @flatPullback _ _ (fun _ ↦ 0) _
        (Over.mk (X'.hom.fiberToSpecResidueField s)) (Over.mk (X.hom.fiberToSpecResidueField s))
        (instLocallyOfFiniteType_fiberToSpecResidueField X'.hom s) (instLocallyOfFiniteType_fiberToSpecResidueField X.hom s)
        (Over.homMk (specialFiberMap f) (specialFiberMap_fiberToSpecResidueField f)) e
        (instFlat_specialFiberMap f) (instRelativeDimension_specialFiberMap f e) r α := sorry

/-- Specialization of cycles over a discrete valuation ring commutes with flat
pullback along a morphism of relative dimension `e`, as an equality of additive
homomorphisms from generic-fibre `r`-cycles to special-fibre `(r + e)`-cycles. -/
theorem cycleSpecialization_comp_flatPullback
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ) :
    (X'.hom.cycleSpecialization (r + e)).comp (genericFiberFlatPullback f e r) =
      (specialFiberFlatPullback f e r).comp (X.hom.cycleSpecialization r) := sorry

/-- Specialization of an `r`-cycle on the generic fibre, then flat pullback on
the special fibre, agrees with flat pullback on the generic fibre followed by
specialization. -/
theorem cycleSpecialization_flatPullback
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Over (Spec (CommRingCat.of R))}
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType X'.hom]
    (f : X' ⟶ X) (e : ℕ) [Flat f.left] [RelativeDimension f.left e] (r : ℕ)
    (α : CycleGroup X.hom.genericFiber
      (X.hom.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    X'.hom.cycleSpecialization (r + e) (genericFiberFlatPullback f e r α) =
      specialFiberFlatPullback f e r (X.hom.cycleSpecialization r α) := sorry

end AlgebraicGeometry.CycleGroup
