/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Induced maps of generic and special fibres

Morphisms of schemes over a domain or a local ring induce morphisms of their
generic or special fibres, respectively. Properness is preserved on these fibres.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The morphism of generic fibres induced by a morphism of schemes over a domain. -/
noncomputable def genericFiberMap {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    X.hom.genericFiber ⟶ Y.hom.genericFiber :=
  fiberMap X.hom f.left (𝟙 (Spec (CommRingCat.of R))) Y.hom
    ⟨(Over.w f).trans (Category.comp_id X.hom).symm⟩
    (genericPoint (Spec (CommRingCat.of R)))

/-- `genericFiberMap` is the fibre morphism of the identity square on `Spec R` at
the generic point. -/
theorem genericFiberMap_eq {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    genericFiberMap f =
      fiberMap X.hom f.left (𝟙 (Spec (CommRingCat.of R))) Y.hom
        ⟨(Over.w f).trans (Category.comp_id X.hom).symm⟩
        (genericPoint (Spec (CommRingCat.of R))) := sorry

/-- The morphism of generic fibres is compatible with the immersions into the
ambient schemes. -/
theorem genericFiberMap_fiberι {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    genericFiberMap f ≫ Y.hom.genericFiberι = X.hom.genericFiberι ≫ f.left := sorry

/-- A proper morphism of schemes over a domain induces a proper morphism of
generic fibres. -/
instance instIsProper_genericFiberMap {R : Type u} [CommRing R] [IsDomain R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsProper f.left] :
    IsProper (genericFiberMap f) := sorry

/-- The morphism of special fibres induced by a morphism of schemes over a local
ring. -/
noncomputable def specialFiberMap {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    X.hom.specialFiber ⟶ Y.hom.specialFiber :=
  fiberMap X.hom f.left (𝟙 (Spec (CommRingCat.of R))) Y.hom
    ⟨(Over.w f).trans (Category.comp_id X.hom).symm⟩
    (IsLocalRing.closedPoint R)

/-- `specialFiberMap` is the fibre morphism of the identity square on `Spec R` at
the closed point. -/
theorem specialFiberMap_eq {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    specialFiberMap f =
      fiberMap X.hom f.left (𝟙 (Spec (CommRingCat.of R))) Y.hom
        ⟨(Over.w f).trans (Category.comp_id X.hom).symm⟩
        (IsLocalRing.closedPoint R) := sorry

/-- The morphism of special fibres is compatible with the immersions into the
ambient schemes. -/
theorem specialFiberMap_fiberι {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    specialFiberMap f ≫ Y.hom.specialFiberι = X.hom.specialFiberι ≫ f.left := sorry

/-- A proper morphism of schemes over a local ring induces a proper morphism of
special fibres. -/
instance instIsProper_specialFiberMap {R : Type u} [CommRing R] [IsLocalRing R]
    {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) [IsProper f.left] :
    IsProper (specialFiberMap f) := sorry

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

/-- The morphism of generic fibres commutes with the residue-field structure
morphisms. -/
theorem genericFiberMap_fiberToSpecResidueField {R : Type u} [CommRing R]
    [IsDomain R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    genericFiberMap f ≫
        Y.hom.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R))) =
      X.hom.fiberToSpecResidueField (genericPoint (Spec (CommRingCat.of R))) := sorry

/-- The morphism of special fibres commutes with the residue-field structure
morphisms. -/
theorem specialFiberMap_fiberToSpecResidueField {R : Type u} [CommRing R]
    [IsLocalRing R] {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    specialFiberMap f ≫
        Y.hom.fiberToSpecResidueField (IsLocalRing.closedPoint R) =
      X.hom.fiberToSpecResidueField (IsLocalRing.closedPoint R) := sorry

end AlgebraicGeometry.Scheme.Hom
