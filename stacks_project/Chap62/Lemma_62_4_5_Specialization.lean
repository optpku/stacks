module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import stacks_project.Chap62.Lemma_62_4_1_Specialization

/-!
# Induced maps of generic and special fibres

This file names the morphisms of generic and special fibres induced by a
morphism of schemes over a discrete valuation ring, as fibre maps of the
identity square on `Spec R`.
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

end AlgebraicGeometry.Scheme.Hom
