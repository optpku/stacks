/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.IdealSystem
public import ReasLib.AlgebraicGeometry.FormalScheme.Size
public import ReasLib.AlgebraicGeometry.FormalScheme.Affine
public import ReasLib.AlgebraicGeometry.FormalSpectrum.GlobalSections

/-!
# Ideal sheaves and ideals of definition on EGA formal schemes
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open AlgebraicGeometry.Spec (structureSheaf)
open TopologicalRing

namespace AlgebraicGeometry.FormalScheme

/-- Affine formal opens of an EGA formal scheme have admissible section rings. -/
instance instIsAdmissibleRing_sections {X : FormalScheme.{u}} (U : X.affineOpens) :
    IsAdmissibleRing (X.presheaf.obj (op U.1) : Type u) :=
  sorry

/-- An ideal sheaf on a EGA formal scheme, recorded by its ideals of
sections on formal affine opens together with restriction closure and local membership descent. -/
structure IdealSheafData (X : FormalScheme.{u}) where
  /-- The component of the ideal sheaf at a formal affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u)
  /-- Restriction sends an ideal component into the smaller affine-open component. -/
  map_ideal :
    ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
      (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U

  /-- Membership descends along affine covers of an affine open. -/
  local_mem : ∀ (U : X.affineOpens) (𝒰 : X.affineOpens → Prop)
    (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
    (hcover : ⨆ (V : X.affineOpens) (_ : 𝒰 V), V.1 = U.1)
    (f : (X.presheaf.obj (op U.1) : Type u)),
    (∀ (V : X.affineOpens) (hV : 𝒰 V),
      (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ ideal V) → f ∈ ideal U

/-- Construct ideal-sheaf data from an affine-open family of ideals together
with the restriction-compatibility of an ideal sheaf. -/
def IdealSheafData.of {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U)
    (local_mem : ∀ (U : X.affineOpens) (𝒰 : X.affineOpens → Prop)
      (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
      (hcover : ⨆ (V : X.affineOpens) (_ : 𝒰 V), V.1 = U.1)
      (f : (X.presheaf.obj (op U.1) : Type u)),
      (∀ (V : X.affineOpens) (hV : 𝒰 V),
        (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ ideal V) → f ∈ ideal U) :
    IdealSheafData X where
  ideal := ideal
  map_ideal := map_ideal
  local_mem := local_mem

/-- The smart constructor recovers the given affine-open family of ideals. -/
theorem IdealSheafData.of_spec {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U)
    (local_mem : ∀ (U : X.affineOpens) (𝒰 : X.affineOpens → Prop)
      (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
      (hcover : ⨆ (V : X.affineOpens) (_ : 𝒰 V), V.1 = U.1)
      (f : (X.presheaf.obj (op U.1) : Type u)),
      (∀ (V : X.affineOpens) (hV : 𝒰 V),
        (X.presheaf.map (homOfLE (hle V hV)).op).val f ∈ ideal V) → f ∈ ideal U) :
    (IdealSheafData.of ideal map_ideal local_mem).ideal = ideal :=
  rfl

/-- Restriction compatibility of an ideal sheaf on formal affine opens. -/
theorem IdealSheafData.map_ideal_apply {X : FormalScheme.{u}} (I : IdealSheafData X)
    {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ I.ideal U :=
  I.map_ideal h

/-- The canonical map from an admissible ring to sections on an open of its formal spectrum. -/
def ofSpfSectionHom (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (U : Opens (FormalScheme.ofSpf A hA).carrier) :
    (A : Type u) →+* ((FormalScheme.ofSpf A hA).presheaf.obj (op U) : Type u) :=
  (FormalSpectrum.restriction (show U ≤ ⊤ from le_top)).comp
    (FormalSpectrum.globalSectionsHom A)

/-- Components of `ofSpfSectionHom` are the structure-sheaf algebra maps of
`A ⧸ I`. -/
theorem ofSpfSectionHom_component (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (U : Opens (FormalScheme.ofSpf A hA).carrier) (a : A) (I : Ideal (A : Type u))
    (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (ofSpfSectionHom A hA U a).component I hI =
      algebraMap (A ⧸ I)
        (((structureSheaf (A ⧸ I)).1.obj
            (op (FormalSpectrum.pullbackOpens
              (U : Opens (FormalSpectrum.OpenPrime (A : Type u))) I hI))) : Type u)
        (Ideal.Quotient.mk I a) :=
  sorry

/-- Extending an open ideal to affine section rings respects restriction and affine descent. -/
theorem IdealSheafData.ofSpf_laws (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (I : Ideal (A : Type u)) (hI : IsOpen (I : Set A)) :
    (∀ {U V : (FormalScheme.ofSpf A hA).affineOpens} (h : U.1 ≤ V.1),
      (I.map (ofSpfSectionHom A hA V.1)).map
        ((FormalScheme.ofSpf A hA).presheaf.map (homOfLE h).op).val ≤
          I.map (ofSpfSectionHom A hA U.1)) ∧
    (∀ (U : (FormalScheme.ofSpf A hA).affineOpens) (𝒰 : (FormalScheme.ofSpf A hA).affineOpens → Prop)
    (hle : ∀ V, 𝒰 V → V.1 ≤ U.1)
    (hcover : ⨆ (V : (FormalScheme.ofSpf A hA).affineOpens) (_ : 𝒰 V), V.1 = U.1)
    (f : ((FormalScheme.ofSpf A hA).presheaf.obj (op U.1) : Type u)),
    (∀ (V : (FormalScheme.ofSpf A hA).affineOpens) (hV : 𝒰 V),
      ((FormalScheme.ofSpf A hA).presheaf.map (homOfLE (hle V hV)).op).val f ∈ I.map (ofSpfSectionHom A hA V.1)) → f ∈ I.map (ofSpfSectionHom A hA U.1)) :=
  sorry

/-- The ideal sheaf extending an open ideal of an admissible ring to its formal spectrum. -/
def IdealSheafData.ofSpf (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (I : Ideal (A : Type u)) (hI : IsOpen (I : Set A)) :
    IdealSheafData (FormalScheme.ofSpf A hA) where
  ideal U := I.map (ofSpfSectionHom A hA U.1)
  map_ideal := (IdealSheafData.ofSpf_laws A hA I hI).1
  local_mem := (IdealSheafData.ofSpf_laws A hA I hI).2

/-- On each affine open, extension is the image under the canonical section homomorphism. -/
theorem IdealSheafData.ofSpf_ideal (A : TopCommRingCat.{u}) (hA : IsAdmissibleRing A)
    (I : Ideal (A : Type u)) (hI : IsOpen (I : Set A))
    (U : (FormalScheme.ofSpf A hA).affineOpens) :
    (IdealSheafData.ofSpf A hA I hI).ideal U = I.map (ofSpfSectionHom A hA U.1) :=
  rfl

/-- An ideal sheaf is an ideal of definition when its sections on every formal
affine open are an ideal of definition. -/
def IsIdealOfDefinition {X : FormalScheme.{u}} (I : IdealSheafData X) : Prop :=
  ∀ U : X.affineOpens, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal U)

/-- Unfolding of `IsIdealOfDefinition`. -/
theorem isIdealOfDefinition_iff {X : FormalScheme.{u}} (I : IdealSheafData X) :
    IsIdealOfDefinition I ↔
      ∀ U : X.affineOpens, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal U) :=
  Iff.rfl

/-- Being an ideal of definition may be checked on the members of an affine
open covering. -/
theorem isIdealOfDefinition_iff_affineCover {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤) :
    IsIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsIdealOfDefinition (I.ideal (𝒰 i)) :=
  sorry

/-- The ideal sheaf on `ofSpf A` extending an ideal of definition of `A` is an
ideal of definition. -/
theorem isIdealOfDefinition_ofSpf (A : TopCommRingCat.{u})
    (hA : IsAdmissibleRing A)
    (I : TopologicalRing.IdealOfDefinition A) :
    IsIdealOfDefinition (IdealSheafData.ofSpf A hA I.val I.property.1) :=
  sorry

end AlgebraicGeometry.FormalScheme
