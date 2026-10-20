/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Definition_87_9_9_WeakIdeal
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_FormalScheme
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Neighborhoods
public import stacks_project.Chap87.Remark_87_2_3_McQuillan_s_variant_Spf

/-!
# Weak ideals of definition on McQuillan formal schemes

An ideal sheaf on a McQuillan formal scheme is determined by its values on
formal affine opens, with the restriction-compatibility of an ideal sheaf.
It is a weak ideal of definition when those values are weak ideals of
definition of the weakly admissible section rings.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopologicalSpace Topology AlgebraicGeometry
open AlgebraicGeometry.Spec (structureSheaf)
open TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- Sections of the structure sheaf of a McQuillan formal scheme over an open. -/
abbrev sections (X : FormalScheme.{u}) (U : Opens X.carrier) : Type u :=
  X.presheaf.obj (op U)

/-- Unfolding of `sections`. -/
theorem sections_eq (X : FormalScheme.{u}) (U : Opens X.carrier) :
    sections X U = X.presheaf.obj (op U) :=
  sorry

/-- Affine formal opens of a McQuillan formal scheme have weakly admissible
section rings. -/
instance instIsWeaklyAdmissibleRing_sections {X : FormalScheme.{u}}
    (U : X.affineOpens) :
    IsWeaklyAdmissibleRing (X.presheaf.obj (op U.1) : Type u) :=
  sorry

/-- An ideal sheaf on a McQuillan formal scheme, recorded by its ideals of
sections on formal affine opens together with restriction compatibility. -/
structure IdealSheafData (X : FormalScheme.{u}) where
  /-- The component of the ideal sheaf at a formal affine open. -/
  ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u)
  /-- Restriction of a larger affine-open component lands in the smaller one. -/
  map_ideal :
    ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
      (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U

/-- Construct ideal-sheaf data from an affine-open family of ideals together
with the restriction-compatibility of an ideal sheaf. -/
def IdealSheafData.of {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U) :
    IdealSheafData X where
  ideal := ideal
  map_ideal := map_ideal

/-- The smart constructor recovers the given affine-open family of ideals. -/
theorem IdealSheafData.of_spec {X : FormalScheme.{u}}
    (ideal : ∀ U : X.affineOpens, Ideal (X.presheaf.obj (op U.1) : Type u))
    (map_ideal :
      ∀ {U V : X.affineOpens} (h : U.1 ≤ V.1),
        (ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ ideal U) :
    (IdealSheafData.of ideal map_ideal).ideal = ideal :=
  sorry

/-- Restriction compatibility of an ideal sheaf on formal affine opens. -/
theorem IdealSheafData.map_ideal_apply {X : FormalScheme.{u}} (I : IdealSheafData X)
    {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    (I.ideal V).map (X.presheaf.map (homOfLE h).op).val ≤ I.ideal U :=
  sorry

/-- Canonical map from a weakly admissible ring into sections of `ofSpf A` over
an open of its formal spectrum. -/
def ofSpfSectionHom (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    (U : Opens (FormalScheme.ofSpf A hA).carrier) :
    (A : Type u) →+* ((FormalScheme.ofSpf A hA).presheaf.obj (op U) : Type u) where
  toFun a :=
    ⟨fun I hI ↦
      algebraMap (A ⧸ I)
        (((structureSheaf (A ⧸ I)).1.obj
            (op (pullbackOpens
              (U : Opens (AlgebraicGeometry.OpenPrime (A : Type u))) I hI))) : Type u)
        (Ideal.Quotient.mk I a),
      sorry⟩
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- Components of `ofSpfSectionHom` are the structure-sheaf algebra maps of
`A ⧸ I`. -/
theorem ofSpfSectionHom_component (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A) (U : Opens (FormalScheme.ofSpf A hA).carrier)
    (a : A) (I : Ideal (A : Type u))
    (hI : _root_.TopologicalRing.Ideal.IsWeakIdealOfDefinition I) :
    (ofSpfSectionHom A hA U a).component I hI =
      algebraMap (A ⧸ I)
        (((structureSheaf (A ⧸ I)).1.obj
            (op (pullbackOpens
              (U : Opens (AlgebraicGeometry.OpenPrime (A : Type u))) I hI))) : Type u)
        (Ideal.Quotient.mk I a) :=
  sorry

/-- The ideal sheaf on `ofSpf A` extending a weak ideal of definition of `A`. -/
def IdealSheafData.ofSpf (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    (I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A) :
    IdealSheafData (FormalScheme.ofSpf A hA) where
  ideal U := I.ideal.map (ofSpfSectionHom A hA U.1)
  map_ideal := sorry

/-- On affine opens of `ofSpf A`, `ofSpf` is the extension of the given weak
ideal along `ofSpfSectionHom`. -/
theorem IdealSheafData.ofSpf_ideal (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A)
    (I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A)
    (U : (FormalScheme.ofSpf A hA).affineOpens) :
    (IdealSheafData.ofSpf A hA I).ideal U = I.ideal.map (ofSpfSectionHom A hA U.1) :=
  sorry

/-- The ideal of sections over an arbitrary open, obtained by comapping the
affine-open components along restriction. -/
def IdealSheafData.idealOn {X : FormalScheme.{u}} (I : IdealSheafData X)
    (U : Opens X.carrier) : Ideal (X.presheaf.obj (op U) : Type u) :=
  ⨅ (V : X.affineOpens), ⨅ (hVU : V.1 ≤ U),
    (I.ideal V).comap (X.presheaf.map (homOfLE hVU).op).val

/-- Membership in `idealOn` is restriction into every affine-open component. -/
theorem IdealSheafData.mem_idealOn {X : FormalScheme.{u}} (I : IdealSheafData X)
    {U : Opens X.carrier} {f : (X.presheaf.obj (op U) : Type u)} :
    f ∈ I.idealOn U ↔
      ∀ (V : X.affineOpens) (h : V.1 ≤ U),
        (X.presheaf.map (homOfLE h).op).val f ∈ I.ideal V :=
  sorry

/-- On a formal affine open, `idealOn` recovers the component ideal. -/
theorem IdealSheafData.idealOn_affine {X : FormalScheme.{u}} (I : IdealSheafData X)
    (U : X.affineOpens) :
    I.idealOn U.1 = I.ideal U :=
  sorry

/-- An ideal sheaf is a weak ideal of definition when its sections on every
formal affine open are a weak ideal of definition. -/
class IsWeakIdealOfDefinition {X : FormalScheme.{u}} (I : IdealSheafData X) : Prop where
  /-- Affine-open sections form a weak ideal of definition. -/
  isWeak :
    ∀ U : X.affineOpens, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal U)

/-- Unfolding of `IsWeakIdealOfDefinition`. -/
theorem isWeakIdealOfDefinition_iff {X : FormalScheme.{u}} (I : IdealSheafData X) :
    IsWeakIdealOfDefinition I ↔
      ∀ U : X.affineOpens, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal U) :=
  sorry

/-- Being a weak ideal of definition may be checked on the members of an affine
open covering. -/
theorem isWeakIdealOfDefinition_iff_affineCover {X : FormalScheme.{u}}
    (I : IdealSheafData X) {ι : Type u} (𝒰 : ι → X.affineOpens)
    (hcover : ⨆ i, (𝒰 i).1 = ⊤) :
    IsWeakIdealOfDefinition I ↔
      ∀ i, TopologicalRing.Ideal.IsWeakIdealOfDefinition (I.ideal (𝒰 i)) :=
  sorry

/-- The ideal sheaf on `ofSpf A` extending a weak ideal of definition of `A` is
a weak ideal of definition. -/
instance instIsWeakIdealOfDefinition_ofSpf (A : TopCommRingCat.{u})
    (hA : IsWeaklyAdmissibleRing A)
    (I : AffineFormalAlgebraicSpace.WeakIdealOfDefinition A) :
    IsWeakIdealOfDefinition (IdealSheafData.ofSpf A hA I) :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
