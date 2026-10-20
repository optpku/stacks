/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RationalBridge

/-- A rational-bridge contraction is a pushout compatible with the component and complement
maps that preserves curve invariants and has vanishing first higher direct image. -/
structure IsContraction
    {k : Type u} [Field k] {X : SchemeOverField k}
    (B : RationalBridge X) (Y : SchemeOverField k) (c : X ⟶ Y)
    (a : (complementScheme X B.component).left ⟶ Y.left)
    (b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left)
    (componentMap : (componentScheme X B.component).left ⟶ Y.left)
    (componentToSpec : (componentScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
    (intersectionToSpec : (intersectionScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)) : Prop where
  /-- The spectrum of component global sections and the complement form the contraction pushout. -/
  isPushout : IsPushout
    intersectionToSpec (intersectionToComplement X B.component) b a
  /-- The map from the complementary closure to the pushout is affine. -/
  complement_affine : IsAffineHom a
  /-- The contraction map restricts to the displayed map on the component. -/
  contraction_eq :
    X.left.irreducibleComponentSubschemeι B.component ≫ c.left = componentMap
  /-- The contraction map restricts to the displayed map on the complementary closure. -/
  complement_restriction :
    schemeTheoreticClosureι (complement X B.component) ≫ c.left = a
  /-- The component-to-spectrum map is the canonical global-sections map. -/
  componentToSpec_eq_toSpecΓ :
    componentToSpec = (componentScheme X B.component).left.toSpecΓ
  /-- The component map factors through the spectrum of its global section ring. -/
  component_globalSections_factor : componentToSpec ≫ b = componentMap
  /-- The intersection map to the section spectrum is induced from the component map. -/
  intersection_globalSections_factor :
    intersectionToSpec = intersectionToComponent X B.component ≫ componentToSpec
  /-- The spectrum map is a morphism over the ground field. -/
  sectionSpec_over :
    b ≫ Y.hom = Scheme.Hom.globalSectionsSpecMap (componentScheme X B.component).hom
  /-- The target is proper over the ground field. -/
  target_proper : IsProper Y.hom
  /-- The target has dimension one. -/
  target_dimension : topologicalKrullDim Y.left = 1
  /-- The target has constant global functions. -/
  target_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom)
  /-- The target has at-worst-nodal singularities. -/
  target_atWorstNodal : SchemeOverField.atWorstNodal Y
  /-- The structure-sheaf map identifies `𝒪_Y` with `c_*𝒪_X`. -/
  structureSheaf_iso : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom)
  /-- The first higher direct image of the structure sheaf vanishes. -/
  higherDirectImage_one_isZero : IsZero
    (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf) 1)
  /-- The contraction preserves the cohomological genus. -/
  genus_eq : Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 =
    Scheme.Hom.cohomologyFinrank Y.hom
      (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1

/-- The contraction pushout square commutes on the scheme-theoretic intersection. -/
theorem IsContraction.commutes
    {k : Type u} [Field k] {X : SchemeOverField k}
    {B : RationalBridge X} {Y : SchemeOverField k} {c : X ⟶ Y}
    {a : (complementScheme X B.component).left ⟶ Y.left}
    {b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left}
    {componentMap : (componentScheme X B.component).left ⟶ Y.left}
    {componentToSpec : (componentScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)}
    {intersectionToSpec : (intersectionScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)}
    (h : B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec) :
    intersectionToSpec ≫ b = intersectionToComplement X B.component ≫ a := sorry

/-- Construct a contraction predicate from its pushout, affine complement map, and
compatibility and target conditions. -/
def IsContraction.of
    {k : Type u} [Field k] {X : SchemeOverField k}
    (B : RationalBridge X) (Y : SchemeOverField k) (c : X ⟶ Y)
    (a : (complementScheme X B.component).left ⟶ Y.left)
    (b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left)
    (componentMap : (componentScheme X B.component).left ⟶ Y.left)
    (componentToSpec : (componentScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
    (intersectionToSpec : (intersectionScheme X B.component).left ⟶
      Spec (Scheme.globalSectionsRing (componentScheme X B.component).left))
    (isPushout : IsPushout
      intersectionToSpec (intersectionToComplement X B.component) b a)
    (complement_affine : IsAffineHom a)
    (contraction_eq :
      X.left.irreducibleComponentSubschemeι B.component ≫ c.left = componentMap)
    (complement_restriction :
      schemeTheoreticClosureι (complement X B.component) ≫ c.left = a)
    (componentToSpec_eq_toSpecΓ :
      componentToSpec = (componentScheme X B.component).left.toSpecΓ)
    (component_globalSections_factor : componentToSpec ≫ b = componentMap)
    (intersection_globalSections_factor :
      intersectionToSpec = intersectionToComponent X B.component ≫ componentToSpec)
    (sectionSpec_over :
      b ≫ Y.hom = Scheme.Hom.globalSectionsSpecMap (componentScheme X B.component).hom)
    (target_proper : IsProper Y.hom)
    (target_dimension : topologicalKrullDim Y.left = 1)
    (target_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom))
    (target_atWorstNodal : SchemeOverField.atWorstNodal Y)
    (structureSheaf_iso : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom))
    (higherDirectImage_one_isZero : IsZero
      (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
        (SheafOfModules.unit X.left.ringCatSheaf) 1))
    (genus_eq : Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 =
      Scheme.Hom.cohomologyFinrank Y.hom
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1) :
    B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec :=
  { isPushout := isPushout
    complement_affine := complement_affine
    contraction_eq := contraction_eq
    complement_restriction := complement_restriction
    componentToSpec_eq_toSpecΓ := componentToSpec_eq_toSpecΓ
    component_globalSections_factor := component_globalSections_factor
    intersection_globalSections_factor := intersection_globalSections_factor
    sectionSpec_over := sectionSpec_over
    target_proper := target_proper
    target_dimension := target_dimension
    target_globalSections := target_globalSections
    target_atWorstNodal := target_atWorstNodal
    structureSheaf_iso := structureSheaf_iso
    higherDirectImage_one_isZero := higherDirectImage_one_isZero
    genus_eq := genus_eq }

/-- Every rational bridge on a proper one-dimensional nodal scheme with constant global
functions admits a contraction preserving the curve invariants. -/
theorem existsContraction
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : SchemeOverField.atWorstNodal X)
    (B : RationalBridge X) :
    ∃ (Y : SchemeOverField k) (c : X ⟶ Y)
      (a : (RationalBridge.complementScheme X B.component).left ⟶ Y.left)
      (b : Spec (Scheme.globalSectionsRing
        (RationalBridge.componentScheme X B.component).left) ⟶ Y.left)
      (componentMap : (RationalBridge.componentScheme X B.component).left ⟶ Y.left)
      (componentToSpec : (RationalBridge.componentScheme X B.component).left ⟶
        Spec (Scheme.globalSectionsRing
          (RationalBridge.componentScheme X B.component).left))
      (intersectionToSpec : (RationalBridge.intersectionScheme X B.component).left ⟶
        Spec (Scheme.globalSectionsRing
          (RationalBridge.componentScheme X B.component).left)),
      B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec := sorry


section Specifications

variable {k : Type u} [Field k] {X : SchemeOverField k}
  {B : RationalBridge X} {Y : SchemeOverField k} {c : X ⟶ Y}
  {a : (complementScheme X B.component).left ⟶ Y.left}
  {b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left}
  {componentMap : (componentScheme X B.component).left ⟶ Y.left}
  {componentToSpec : (componentScheme X B.component).left ⟶
    Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)}
  {intersectionToSpec : (intersectionScheme X B.component).left ⟶
    Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)}

/-- A contraction has an affine complementary pushout and the specified restrictions,
canonical spectrum maps, target invariants, and structure-sheaf direct-image properties. -/
theorem IsContraction.spec
    (h : B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec) :
    (IsPushout intersectionToSpec (intersectionToComplement X B.component) b a ∧
      IsAffineHom a) ∧
    ((X.left.irreducibleComponentSubschemeι B.component ≫ c.left = componentMap ∧
      schemeTheoreticClosureι (complement X B.component) ≫ c.left = a) ∧
    ((componentToSpec = (componentScheme X B.component).left.toSpecΓ ∧
      componentToSpec ≫ b = componentMap) ∧
    ((intersectionToSpec = intersectionToComponent X B.component ≫ componentToSpec ∧
      b ≫ Y.hom = Scheme.Hom.globalSectionsSpecMap (componentScheme X B.component).hom) ∧
    ((IsProper Y.hom ∧ topologicalKrullDim Y.left = 1) ∧
    ((Function.Bijective (Scheme.Hom.globalSectionsMap Y.hom) ∧ SchemeOverField.atWorstNodal Y) ∧
    ((IsIso (RingedSpace.Hom.commRingSheafPushforwardMap c.left.toShHom) ∧
      IsZero (RingedSpace.Hom.higherDirectImageModule c.left.toShHom
        (SheafOfModules.unit X.left.ringCatSheaf) 1)) ∧
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 =
      Scheme.Hom.cohomologyFinrank Y.hom
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1)))))) := sorry

end Specifications

section LocalRings

variable {k : Type u} [Field k] {X : SchemeOverField k} [h_proper : IsProper X.hom]
  (h_dimension : topologicalKrullDim X.left = 1)
  (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
  (h_nodal : SchemeOverField.atWorstNodal X)
  {B : RationalBridge X} {Y : SchemeOverField k} {c : X ⟶ Y}
  {a : (complementScheme X B.component).left ⟶ Y.left}
  {b : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left) ⟶ Y.left}
  {componentMap : (componentScheme X B.component).left ⟶ Y.left}
  {componentToSpec : (componentScheme X B.component).left ⟶
    Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)}
  {intersectionToSpec : (intersectionScheme X B.component).left ⟶
    Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)}

include h_proper h_dimension hΓ h_nodal

/-- The image of the component section spectrum under a rational-bridge contraction is a node. -/
theorem IsContraction.image_isNode
    (h : B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec)
    (point : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)) :
    SchemeOverField.isNode Y (b point) := sorry

/-- With two attachment points, the completed local ring at the contracted image is the
quotient of the two-variable power series ring over the component section field by the product
of its variables. -/
theorem IsContraction.completedLocalRing_split
    (h : B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec)
    (h_split : Nat.card (intersectionScheme X B.component).left = 2)
    (point : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (b point)))
      (Y.left.presheaf.stalk (b point)) ≃+*
      (MvPowerSeries (Fin 2) (Scheme.globalSectionsRing (componentScheme X B.component).left) ⧸
        Ideal.span {MvPowerSeries.X (R := Scheme.globalSectionsRing
          (componentScheme X B.component).left) (0 : Fin 2) *
          MvPowerSeries.X (1 : Fin 2)})) := sorry

/-- With one attachment point, the completed local ring at the contracted image consists of
power series over the attachment section field whose constant coefficients belong to the
image of the component section field. -/
theorem IsContraction.completedLocalRing_nonsplit
    (h : B.IsContraction Y c a b componentMap componentToSpec intersectionToSpec)
    (h_nonsplit : Nat.card (intersectionScheme X B.component).left = 1)
    (point : Spec (Scheme.globalSectionsRing (componentScheme X B.component).left)) :
    Nonempty (AdicCompletion (IsLocalRing.maximalIdeal (Y.left.presheaf.stalk (b point)))
      (Y.left.presheaf.stalk (b point)) ≃+*
      ((intersectionToComponent X B.component).appTop.hom.range.comap
        (PowerSeries.constantCoeff (R := Scheme.globalSectionsRing
          (intersectionScheme X B.component).left)))) := sorry

end LocalRings

end AlgebraicGeometry.RationalBridge
