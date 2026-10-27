/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Topology.Sheaf.Subset.Closed
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Adjunction
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Pointed.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# The pointed closed-support adjunction

The canonical adjunction and its inverse maps are owned by
`TopCat.Sheaf.ClosedSubset.SectionsWithSupport` in `ClosedSubset.Adjunction`.
The names below are thin specializations at `C := Pointed`; in particular the pointed functor
is definitionally the generic closed-support functor. Isomorphism instances come from that generic construction; the right-adjoint instance bridges
the pointed functor definition to its generic specialization. Only pointed exactness is specific
to this module.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

variable {X : TopCat.{u}} {Z : Set X}

/-- Pointed specialization of `SectionsWithSupport.subsheafPushforwardEqTop`. -/
abbrev subsheafPushforwardEqTop
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.subsheafPushforwardEqTop hZ F

/-- Pointed specialization of `SectionsWithSupport.objectMemEssImage`. -/
abbrev objectMemEssImage
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectMemEssImage hZ F

/-- Pointed specialization of `SectionsWithSupport.objectUnitIsIso`. -/
abbrev objectUnitIsIso
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectUnitIsIso hZ F

/-- Pointed specialization of `SectionsWithSupport.counitAppIsIso`. -/
abbrev counitAppIsIso
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.counitAppIsIso Z F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforwardInv`. -/
abbrev inclusionPushforwardInv
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforwardInv hZ F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforward_hom_inv_id`. -/
abbrev inclusionPushforward_hom_inv_id
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforward_hom_inv_id hZ F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforward_inv_hom_id`. -/
abbrev inclusionPushforward_inv_hom_id
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforward_inv_hom_id hZ F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforwardIsIso`. -/
abbrev inclusionPushforwardIsIso
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforwardIsIso hZ F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforwardIso`. -/
abbrev inclusionPushforwardIso
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforwardIso hZ F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforwardIso_hom`. -/
abbrev inclusionPushforwardIso_hom
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforwardIso_hom hZ F

/-- Pointed specialization of `SectionsWithSupport.inclusionPushforwardIso_inv`. -/
abbrev inclusionPushforwardIso_inv
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.inclusionPushforwardIso_inv hZ F

/-- Pointed specialization of `SectionsWithSupport.pullbackPushforwardCounitAppInv`. -/
abbrev pullbackPushforwardCounitAppInv
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.pullbackPushforwardCounitAppInv Z F

/-- Pointed specialization of `SectionsWithSupport.pullbackPushforwardCounitApp_hom_inv_id`. -/
abbrev pullbackPushforwardCounitApp_hom_inv_id
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.pullbackPushforwardCounitApp_hom_inv_id Z F

/-- Pointed specialization of `SectionsWithSupport.pullbackPushforwardCounitApp_inv_hom_id`. -/
abbrev pullbackPushforwardCounitApp_inv_hom_id
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.pullbackPushforwardCounitApp_inv_hom_id Z F

/-- Pointed specialization of `SectionsWithSupport.pullbackPushforwardCounitAppIso`. -/
abbrev pullbackPushforwardCounitAppIso
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.pullbackPushforwardCounitAppIso Z F

/-- Pointed specialization of `SectionsWithSupport.pullbackPushforwardCounitAppIso_hom`. -/
abbrev pullbackPushforwardCounitAppIso_hom
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.pullbackPushforwardCounitAppIso_hom Z F

/-- Pointed specialization of `SectionsWithSupport.pullbackPushforwardCounitAppIso_inv`. -/
abbrev pullbackPushforwardCounitAppIso_inv
    (Z : Set X) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.pullbackPushforwardCounitAppIso_inv Z F

/-- Pointed specialization of `SectionsWithSupport.objectPullbackPushforwardUnitAppInv`. -/
abbrev objectPullbackPushforwardUnitAppInv
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectPullbackPushforwardUnitAppInv hZ F

/-- Pointed specialization of `SectionsWithSupport.objectPullbackPushforwardUnitApp_hom_inv_id`. -/
abbrev objectPullbackPushforwardUnitApp_hom_inv_id
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectPullbackPushforwardUnitApp_hom_inv_id hZ F

/-- Pointed specialization of `SectionsWithSupport.objectPullbackPushforwardUnitApp_inv_hom_id`. -/
abbrev objectPullbackPushforwardUnitApp_inv_hom_id
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectPullbackPushforwardUnitApp_inv_hom_id hZ F

/-- Pointed specialization of `SectionsWithSupport.objectPullbackPushforwardUnitAppIso`. -/
abbrev objectPullbackPushforwardUnitAppIso
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectPullbackPushforwardUnitAppIso hZ F

/-- Pointed specialization of `SectionsWithSupport.objectPullbackPushforwardUnitAppIso_hom`. -/
abbrev objectPullbackPushforwardUnitAppIso_hom
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectPullbackPushforwardUnitAppIso_hom hZ F

/-- Pointed specialization of `SectionsWithSupport.objectPullbackPushforwardUnitAppIso_inv`. -/
abbrev objectPullbackPushforwardUnitAppIso_inv
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.objectPullbackPushforwardUnitAppIso_inv hZ F

/-- Pointed specialization of `SectionsWithSupport.unitApp`. -/
abbrev unitApp
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.unitApp hZ F

/-- Pointed specialization of `SectionsWithSupport.counitApp`. -/
abbrev counitApp
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.counitApp hZ F

/-- Remark 17.6.4 (01B0): the generic closed-support adjunction at pointed coefficients.
This bridge is definitionally the canonical adjunction, including its unit and counit data. -/
@[stacks 01B0 "pointed closed-support adjunction"]
abbrev adjunction (hZ : IsClosed Z) :
    Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z) ⊣ functor hZ :=
  SectionsWithSupport.adjunction (C := Pointed.{u}) hZ

/-- Pointed specialization of `SectionsWithSupport.adjunction_unit_app`. -/
abbrev adjunction_unit_app
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :=
  SectionsWithSupport.adjunction_unit_app hZ F

/-- Pointed specialization of `SectionsWithSupport.adjunction_counit_app`. -/
abbrev adjunction_counit_app
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :=
  SectionsWithSupport.adjunction_counit_app hZ F

/-- Closed-subset pushforward of pointed sheaves is a left adjoint. -/
@[stacks 01B0 "pointed closed-subset pushforward is a left adjoint"]
theorem pushforwardIsLeftAdjoint (hZ : IsClosed Z) :
    (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).IsLeftAdjoint :=
  SectionsWithSupport.pushforwardIsLeftAdjointOfIsClosed (C := Pointed.{u}) hZ

/-- The canonical right-adjoint instance, exposed for the pointed functor definition. -/
@[stacks 01B0 "pointed sections with support are a right adjoint"]
noncomputable instance functorIsRightAdjoint (hZ : IsClosed Z) :
    (functor hZ).IsRightAdjoint :=
  SectionsWithSupport.functorIsRightAdjoint (C := Pointed.{u}) hZ

/-- Remark 17.6.4 (01B0): pushforward of pointed sheaves along a closed-subset inclusion is
exact. -/
@[stacks 01B0 "closed-subset pushforward of pointed sheaves is exact"]
theorem pushforwardExact (hZ : IsClosed Z) :
    exactFunctor ((TopCat.of Z).Sheaf Pointed.{u}) (X.Sheaf Pointed.{u})
      (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)) := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

end
