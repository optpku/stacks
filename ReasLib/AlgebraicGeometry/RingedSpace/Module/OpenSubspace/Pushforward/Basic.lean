/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Category
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.Restriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace.BaseChange.Restriction
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Pushforward from an open subspace

Direct image along the canonical open immersion is a left exact right adjoint.
Its counit inverse is the section restriction for the identity open in the subspace,
transported through the concrete literal-restriction adjunction. Finite colimits
require an additional hypothesis; the unbounded derived functor uses K-injectives.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open TopologicalSpace
open scoped RingedSpace.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- Direct image of `𝒪_U`-modules along the canonical open immersion `U ⟶ X`. -/
@[stacks 08DP "underived open-pushforward owner"]
abbrev modulePushforwardFromOpen (U : Opens X.carrier) :
    openSubspaceModuleCategory X U ⥤ X.Modules :=
  RingedSpace.Hom.pushforward (X.ofRestrict U.isOpenEmbedding)

namespace OpenSubspace.Pushforward

/-- Restriction to an open subspace is left adjoint to direct image from that subspace. -/
@[stacks 08DP "open restriction-pushforward adjunction"]
noncomputable def adjunction (X : RingedSpace.{u}) (U : Opens X.carrier) :
    moduleRestrictionToOpen X U ⊣ modulePushforwardFromOpen U :=
  RingedSpace.Hom.pullbackPushforwardAdjunction (X.ofRestrict U.isOpenEmbedding)

/-- Restriction to an open subspace is a left adjoint. -/
instance isLeftAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsLeftAdjoint (moduleRestrictionToOpen X U) := (adjunction X U).isLeftAdjoint

/-- Direct image from an open subspace is a right adjoint. -/
instance isRightAdjoint (X : RingedSpace.{u}) (U : Opens X.carrier) :
    Functor.IsRightAdjoint (modulePushforwardFromOpen U) := (adjunction X U).isRightAdjoint

/-- The preimage of the image of a subspace open is that same open. -/
theorem sectionIdentity_le (X : RingedSpace.{u}) (U : Opens X.carrier)
    (W : Opens (X.restrict U.isOpenEmbedding).carrier) :
    (Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj W) ≤ W := sorry

/-- Reverse the literal counit by restricting sections along the identity inclusion. -/
def literalCounitInv (X : RingedSpace.{u}) (U : Opens X.carrier)
    (F : openSubspaceModuleCategory X U) :
    F ⟶ (OpenSubspace.BaseChange.literalRestriction X U).obj
      ((modulePushforwardFromOpen U).obj F) where
  val := {
    app := fun W ↦ ModuleCat.homEquiv.symm {
      toFun := fun s ↦ F.val.map (homOfLE (sectionIdentity_le X U W.unop)).op s
      map_add' := (F.val.map (homOfLE (sectionIdentity_le X U W.unop)).op).hom.map_add
      map_smul' := by intros; sorry }
    naturality := by intros; sorry }

/-- The ordinary inverse has specified section maps and the actual adjunction bridge. -/
def counitInv (X : RingedSpace.{u}) (U : Opens X.carrier) :
    𝟭 (openSubspaceModuleCategory X U) ⟶
      modulePushforwardFromOpen U ⋙ moduleRestrictionToOpen X U where
  app F := literalCounitInv X U F ≫
    (OpenSubspace.BaseChange.restrictionBridge X U).hom.app
      ((modulePushforwardFromOpen U).obj F)
  naturality := by intros; sorry

/-- The section restriction reverses the actual ordinary counit. -/
theorem counit_hom_inv_id (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (adjunction X U).counit ≫ counitInv X U = 𝟙 _ := sorry

/-- The actual ordinary counit reverses the section restriction. -/
theorem counit_inv_hom_id (X : RingedSpace.{u}) (U : Opens X.carrier) :
    counitInv X U ≫ (adjunction X U).counit = 𝟙 _ := sorry

/-- The ordinary counit isomorphism stores its restriction inverse explicitly. -/
def counitIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    modulePushforwardFromOpen U ⋙ moduleRestrictionToOpen X U ≅ 𝟭 _ where
  hom := (adjunction X U).counit
  inv := counitInv X U
  hom_inv_id := counit_hom_inv_id X U
  inv_hom_id := counit_inv_hom_id X U

/-- The counit is invertible because its two maps were constructed above. -/
instance counitIsIso (X : RingedSpace.{u}) (U : Opens X.carrier) :
    IsIso (adjunction X U).counit := (counitIso X U).isIso_hom

/-- Every component uses the same constructed counit isomorphism. -/
instance counitAppIsIso (X : RingedSpace.{u}) (U : Opens X.carrier)
    (F : openSubspaceModuleCategory X U) :
    IsIso ((adjunction X U).counit.app F) := (counitIso X U).app F |>.isIso_hom

/-- Direct image from an open subspace is fully faithful. -/
@[stacks 08DP "open pushforward is fully faithful"]
noncomputable def fullyFaithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).FullyFaithful :=
  (adjunction X U).fullyFaithfulROfIsIsoCounit

/-- Direct image from an open subspace is full. -/
noncomputable instance full (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Full :=
  (fullyFaithful X U).full

/-- Direct image from an open subspace is faithful. -/
noncomputable instance faithful (X : RingedSpace.{u}) (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Faithful :=
  (fullyFaithful X U).faithful

end OpenSubspace.Pushforward

/-- Direct image from an open subspace is additive. -/
instance OpenSubspace.Pushforward.additive (U : Opens X.carrier) :
    (modulePushforwardFromOpen U).Additive := sorry

/-- Direct image is exact if it also preserves finite colimits. -/
theorem OpenSubspace.Pushforward.isExact (U : Opens X.carrier)
    [PreservesFiniteColimits (modulePushforwardFromOpen U)] :
    exactFunctor (openSubspaceModuleCategory X U) X.Modules
      (modulePushforwardFromOpen U) := sorry

/-- Direct image from an open subspace preserves finite limits. -/
instance OpenSubspace.Pushforward.preservesFiniteLimits (U : Opens X.carrier) :
    PreservesFiniteLimits (modulePushforwardFromOpen U) := sorry

/-- An explicit exactness certificate implies finite-colimit preservation. -/
theorem OpenSubspace.Pushforward.preservesFiniteColimits (U : Opens X.carrier)
    (h : exactFunctor (openSubspaceModuleCategory X U) X.Modules
      (modulePushforwardFromOpen U)) :
    PreservesFiniteColimits (modulePushforwardFromOpen U) := h.2

end AlgebraicGeometry.RingedSpace
