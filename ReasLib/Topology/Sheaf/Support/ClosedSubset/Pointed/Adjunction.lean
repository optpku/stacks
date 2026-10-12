/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.Topology.Sheaf.Subset.Closed
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Pointed.Functor
import Mathlib.Tactic.CrossRefAttribute

/-!
# The pointed closed-support adjunction

For a closed subset `Z`, pushforward of pointed sheaves from `Z` is left adjoint to pointed
sections with support in `Z`. Unit and counit components are explicit data; only coherence laws
are deferred to the proof layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

variable {X : TopCat.{u}} {Z : Set X}

/-- The support subobject of a pointed sheaf pushed forward from `Z` is the top subobject. -/
@[stacks 01B0 "pointed support subobject of a pushforward is top"]
theorem subsheafPushforwardEqTop
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    subsheaf hZ ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) =
      ⊤ := sorry

/-- The ambient support inclusion is invertible on pointed sheaves pushed forward from `Z`. -/
@[stacks 01B0 "pointed support inclusion on a pushforward is invertible"]
noncomputable instance inclusionPushforwardIsIso
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    IsIso
      (inclusion hZ
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F)) := sorry

/-- The ambient pointed support object belongs to the essential image of closed-subset
pushforward. -/
@[stacks 01B0 "pointed support object lies in the pushforward essential image"]
theorem objectMemEssImage (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).essImage
      (object hZ F) := sorry

/-- The pullback-pushforward unit is canonically invertible on the ambient support object. -/
@[stacks 01B0 "pointed support unit is invertible"]
noncomputable instance objectUnitIsIso
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed.{u}
        (TopCat.subsetInclusion Z)).unit.app (object hZ F)) := sorry

/-- The pullback-pushforward counit is invertible on every pointed sheaf over a subset. -/
@[stacks 01B0 "pointed pullback-pushforward counit isomorphism instance"]
noncomputable instance counitAppIsIso (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction Pointed.{u}
        (TopCat.subsetInclusion Z)).counit.app F) := sorry

/-- The explicit inverse of the closed-support inclusion on a pointed direct image. -/
@[stacks 01B0 "inverse pointed closed-support inclusion on a direct image"]
noncomputable def inclusionPushforwardInv
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F ⟶
      object hZ
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) :=
  inv
    (inclusion hZ
      ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F))

/-- The pointed closed-support inclusion and its inverse compose to the identity. -/
@[simp, stacks 01B0 "pointed closed-support inclusion forward-inverse law"]
theorem inclusionPushforward_hom_inv_id
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    inclusion hZ
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) ≫
      inclusionPushforwardInv hZ F = 𝟙 _ := sorry

/-- The inverse of the pointed closed-support inclusion followed by the inclusion is identity. -/
@[simp, stacks 01B0 "pointed closed-support inclusion inverse-forward law"]
theorem inclusionPushforward_inv_hom_id
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    inclusionPushforwardInv hZ F ≫
        inclusion hZ
          ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) =
      𝟙 _ := sorry

/-- The pointed closed-support inclusion on a direct image is a literal isomorphism. -/
@[stacks 01B0 "pointed closed-support inclusion isomorphism"]
noncomputable def inclusionPushforwardIso
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    object hZ
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) ≅
      (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F where
  hom := inclusion hZ
    ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F)
  inv := inclusionPushforwardInv hZ F
  hom_inv_id := inclusionPushforward_hom_inv_id hZ F
  inv_hom_id := inclusionPushforward_inv_hom_id hZ F

/-- The forward map of the pointed closed-support inclusion isomorphism. -/
@[simp, stacks 01B0 "pointed closed-support inclusion isomorphism hom"]
theorem inclusionPushforwardIso_hom
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (inclusionPushforwardIso hZ F).hom =
      inclusion hZ
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) := sorry

/-- The inverse map of the pointed closed-support inclusion isomorphism. -/
@[simp, stacks 01B0 "pointed closed-support inclusion isomorphism inverse"]
theorem inclusionPushforwardIso_inv
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (inclusionPushforwardIso hZ F).inv = inclusionPushforwardInv hZ F := sorry

/-- The explicit inverse of the pullback-pushforward counit for pointed sheaves. -/
@[stacks 01B0 "inverse pointed pullback-pushforward counit"]
noncomputable def pullbackPushforwardCounitAppInv (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    F ⟶
      (Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) :=
  @CategoryTheory.inv _ _ _ _
    ((Sheaf.pullbackPushforwardAdjunction Pointed.{u}
      (TopCat.subsetInclusion Z)).counit.app F)
    (counitAppIsIso Z F)

/-- The pointed pullback-pushforward counit followed by its inverse is identity. -/
@[simp, stacks 01B0 "pointed counit forward-inverse law"]
theorem pullbackPushforwardCounitApp_hom_inv_id (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
      (TopCat.subsetInclusion Z)).counit.app F ≫
        pullbackPushforwardCounitAppInv Z F = 𝟙 _ := sorry

/-- The inverse of the pointed pullback-pushforward counit followed by the counit is identity. -/
@[simp, stacks 01B0 "pointed counit inverse-forward law"]
theorem pullbackPushforwardCounitApp_inv_hom_id (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    pullbackPushforwardCounitAppInv Z F ≫
        (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
          (TopCat.subsetInclusion Z)).counit.app F = 𝟙 _ := sorry

/-- The pointed pullback-pushforward counit is a literal isomorphism. -/
@[stacks 01B0 "pointed pullback-pushforward counit isomorphism"]
noncomputable def pullbackPushforwardCounitAppIso (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) ≅ F where
  hom := (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
    (TopCat.subsetInclusion Z)).counit.app F
  inv := pullbackPushforwardCounitAppInv Z F
  hom_inv_id := pullbackPushforwardCounitApp_hom_inv_id Z F
  inv_hom_id := pullbackPushforwardCounitApp_inv_hom_id Z F

/-- The forward map of the pointed pullback-pushforward counit isomorphism. -/
@[simp, stacks 01B0 "pointed counit isomorphism hom"]
theorem pullbackPushforwardCounitAppIso_hom (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (pullbackPushforwardCounitAppIso Z F).hom =
      (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
        (TopCat.subsetInclusion Z)).counit.app F := sorry

/-- The inverse map of the pointed pullback-pushforward counit isomorphism. -/
@[simp, stacks 01B0 "pointed counit isomorphism inverse"]
theorem pullbackPushforwardCounitAppIso_inv (Z : Set X)
    (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (pullbackPushforwardCounitAppIso Z F).inv =
      pullbackPushforwardCounitAppInv Z F := sorry

/-- The explicit inverse of the pullback-pushforward unit on a pointed support object. -/
@[stacks 01B0 "inverse pointed ambient pullback-pushforward unit"]
noncomputable def objectPullbackPushforwardUnitAppInv
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).obj
          (object hZ F)) ⟶ object hZ F :=
  @CategoryTheory.inv _ _ _ _
    ((Sheaf.pullbackPushforwardAdjunction Pointed.{u}
      (TopCat.subsetInclusion Z)).unit.app (object hZ F))
    (objectUnitIsIso hZ F)

/-- The pointed pullback-pushforward unit followed by its inverse is identity. -/
@[simp, stacks 01B0 "pointed ambient unit forward-inverse law"]
theorem objectPullbackPushforwardUnitApp_hom_inv_id
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
      (TopCat.subsetInclusion Z)).unit.app (object hZ F) ≫
        objectPullbackPushforwardUnitAppInv hZ F = 𝟙 _ := sorry

/-- The inverse of the pointed pullback-pushforward unit followed by the unit is identity. -/
@[simp, stacks 01B0 "pointed ambient unit inverse-forward law"]
theorem objectPullbackPushforwardUnitApp_inv_hom_id
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    objectPullbackPushforwardUnitAppInv hZ F ≫
        (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
          (TopCat.subsetInclusion Z)).unit.app (object hZ F) = 𝟙 _ := sorry

/-- The pointed pullback-pushforward unit on a support object is a literal isomorphism. -/
@[stacks 01B0 "pointed ambient pullback-pushforward unit isomorphism"]
noncomputable def objectPullbackPushforwardUnitAppIso
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    object hZ F ≅
      (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).obj
          (object hZ F)) where
  hom := (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
    (TopCat.subsetInclusion Z)).unit.app (object hZ F)
  inv := objectPullbackPushforwardUnitAppInv hZ F
  hom_inv_id := objectPullbackPushforwardUnitApp_hom_inv_id hZ F
  inv_hom_id := objectPullbackPushforwardUnitApp_inv_hom_id hZ F

/-- The forward map of the pointed ambient unit isomorphism. -/
@[simp, stacks 01B0 "pointed ambient unit isomorphism hom"]
theorem objectPullbackPushforwardUnitAppIso_hom
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (objectPullbackPushforwardUnitAppIso hZ F).hom =
      (Sheaf.pullbackPushforwardAdjunction Pointed.{u}
        (TopCat.subsetInclusion Z)).unit.app (object hZ F) := sorry

/-- The inverse map of the pointed ambient unit isomorphism. -/
@[simp, stacks 01B0 "pointed ambient unit isomorphism inverse"]
theorem objectPullbackPushforwardUnitAppIso_inv
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (objectPullbackPushforwardUnitAppIso hZ F).inv =
      objectPullbackPushforwardUnitAppInv hZ F := sorry

/-- The unit component for the pointed pushforward/sections-with-support adjunction. -/
@[stacks 01B0 "pointed closed-support adjunction unit component"]
noncomputable def unitApp
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    F ⟶
      (functor hZ).obj
        ((Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj F) :=
  pullbackPushforwardCounitAppInv Z F ≫
    (Sheaf.pullback Pointed.{u} (TopCat.subsetInclusion Z)).map
      (inclusionPushforwardInv hZ F)

/-- The counit component for the pointed pushforward/sections-with-support adjunction. -/
@[stacks 01B0 "pointed closed-support adjunction counit component"]
noncomputable def counitApp
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).obj
        ((functor hZ).obj F) ⟶ F :=
  objectPullbackPushforwardUnitAppInv hZ F ≫
    inclusion hZ F

/-- Remark 17.6.4 (01B0): closed-subset pushforward of pointed sheaves is left adjoint to
pointed sections with support. -/
@[stacks 01B0 "pointed closed-support adjunction"]
noncomputable def adjunction (hZ : IsClosed Z) :
    Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z) ⊣ functor hZ where
  unit :=
    { app := unitApp hZ
      naturality := sorry }
  counit :=
    { app := counitApp hZ
      naturality := sorry }
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The unit of the pointed closed-support adjunction is the explicit unit component. -/
@[simp, stacks 01B0 "pointed closed-support adjunction unit app"]
theorem adjunction_unit_app
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf Pointed.{u}) :
    (adjunction hZ).unit.app F = unitApp hZ F := sorry

/-- The counit of the pointed closed-support adjunction is the explicit counit component. -/
@[simp, stacks 01B0 "pointed closed-support adjunction counit app"]
theorem adjunction_counit_app
    (hZ : IsClosed Z) (F : X.Sheaf Pointed.{u}) :
    (adjunction hZ).counit.app F = counitApp hZ F := sorry

/-- Closed-subset pushforward of pointed sheaves is a left adjoint. -/
@[stacks 01B0 "pointed closed-subset pushforward is a left adjoint"]
theorem pushforwardIsLeftAdjoint (hZ : IsClosed Z) :
    (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)).IsLeftAdjoint := sorry

/-- Pointed sections with support form a right adjoint. -/
@[stacks 01B0 "pointed sections with support are a right adjoint"]
noncomputable instance functorIsRightAdjoint (hZ : IsClosed Z) :
    (functor hZ).IsRightAdjoint := sorry

/-- Remark 17.6.4 (01B0): pushforward of pointed sheaves along a closed-subset inclusion is
exact. -/
@[stacks 01B0 "closed-subset pushforward of pointed sheaves is exact"]
theorem pushforwardExact (hZ : IsClosed Z) :
    exactFunctor ((TopCat.of Z).Sheaf Pointed.{u}) (X.Sheaf Pointed.{u})
      (Sheaf.pushforward Pointed.{u} (TopCat.subsetInclusion Z)) := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport.Pointed

end
