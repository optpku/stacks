module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Supported
public import ReasLib.Topology.Sheaf.Support.ClosedSubset.Functor

/-!
# The closed-support adjunction

Pushforward from a closed subspace is left adjoint to the additive sheaf of sections supported on
that subspace. The unit and counit components are explicit; naturality and triangle identities
are kept as the proof layer.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace

noncomputable section

universe u

namespace TopCat.Sheaf.ClosedSubset.SectionsWithSupport

variable {X : TopCat.{u}} {Z : Set X}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]

/-- The closed-support subobject of a sheaf pushed forward from `Z` is the whole sheaf. -/
theorem subsheafPushforwardEqTop
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    subsheaf hZ
      ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) = ⊤ := sorry

/-- The ambient closed-support sheaf belongs to the essential image of pushforward from `Z`. -/
theorem objectMemEssImage
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).essImage
      (object hZ F) :=
  ⟨supportedRestriction hZ F, ⟨(supportedRestrictionPushforwardIso hZ F).symm⟩⟩

/-- The pullback-pushforward unit is invertible on the ambient closed-support object. -/
@[stacks 01AZ "ambient closed-support unit invertibility"]
theorem objectUnitIsIso
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.subsetInclusion Z)).unit.app (object hZ F)) :=
  ⟨⟨supportedUnitInv hZ F, unit_supportedUnitInv hZ F,
    supportedUnitInv_unit hZ F⟩⟩

attribute [instance] objectUnitIsIso

/-- The pullback-pushforward counit is invertible on every sheaf over a subset. -/
@[stacks 01AZ "closed-subspace counit invertibility"]
noncomputable instance counitAppIsIso (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    IsIso
      ((Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.subsetInclusion Z)).counit.app F) :=
  ⟨⟨Subset.counitInv Z F, Subset.counit_app_counitInv Z F,
    Subset.counitInv_counit_app Z F⟩⟩

/-- The explicit inverse of the closed-support inclusion on a direct image. -/
@[stacks 01AZ "inverse closed-support inclusion on a direct image"]
noncomputable def inclusionPushforwardInv
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F ⟶
      object hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) :=
  liftToObject hZ (𝟙 _) (by
    simpa only [Category.id_comp] using restrictionPushforward_eq_zero hZ F)

/-- The closed-support inclusion and its explicit inverse compose to the identity on the kernel
object. -/
@[simp, stacks 01AZ "closed-support inclusion forward-inverse law"]
theorem inclusionPushforward_hom_inv_id
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    inclusion hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) ≫
      inclusionPushforwardInv hZ F = 𝟙 _ := sorry

/-- The explicit inverse of the closed-support inclusion followed by the inclusion is the
identity on a direct image. -/
@[simp, stacks 01AZ "closed-support inclusion inverse-forward law"]
theorem inclusionPushforward_inv_hom_id
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    inclusionPushforwardInv hZ F ≫
        inclusion hZ
          ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) =
      𝟙 _ := sorry

/-- The ambient support inclusion is invertible on a sheaf pushed forward from `Z`. -/
@[stacks 01AZ "closed-support inclusion invertibility"]
noncomputable instance inclusionPushforwardIsIso
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    IsIso
      (inclusion hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F)) :=
  ⟨⟨inclusionPushforwardInv hZ F,
    inclusionPushforward_hom_inv_id hZ F, inclusionPushforward_inv_hom_id hZ F⟩⟩

/-- The closed-support inclusion on a direct image is a literal isomorphism. -/
@[stacks 01AZ "closed-support inclusion isomorphism on a direct image"]
noncomputable def inclusionPushforwardIso
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    object hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) ≅
      (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F where
  hom := inclusion hZ
    ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F)
  inv := inclusionPushforwardInv hZ F
  hom_inv_id := inclusionPushforward_hom_inv_id hZ F
  inv_hom_id := inclusionPushforward_inv_hom_id hZ F

/-- The forward map of `inclusionPushforwardIso` is the closed-support inclusion. -/
@[simp, stacks 01AZ "closed-support inclusion isomorphism hom"]
theorem inclusionPushforwardIso_hom
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (inclusionPushforwardIso hZ F).hom =
      inclusion hZ
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) := sorry

/-- The inverse map of `inclusionPushforwardIso` is the explicit closed-support inverse. -/
@[simp, stacks 01AZ "closed-support inclusion isomorphism inverse"]
theorem inclusionPushforwardIso_inv
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (inclusionPushforwardIso hZ F).inv = inclusionPushforwardInv hZ F := sorry

/-- The explicit inverse of the pullback-pushforward counit on a sheaf over the closed subspace. -/
@[stacks 01AZ "inverse closed-subspace pullback-pushforward counit"]
noncomputable def pullbackPushforwardCounitAppInv (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    F ⟶
      (Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) :=
  Subset.counitInv Z F

/-- The pullback-pushforward counit followed by its explicit inverse is the identity. -/
@[simp, stacks 01AZ "closed-subspace counit forward-inverse law"]
theorem pullbackPushforwardCounitApp_hom_inv_id (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.subsetInclusion Z)).counit.app F ≫
        pullbackPushforwardCounitAppInv Z F = 𝟙 _ := sorry

/-- The explicit inverse of the pullback-pushforward counit followed by the counit is the
identity. -/
@[simp, stacks 01AZ "closed-subspace counit inverse-forward law"]
theorem pullbackPushforwardCounitApp_inv_hom_id (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    pullbackPushforwardCounitAppInv Z F ≫
        (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.subsetInclusion Z)).counit.app F = 𝟙 _ := sorry

/-- The pullback-pushforward counit on a sheaf over the closed subspace is a literal isomorphism.
-/
@[stacks 01AZ "closed-subspace pullback-pushforward counit isomorphism"]
noncomputable def pullbackPushforwardCounitAppIso (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) ≅ F where
  hom := (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (TopCat.subsetInclusion Z)).counit.app F
  inv := pullbackPushforwardCounitAppInv Z F
  hom_inv_id := pullbackPushforwardCounitApp_hom_inv_id Z F
  inv_hom_id := pullbackPushforwardCounitApp_inv_hom_id Z F

/-- The forward map of `pullbackPushforwardCounitAppIso` is the adjunction counit. -/
@[simp, stacks 01AZ "closed-subspace counit isomorphism hom"]
theorem pullbackPushforwardCounitAppIso_hom (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (pullbackPushforwardCounitAppIso Z F).hom =
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.subsetInclusion Z)).counit.app F := sorry

/-- The inverse map of `pullbackPushforwardCounitAppIso` is explicit. -/
@[simp, stacks 01AZ "closed-subspace counit isomorphism inverse"]
theorem pullbackPushforwardCounitAppIso_inv (Z : Set X)
    (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (pullbackPushforwardCounitAppIso Z F).inv =
      pullbackPushforwardCounitAppInv Z F := sorry

/-- The explicit inverse of the pullback-pushforward unit on the ambient closed-support object.
-/
@[stacks 01AZ "inverse ambient closed-support pullback-pushforward unit"]
noncomputable def objectPullbackPushforwardUnitAppInv
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
          (object hZ F)) ⟶ object hZ F :=
  supportedUnitInv hZ F

/-- The pullback-pushforward unit followed by its explicit inverse is the identity. -/
@[simp, stacks 01AZ "ambient closed-support unit forward-inverse law"]
theorem objectPullbackPushforwardUnitApp_hom_inv_id
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
      (TopCat.subsetInclusion Z)).unit.app (object hZ F) ≫
        objectPullbackPushforwardUnitAppInv hZ F = 𝟙 _ := sorry

/-- The explicit inverse of the pullback-pushforward unit followed by the unit is the identity.
-/
@[simp, stacks 01AZ "ambient closed-support unit inverse-forward law"]
theorem objectPullbackPushforwardUnitApp_inv_hom_id
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    objectPullbackPushforwardUnitAppInv hZ F ≫
        (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
          (TopCat.subsetInclusion Z)).unit.app (object hZ F) = 𝟙 _ := sorry

/-- The pullback-pushforward unit on the ambient closed-support object is a literal isomorphism.
-/
@[stacks 01AZ "ambient closed-support pullback-pushforward unit isomorphism"]
noncomputable def objectPullbackPushforwardUnitAppIso
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    object hZ F ≅
      (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
        ((Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
          (object hZ F)) where
  hom := (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
    (TopCat.subsetInclusion Z)).unit.app (object hZ F)
  inv := objectPullbackPushforwardUnitAppInv hZ F
  hom_inv_id := objectPullbackPushforwardUnitApp_hom_inv_id hZ F
  inv_hom_id := objectPullbackPushforwardUnitApp_inv_hom_id hZ F

/-- The forward map of `objectPullbackPushforwardUnitAppIso` is the adjunction unit. -/
@[simp, stacks 01AZ "ambient closed-support unit isomorphism hom"]
theorem objectPullbackPushforwardUnitAppIso_hom
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (objectPullbackPushforwardUnitAppIso hZ F).hom =
      (Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u}
        (TopCat.subsetInclusion Z)).unit.app (object hZ F) := sorry

/-- The inverse map of `objectPullbackPushforwardUnitAppIso` is explicit. -/
@[simp, stacks 01AZ "ambient closed-support unit isomorphism inverse"]
theorem objectPullbackPushforwardUnitAppIso_inv
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (objectPullbackPushforwardUnitAppIso hZ F).inv =
      objectPullbackPushforwardUnitAppInv hZ F := sorry

/-- The unit component for the closed-subset pushforward/closed-support adjunction. -/
@[stacks 01AZ "closed-support adjunction unit component"]
noncomputable def unitApp
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    F ⟶
      (functor hZ).obj
        ((Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj F) :=
  pullbackPushforwardCounitAppInv Z F ≫
    (Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).map
      (inclusionPushforwardInv hZ F)

/-- The counit component for the closed-subset pushforward/closed-support adjunction. -/
@[stacks 01AZ "closed-support adjunction counit component"]
noncomputable def counitApp
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).obj
        ((functor hZ).obj F) ⟶ F :=
  objectPullbackPushforwardUnitAppInv hZ F ≫
    inclusion hZ F

/-- Lemma 17.6.3 (01AZ) (1): pushforward from a closed subset is left adjoint to the additive
sheaf of sections supported on that subset. -/
@[stacks 01AZ "(1)"]
noncomputable def adjunction
    (hZ : IsClosed Z) :
    Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z) ⊣ functor hZ where
  unit :=
    { app := unitApp hZ
      naturality := sorry }
  counit :=
    { app := counitApp hZ
      naturality := sorry }
  left_triangle_components := sorry
  right_triangle_components := sorry

/-- The unit of the closed-support adjunction is the explicit unit component. -/
@[simp, stacks 01AZ "closed-support adjunction unit app"]
theorem adjunction_unit_app
    (hZ : IsClosed Z) (F : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) :
    (adjunction hZ).unit.app F = unitApp hZ F := sorry

/-- The counit of the closed-support adjunction is the explicit counit component. -/
@[simp, stacks 01AZ "closed-support adjunction counit app"]
theorem adjunction_counit_app
    (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (adjunction hZ).counit.app F = counitApp hZ F := sorry

/-- Closed-subset pushforward is a left adjoint. -/
theorem pushforwardIsLeftAdjointOfIsClosed (hZ : IsClosed Z) :
    (Sheaf.pushforward AddCommGrpCat.{u}
      (TopCat.subsetInclusion Z)).IsLeftAdjoint :=
  (adjunction hZ).isLeftAdjoint

/-- The closed-support functor is a right adjoint. -/
noncomputable instance functorIsRightAdjoint (hZ : IsClosed Z) :
    (functor (C := AddCommGrpCat.{u}) hZ).IsRightAdjoint :=
  (adjunction hZ).isRightAdjoint

/-- The closed-support functor is additive. -/
noncomputable instance functorAdditive (hZ : IsClosed Z)
    [(Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)).Additive] :
    (functor (C := AddCommGrpCat.{u}) hZ).Additive := sorry

/-- Lemma 17.6.3 (01AZ) (2): pushforward from a closed subset preserves arbitrary colimits. -/
@[stacks 01AZ "(2)"]
theorem pushforwardPreservesColimitsOfIsClosed (hZ : IsClosed Z) :
    PreservesColimits
      (Sheaf.pushforward AddCommGrpCat.{u} (TopCat.subsetInclusion Z)) := sorry

/-- Lemma 17.6.3 (01AZ): for a bundled closed subset, preservation of arbitrary colimits by
pushforward is available directly to typeclass search. -/
@[stacks 01AZ "bundled closed-set colimit instance"]
noncomputable instance pushforwardPreservesColimits (Z : Closeds X) :
    PreservesColimits
      (Sheaf.pushforward AddCommGrpCat.{u}
        (TopCat.subsetInclusion (Z : Set X))) := sorry

end TopCat.Sheaf.ClosedSubset.SectionsWithSupport

end
