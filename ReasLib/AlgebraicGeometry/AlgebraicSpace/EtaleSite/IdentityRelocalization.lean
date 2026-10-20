/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Relocalization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SpacesPullback
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.CategoryTheory.Sites.MorphismOfSites
public import ReasLib.CategoryTheory.Sites.FullyFaithful
public import ReasLib.CategoryTheory.Sites.Topos.Continuous

/-! # Identity-base relocalization of étale sites

The inclusion of the spaces-étale site into the big étale slice is fully faithful
and induces a site morphism whose geometric morphism retracts relocalization.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace
namespace Etale
namespace SmallToBig

variable {S : Scheme.{u}}

/-- Identity-base small-to-big étale relocalization admits pointwise left Kan
extensions with coefficients in a universe containing its comma categories. -/
instance relocalizationFunctor_id_op_hasPointwiseLeftKanExtension
    [UnivLE.{u + 1, w}] (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor (𝟙 X)).op.HasPointwiseLeftKanExtension P :=
  fun _ ↦ inferInstance

/-- Identity-base small-to-big étale relocalization admits left Kan extensions
with coefficients in a universe containing its comma categories. -/
instance relocalizationFunctor_id_op_hasLeftKanExtension
    [UnivLE.{u + 1, w}] (X : AlgebraicSpace S)
    (P : (smallEtaleSite X)ᵒᵖ ⥤ Type w) :
    (relocalizationFunctor (𝟙 X)).op.HasLeftKanExtension P :=
  inferInstance

/-- Sheaf pullback along identity-base small-to-big étale relocalization
preserves finite limits. -/
instance relocalizationFunctor_id_sheafPullback_preservesFiniteLimits
    (X : AlgebraicSpace S) :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).sheafPullback.{u + 1, u, u + 1, u + 2, u + 1, u + 1}
        (Type (u + 1)) (smallEtaleTopology X)
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)) := sorry

/-- The canonical morphism from the big étale topos to the small étale topos
is induced by identity-base small-to-big étale relocalization. -/
def siteMorphismOfTopoi (X : AlgebraicSpace S) :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u + 1, u + 1}
      (smallEtaleTopology X)
      (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X) :=
  Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u, u + 1}
    (relocalizationFunctor (𝟙 X)) (smallEtaleTopology X)
    (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X)

/-- The big-to-small étale comparison is the geometric morphism of the
identity-base relocalization functor. -/
theorem siteMorphismOfTopoi_eq (X : AlgebraicSpace S) :
    siteMorphismOfTopoi X =
      Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u, u + 1}
        (relocalizationFunctor (𝟙 X)) (smallEtaleTopology X)
        (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X) :=
  rfl

/-- Direct image from the big étale topos to the small étale topos is
restriction along identity-base relocalization. -/
@[simp]
theorem siteMorphismOfTopoi_pushforward (X : AlgebraicSpace S) :
    (siteMorphismOfTopoi X).pushforward =
      (relocalizationFunctor (𝟙 X)).sheafPushforwardContinuous (Type (u + 1))
        (smallEtaleTopology X) (AlgebraicGeometry.AlgebraicSpace.overEtaleTopology X) :=
  rfl

end SmallToBig

namespace SpacesToBig

section Identity

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

/-- The identity-base relocalization is canonically isomorphic to the inclusion
of the spaces-étale site into the big étale slice. -/
def relocalizationFunctor_id_iso :
    relocalizationFunctor (𝟙 X) ≅ MorphismProperty.Over.forget (@Etale S) ⊤ X :=
  Functor.isoWhiskerLeft (MorphismProperty.Over.forget (@Etale S) ⊤ X) (Over.mapId X) ≪≫
    Functor.rightUnitor (MorphismProperty.Over.forget (@Etale S) ⊤ X)

/-- The identity-base relocalization is full. -/
instance relocalizationFunctor_id_full :
    (relocalizationFunctor (𝟙 X)).Full :=
  Functor.Full.of_iso (relocalizationFunctor_id_iso X).symm

/-- The identity-base relocalization is faithful. -/
instance relocalizationFunctor_id_faithful :
    (relocalizationFunctor (𝟙 X)).Faithful :=
  Functor.Faithful.of_iso (relocalizationFunctor_id_iso X).symm

/-- The identity-base relocalization sends the spaces-étale terminal object `X/X`
to a terminal object of the big étale slice. -/
noncomputable def relocalizationFunctor_id_obj_isTerminal :
    IsTerminal ((relocalizationFunctor (𝟙 X)).obj (spacesEtaleSite.self X)) :=
  IsTerminal.ofIso Over.mkIdTerminal
    ((relocalizationFunctor_id_iso X).app (spacesEtaleSite.self X)).symm

/-- The identity-base relocalization is a morphism of spaces-étale to big étale
sites. -/
instance identity_isMorphismOfSites :
    IsMorphismOfSites (spacesEtaleTopology X) (overEtaleTopology X)
      (relocalizationFunctor (𝟙 X)) := sorry

/-- The inverse image of the identity-base spaces-to-big site morphism preserves
finite limits. -/
instance identity_sheafPullback_preservesFiniteLimits
    [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 X)).sheafPullback (Type w)
        (spacesEtaleTopology X) (overEtaleTopology X)) := sorry

/-- The morphism of topoi induced by the identity-base spaces-to-big étale site
morphism. -/
noncomputable def siteMorphismOfTopoi
    [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)] :
    MorphismOfTopoiIn.{u + 1, u + 1, u + 1, u + 1, w}
      (spacesEtaleTopology X) (overEtaleTopology X) :=
  Functor.morphismOfTopoiInOfContinuous.{w, u + 1, u + 1, u + 1, u + 1}
    (relocalizationFunctor (𝟙 X)) (spacesEtaleTopology X) (overEtaleTopology X)

/-- For identity-base spaces-étale relocalization, the inverse image of `i_X`
equals the direct image of the induced site morphism `π_X`. -/
theorem morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward
    [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    [HasSheafify (spacesEtaleTopology X) (Type w)] :
    (morphismOfTopoi (𝟙 X))⁻¹ = (siteMorphismOfTopoi X).pushforward :=
  rfl

/-- The composite inverse image of the identity-base site morphism `π_X` and the
relocalization morphism `i_{id_X}` is naturally isomorphic to the identity. -/
noncomputable def siteMorphismOfTopoi_comp_morphismOfTopoi_id
    [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    [HasSheafify (spacesEtaleTopology X) (Type w)] :
    (MorphismOfTopoiIn.comp (siteMorphismOfTopoi X) (morphismOfTopoi (𝟙 X))).inverseImage ≅
      (MorphismOfTopoiIn.id (spacesEtaleTopology X)).inverseImage :=
  (asIso
    ((relocalizationFunctor (𝟙 X)).sheafAdjunctionContinuous (Type w)
      (spacesEtaleTopology X) (overEtaleTopology X)).unit).symm

/-- The direct image of the identity-base site morphism is computed by
evaluation on relocalized spaces-étale objects. -/
theorem siteMorphismOfTopoi_pushforward_obj_obj
    [UnivLE.{u + 1, w}]
    [HasWeakSheafify (overEtaleTopology X) (Type w)]
    (𝒢 : Sheaf (overEtaleTopology X) (Type w)) (U : spacesEtaleSite X) :
    ((siteMorphismOfTopoi X).pushforward.obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor (𝟙 X)).obj U)) :=
  rfl

end Identity

end SpacesToBig

end Etale
end AlgebraicGeometry.AlgebraicSpace
