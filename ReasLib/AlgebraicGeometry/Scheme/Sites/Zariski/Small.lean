/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Pullback
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Small-to-big Zariski relocalization

This leaf owns the reusable site and sheaf API for the functor sending an open
scheme over `T` to the same scheme over `S` along `f : T ⟶ S`, together with
its computational, adjunction, and finite-limit interfaces.
Cross-layer comparisons with big Zariski morphisms live in the narrower
`Sites/Zariski/SmallToBig` leaf.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open AlgebraicGeometry
open scoped MorphismOfTopoiIn

noncomputable section

universe u w

namespace AlgebraicGeometry.Scheme
namespace Zariski
namespace SmallToBig

variable {S T : Scheme.{u}}

/-- The relocalization functor from the small Zariski site of `T` to the big
Zariski slice site over `S`. -/
abbrev relocalizationFunctor (f : T ⟶ S) : T.smallZariskiSite ⥤ S.bigZariskiSite :=
  MorphismProperty.Over.forget @IsOpenImmersion ⊤ T ⋙ Over.map f

/-- The small Zariski site has all finite connected limits. -/
instance hasFiniteConnectedLimits (T : Scheme.{u}) :
    HasFiniteConnectedLimits T.smallZariskiSite := sorry

/-- Zariski relocalization preserves all finite connected limits. -/
instance Relocalization.preservesFiniteConnectedLimits (f : T ⟶ S) :
    PreservesFiniteConnectedLimits (relocalizationFunctor f) := sorry

/-- The relocalization functor is continuous for the small-to-big Zariski topologies. -/
instance relocalizationFunctor_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (relocalizationFunctor f) T.smallZariskiTopology
      S.bigZariskiTopology := sorry

/-- The relocalization functor is cocontinuous for the small-to-big Zariski topologies. -/
instance relocalizationFunctor_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (relocalizationFunctor f) T.smallZariskiTopology
      S.bigZariskiTopology := sorry

/-- The opposite relocalization functor has the left Kan extensions used by lower shriek. -/
instance relocalizationFunctor_op_hasLeftKanExtension
    (f : T ⟶ S) (P : T.smallZariskiSiteᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasLeftKanExtension P := sorry

/-- The opposite relocalization functor has the pointwise right Kan extensions used by direct image. -/
instance relocalizationFunctor_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : T.smallZariskiSiteᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on sheaves induced by Zariski relocalization. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf S.bigZariskiTopology (Type w) ⥤ Sheaf T.smallZariskiTopology (Type w) :=
  (relocalizationFunctor f).sheafPushforwardContinuous (Type w)
    T.smallZariskiTopology S.bigZariskiTopology

/-- The inverse image is computed by evaluation on the same open scheme over `S`. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S) (𝒢 : Sheaf S.bigZariskiTopology (Type w)) (U : T.smallZariskiSite) :
    ((inverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S) (𝒢 : Sheaf S.bigZariskiTopology (Type w)) (U : T.smallZariskiSite) :
    ((inverseImage f).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (relocalizationFunctor f) (Type w) 𝒢 U

/-- The inverse-image objectwise comparison is an isomorphism. -/
theorem inverseImage_objObjIso_hom_isIso
    (f : T ⟶ S) (𝒢 : Sheaf S.bigZariskiTopology (Type w)) (U : T.smallZariskiSite) :
    IsIso ((inverseImage_objObjIso f 𝒢 U).hom) := sorry

/-- The inverse-image objectwise comparison is natural in the small Zariski object. -/
theorem inverseImage_objObjIso_naturality
    (f : T ⟶ S) (𝒢 : Sheaf S.bigZariskiTopology (Type w))
    {U V : T.smallZariskiSite} (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.1.map ((relocalizationFunctor f).map φ).op =
      ((inverseImage f).obj 𝒢).1.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The lower-shriek functor on small-to-big Zariski sheaves. -/
abbrev lowerShriek (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type w)] :
    Sheaf T.smallZariskiTopology (Type w) ⥤ Sheaf S.bigZariskiTopology (Type w) :=
  (relocalizationFunctor f).sheafPullback (Type w)
    T.smallZariskiTopology S.bigZariskiTopology

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type w)] :
    lowerShriek f ⊣ inverseImage f :=
  (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
    T.smallZariskiTopology S.bigZariskiTopology

/-- The lower-shriek adjunction agrees with the canonical continuous-site adjunction. -/
theorem lowerShriekAdjunction_def (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type w)] :
    lowerShriekAdjunction f =
      (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
        T.smallZariskiTopology S.bigZariskiTopology := sorry

/-- The inverse image is a right adjoint whenever lower shriek is available. -/
theorem inverseImage_isRightAdjoint (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type w)] :
    (inverseImage f).IsRightAdjoint := sorry

/-- The direct-image functor presented by cocontinuous Zariski relocalization. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf T.smallZariskiTopology (Type w) ⥤ Sheaf S.bigZariskiTopology (Type w) :=
  (relocalizationFunctor f).sheafPushforwardCocontinuous (Type w)
    T.smallZariskiTopology S.bigZariskiTopology

/-- The relocalization inverse image preserves finite limits. -/
instance inverseImage_preservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by Zariski relocalization. -/
noncomputable def morphismOfTopoi (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type w)] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, w}
      S.bigZariskiTopology T.smallZariskiTopology where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (relocalizationFunctor f).sheafAdjunctionCocontinuous (Type w)
      T.smallZariskiTopology S.bigZariskiTopology

/-- The inverse-image projection of the bundled Zariski relocalization morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type w)] :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled Zariski relocalization morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S)
    [HasSheafify T.smallZariskiTopology (Type w)] :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- The inverse-image computation through the bundled relocalization morphism. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : T ⟶ S) [HasSheafify T.smallZariskiTopology (Type w)]
    (𝒢 : Sheaf S.bigZariskiTopology (Type w)) (U : T.smallZariskiSite) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).1.obj (op U))
    (morphismOfTopoi_inverseImage f)) ≪≫ inverseImage_objObjIso f 𝒢 U

/-- The lower-shriek adjunction with the inverse-image projection of the bundled morphism. -/
noncomputable def lowerShriekAdjunction_via_morphism (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type w)]
    [HasSheafify T.smallZariskiTopology (Type w)] :
    lowerShriek f ⊣ (morphismOfTopoi f)⁻¹ :=
  (lowerShriekAdjunction f).ofNatIsoRight
    (eqToIso (morphismOfTopoi_inverseImage f)).symm

section Identity

variable (S : Scheme.{u})

/-- The identity-base relocalization is a morphism of small-to-big Zariski sites. -/
instance identity_isMorphismOfSites :
    CategoryTheory.IsMorphismOfSites S.smallZariskiTopology S.bigZariskiTopology
      (relocalizationFunctor (𝟙 S)) := sorry

/-- The inverse image of the identity-base small-to-big site morphism preserves finite limits. -/
instance identity_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).sheafPullback (Type (u + 1))
        S.smallZariskiTopology S.bigZariskiTopology) := sorry

/-- The morphism of topoi induced by the identity-base small-to-big Zariski site morphism. -/
noncomputable def siteMorphismOfTopoi :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      S.smallZariskiTopology S.bigZariskiTopology :=
  Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u, u}
    (relocalizationFunctor (𝟙 S)) S.smallZariskiTopology S.bigZariskiTopology

/-- The identity-base small-to-big site morphism is a retraction of the
relocalization morphism of topoi. -/
theorem siteMorphismOfTopoi_comp_morphismOfTopoi_id :
    MorphismOfTopoiIn.comp (siteMorphismOfTopoi S) (morphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id S.smallZariskiTopology := sorry

/-- The direct image of the identity-base site morphism is computed by evaluation on relocalized
small Zariski objects. -/
theorem siteMorphismOfTopoi_pushforward_obj_obj
    (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : S.smallZariskiSite) :
    ((siteMorphismOfTopoi S).pushforward.obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor (𝟙 S)).obj U)) := sorry

end Identity

end SmallToBig
end Zariski
end AlgebraicGeometry.Scheme
