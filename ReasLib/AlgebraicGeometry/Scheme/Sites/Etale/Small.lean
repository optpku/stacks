/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Small-to-big étale relocalization

This leaf owns the reusable site and sheaf API for the functor which sends an
étale scheme over `T` to the same scheme over `S` along `f : T ⟶ S`.
It exposes both objectwise computations and the adjunction and exactness
interfaces of the construction.
Cross-layer comparisons with big étale morphisms live in the narrower
`Sites/Etale/SmallToBig` leaf.
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
namespace Etale
namespace SmallToBig

variable {S T : Scheme.{u}}

/-- The relocalization functor from the small étale site of `T` to the big
étale slice site over `S`. -/
abbrev relocalizationFunctor (f : T ⟶ S) : T.Etale ⥤ Over S :=
  MorphismProperty.Over.forget @Etale ⊤ T ⋙ Over.map f

/-- The relocalization functor is continuous for the small-to-big étale
topologies. -/
instance relocalizationFunctor_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (relocalizationFunctor f) T.smallEtaleTopology
      (S.overGrothendieckTopology @Etale) := sorry

/-- The relocalization functor is cocontinuous for the small-to-big étale
topologies. -/
instance relocalizationFunctor_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (relocalizationFunctor f) T.smallEtaleTopology
      (S.overGrothendieckTopology @Etale) := sorry

/-- The small étale site has all finite connected limits. -/
instance hasFiniteConnectedLimits (T : Scheme.{u}) :
    HasFiniteConnectedLimits T.Etale := sorry

/-- Étale relocalization preserves all finite connected limits. -/
instance Relocalization.preservesFiniteConnectedLimits (f : T ⟶ S) :
    PreservesFiniteConnectedLimits (relocalizationFunctor f) := sorry

/-- The opposite relocalization functor has the left Kan extensions needed for
the lower-shriek construction. -/
instance relocalizationFunctor_op_hasLeftKanExtension
    (f : T ⟶ S) (P : T.Etaleᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasLeftKanExtension P := sorry

/-- The opposite relocalization functor has pointwise right Kan extensions
needed for the cocontinuous direct-image presentation. -/
instance relocalizationFunctor_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : T.Etaleᵒᵖ ⥤ Type w) :
    (relocalizationFunctor f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on sheaves induced by étale relocalization. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (S.overGrothendieckTopology @Etale) (Type w) ⥤
      Sheaf T.smallEtaleTopology (Type w) :=
  (relocalizationFunctor f).sheafPushforwardContinuous (Type w)
    T.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- The inverse image is computed by evaluating on the same scheme viewed over
`S`. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S)
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type w)) (U : T.Etale) :
    ((inverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S)
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type w)) (U : T.Etale) :
    ((inverseImage f).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (relocalizationFunctor f) (Type w) 𝒢 U

/-- The inverse-image objectwise comparison is an isomorphism. -/
theorem inverseImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type w)) (U : T.Etale) :
    IsIso ((inverseImage_objObjIso f 𝒢 U).hom) := sorry

/-- The inverse-image objectwise comparison is natural in the small étale
object. -/
theorem inverseImage_objObjIso_naturality
    (f : T ⟶ S) (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type w))
    {U V : T.Etale} (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.1.map ((relocalizationFunctor f).map φ).op =
      ((inverseImage f).obj 𝒢).1.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The lower-shriek functor on étale sheaves. -/
abbrev lowerShriek (f : T ⟶ S)
    [HasWeakSheafify (S.overGrothendieckTopology @Etale) (Type w)] :
    Sheaf T.smallEtaleTopology (Type w) ⥤
      Sheaf (S.overGrothendieckTopology @Etale) (Type w) :=
  (relocalizationFunctor f).sheafPullback (Type w) T.smallEtaleTopology
    (S.overGrothendieckTopology @Etale)

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [HasWeakSheafify (S.overGrothendieckTopology @Etale) (Type w)] :
    lowerShriek f ⊣ inverseImage f :=
  (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
    T.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- The lower-shriek adjunction agrees with the canonical continuous-site
adjunction. -/
theorem lowerShriekAdjunction_def (f : T ⟶ S)
    [HasWeakSheafify (S.overGrothendieckTopology @Etale) (Type w)] :
    lowerShriekAdjunction f =
      (relocalizationFunctor f).sheafAdjunctionContinuous (Type w)
        T.smallEtaleTopology (S.overGrothendieckTopology @Etale) := sorry

/-- The inverse image is a right adjoint whenever lower shriek is available. -/
theorem inverseImage_isRightAdjoint (f : T ⟶ S)
    [HasWeakSheafify (S.overGrothendieckTopology @Etale) (Type w)] :
    (inverseImage f).IsRightAdjoint := sorry

/-- The direct-image functor presented by the cocontinuous relocalization
functor. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf T.smallEtaleTopology (Type w) ⥤
      Sheaf (S.overGrothendieckTopology @Etale) (Type w) :=
  (relocalizationFunctor f).sheafPushforwardCocontinuous (Type w)
    T.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- The relocalization inverse image preserves finite limits. -/
instance inverseImage_preservesFiniteLimits (f : T ⟶ S) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by étale relocalization. -/
noncomputable def morphismOfTopoi (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type w)] :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, w}
      (S.overGrothendieckTopology @Etale) T.smallEtaleTopology where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (relocalizationFunctor f).sheafAdjunctionCocontinuous (Type w)
      T.smallEtaleTopology (S.overGrothendieckTopology @Etale)

/-- The inverse-image projection of the cocontinuously presented morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type w)] :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the cocontinuously presented morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S)
    [HasSheafify T.smallEtaleTopology (Type w)] :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- The inverse-image computation through the bundled relocalization morphism. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : T ⟶ S) [HasSheafify T.smallEtaleTopology (Type w)]
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type w)) (U : T.Etale) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).1.obj (op U))
    (morphismOfTopoi_inverseImage f)) ≪≫ inverseImage_objObjIso f 𝒢 U

/-- The lower-shriek adjunction with the inverse-image projection of the bundled morphism. -/
noncomputable def lowerShriekAdjunction_via_morphism (f : T ⟶ S)
    [HasWeakSheafify (S.overGrothendieckTopology @Etale) (Type w)]
    [HasSheafify T.smallEtaleTopology (Type w)] :
    lowerShriek f ⊣ (morphismOfTopoi f)⁻¹ :=
  (lowerShriekAdjunction f).ofNatIsoRight
    (eqToIso (morphismOfTopoi_inverseImage f)).symm

section Identity

variable (S : Scheme.{u})

/-- The identity-base relocalization is a morphism of small-to-big étale sites. -/
instance identity_isMorphismOfSites :
    CategoryTheory.IsMorphismOfSites S.smallEtaleTopology
      (S.overGrothendieckTopology @Etale) (relocalizationFunctor (𝟙 S)) := sorry

/-- The inverse image of the identity-base small-to-big site morphism preserves finite limits. -/
instance identity_sheafPullback_preservesFiniteLimits :
    PreservesFiniteLimits
      ((relocalizationFunctor (𝟙 S)).sheafPullback (Type (u + 1))
        S.smallEtaleTopology (S.overGrothendieckTopology @Etale)) := sorry

/-- The morphism of topoi induced by the identity-base small-to-big étale site morphism. -/
noncomputable def siteMorphismOfTopoi :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      S.smallEtaleTopology (S.overGrothendieckTopology @Etale) :=
  Functor.morphismOfTopoiInOfContinuous.{u + 1, u + 1, u + 1, u, u}
    (relocalizationFunctor (𝟙 S)) S.smallEtaleTopology
      (S.overGrothendieckTopology @Etale)

/-- For identity-base étale relocalization, the inverse image of the
relocalization morphism equals the direct image of the induced site morphism. -/
theorem morphismOfTopoi_id_inverseImage_eq_siteMorphismOfTopoi_pushforward :
    (morphismOfTopoi (𝟙 S))⁻¹ = (siteMorphismOfTopoi S).pushforward := sorry

/-- The identity-base small-to-big site morphism is a retraction of the
relocalization morphism of topoi. -/
theorem siteMorphismOfTopoi_comp_morphismOfTopoi_id :
    MorphismOfTopoiIn.comp (siteMorphismOfTopoi S) (morphismOfTopoi (𝟙 S)) =
      MorphismOfTopoiIn.id S.smallEtaleTopology := sorry

/-- The direct image of the identity-base site morphism is computed by evaluation on relocalized
small étale objects. -/
theorem siteMorphismOfTopoi_pushforward_obj_obj
    (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1))) (U : S.Etale) :
    ((siteMorphismOfTopoi S).pushforward.obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor (𝟙 S)).obj U)) := sorry

end Identity

end SmallToBig
end Etale
end AlgebraicGeometry.Scheme
