/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ZariskiSite.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Limits.Over.FiniteConnected
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big Zariski sheaf functors

This leaf packages the slice-site functors associated with a morphism of schemes on
the big Zariski topology.  The underlying categorical data is the canonical
`Over.map`/`Over.pullback` adjunction.  Both the cocontinuous and continuous
direct-image presentations are exposed, together with objectwise computation,
naturality, and finite-limit APIs for downstream use.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace Zariski
namespace Big

variable {S T : Scheme.{u}}

/-- Postcomposition on the big Zariski slice categories. -/
abbrev map (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Pullback on the big Zariski slice categories. -/
abbrev pullback (f : T ⟶ S) : Over S ⥤ Over T :=
  Over.pullback f

/-- The postcomposition functor is continuous for the big Zariski slice topologies. -/
instance map_isContinuous (f : T ⟶ S) :
    (map f).IsContinuous T.bigZariskiTopology S.bigZariskiTopology := sorry

/-- The postcomposition functor is cocontinuous for the big Zariski slice topologies. -/
instance map_isCocontinuous (f : T ⟶ S) :
    (map f).IsCocontinuous T.bigZariskiTopology S.bigZariskiTopology := sorry

/-- The canonical postcomposition-pullback adjunction on big Zariski slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- The map-pullback adjunction is the canonical adjunction on over-categories. -/
theorem mapPullbackAdjunction_def (f : T ⟶ S) :
    mapPullbackAdjunction f = Over.mapPullbackAdj f := sorry

/-- Pullback is continuous for the big Zariski slice topologies. -/
instance pullback_isContinuous (f : T ⟶ S) :
    (pullback f).IsContinuous S.bigZariskiTopology T.bigZariskiTopology := sorry

/-- The postcomposition presentation has the left Kan extensions used by lower shriek. -/
instance map_op_hasLeftKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- The postcomposition presentation has pointwise right Kan extensions used by direct-image
computations. -/
instance map_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on big Zariski sheaves. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf S.bigZariskiTopology (Type (u + 1)) ⥤
      Sheaf T.bigZariskiTopology (Type (u + 1)) :=
  (map f).sheafPushforwardContinuous (Type (u + 1))
    T.bigZariskiTopology S.bigZariskiTopology

/-- The inverse image is computed by evaluation on the postcomposed slice object. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S)
    (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) =
      𝒢.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S)
    (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (map f) (Type (u + 1)) 𝒢 U

/-- The inverse-image objectwise comparison is an isomorphism on its hom component. -/
theorem inverseImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : Over T) :
    IsIso ((inverseImage_objObjIso f 𝒢 U).hom) := sorry

/-- The inverse-image objectwise comparison is natural in the slice object. -/
theorem inverseImage_objObjIso_naturality
    (f : T ⟶ S)
    (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1)))
    {U V : Over T} (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.obj.map ((map f).map φ).op =
      ((inverseImage f).obj 𝒢).obj.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The direct-image functor on big Zariski sheaves, presented cocontinuously. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf T.bigZariskiTopology (Type (u + 1)) ⥤
      Sheaf S.bigZariskiTopology (Type (u + 1)) :=
  (map f).sheafPushforwardCocontinuous (Type (u + 1))
    T.bigZariskiTopology S.bigZariskiTopology

/-- The bundled morphism of topoi presented by big Zariski postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn S.bigZariskiTopology T.bigZariskiTopology where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type (u + 1))
      T.bigZariskiTopology S.bigZariskiTopology

/-- The inverse-image projection of the bundled big Zariski morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big Zariski morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- Big Zariski morphisms of topoi compose along composition of scheme morphisms. -/
theorem morphismOfTopoi_comp
    {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

/-- The direct-image functor presented by the continuous pullback right adjoint. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf T.bigZariskiTopology (Type (u + 1)) ⥤
      Sheaf S.bigZariskiTopology (Type (u + 1)) :=
  (pullback f).sheafPushforwardContinuous (Type (u + 1))
    S.bigZariskiTopology T.bigZariskiTopology

/-- The continuous direct image is computed by evaluation on the pullback slice object. -/
theorem continuousDirectImage_obj_obj
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) =
      ℱ.obj.obj (op ((pullback f).obj U)) := sorry

/-- The continuous direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def continuousDirectImage_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (pullback f) (Type (u + 1)) ℱ U

/-- The continuous direct-image objectwise comparison is an isomorphism on its hom component. -/
theorem continuousDirectImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S) :
    IsIso ((continuousDirectImage_objObjIso f ℱ U).hom) := sorry

/-- The cocontinuous direct image is canonically identified with the continuous right-adjoint
presentation. -/
noncomputable def continuousDirectImageIsoDirectImage (f : T ⟶ S) :
    continuousDirectImage f ≅ directImage f :=
  Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f)

/-- The cocontinuous direct-image presentation agrees with the continuous pullback presentation. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage f ≅ continuousDirectImage f :=
  (continuousDirectImageIsoDirectImage f).symm

/-- The continuous/cocontinuous direct-image comparison is the canonical right-adjoint
comparison attached to `mapPullbackAdjunction`. -/
theorem continuousDirectImageIsoDirectImage_def (f : T ⟶ S) :
    continuousDirectImageIsoDirectImage f =
      Functor.ContinuousRightAdjoint.pushforwardContinuousIso
        (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f) := sorry

/-- The cocontinuous direct image is computed by evaluation on the pullback slice object. -/
noncomputable def directImage_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S) :
    (((directImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f) ℱ U

/-- The cocontinuous direct-image objectwise comparison is an isomorphism. -/
theorem directImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S) :
    IsIso ((directImage_objObjIso f ℱ U).hom) := sorry

/-- The cocontinuous direct-image comparison is natural in the slice object. -/
theorem directImage_objObjIso_naturality
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1)))
    {U V : Over S} (φ : U ⟶ V) :
    (directImage_objObjIso f ℱ V).hom ≫
        ℱ.obj.map ((pullback f).map φ).op =
      ((directImage f).obj ℱ).obj.map φ.op ≫
        (directImage_objObjIso f ℱ U).hom := sorry

/-- The continuous direct-image comparison is natural in the slice object. -/
theorem continuousDirectImage_objObjIso_naturality
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1)))
    {U V : Over S} (φ : U ⟶ V) :
    (continuousDirectImage_objObjIso f ℱ V).hom ≫
        ℱ.obj.map ((pullback f).map φ).op =
      ((continuousDirectImage f).obj ℱ).obj.map φ.op ≫
        (continuousDirectImage_objObjIso f ℱ U).hom := sorry

/-- The bundled inverse-image computation on every big Zariski slice object. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : T ⟶ S)
    (𝒢 : Sheaf S.bigZariskiTopology (Type (u + 1))) (U : Over T) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).obj.obj (op U))
    (morphismOfTopoi_inverseImage f)) ≪≫ inverseImage_objObjIso f 𝒢 U

/-- The bundled direct-image computation on every big Zariski slice object. -/
noncomputable def morphismOfTopoi_pushforward_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf T.bigZariskiTopology (Type (u + 1))) (U : Over S) :
    (((morphismOfTopoi f).pushforward.obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj ℱ).obj.obj (op U))
    (morphismOfTopoi_pushforward f)) ≪≫ directImage_objObjIso f ℱ U

/-- The bundled direct image agrees with the continuous pullback presentation. -/
noncomputable def morphismOfTopoi_pushforwardIsoPullbackPresentation (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward ≅ continuousDirectImage f :=
  eqToIso (morphismOfTopoi_pushforward f) ≪≫ directImageIsoPullbackPresentation f

/-- The lower-shriek functor on big Zariski sheaves. -/
abbrev lowerShriek (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))] :
    Sheaf T.bigZariskiTopology (Type (u + 1)) ⥤
      Sheaf S.bigZariskiTopology (Type (u + 1)) :=
  (map f).sheafPullback (Type (u + 1))
    T.bigZariskiTopology S.bigZariskiTopology

/-- The lower-shriek functor is a left adjoint whenever the target sheafification exists. -/
theorem lowerShriek_isLeftAdjoint (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))] :
    (lowerShriek f).IsLeftAdjoint := sorry

/-- The canonical lower-shriek/inverse-image adjunction on big Zariski sheaves. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))] :
    lowerShriek f ⊣ inverseImage f :=
  (map f).sheafAdjunctionContinuous (Type (u + 1))
    T.bigZariskiTopology S.bigZariskiTopology

/-- The lower-shriek adjunction with the inverse-image projection of the bundled morphism. -/
noncomputable def lowerShriekAdjunction_via_morphism (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))] :
    lowerShriek f ⊣ (morphismOfTopoi f)⁻¹ :=
  (lowerShriekAdjunction f).ofNatIsoRight
    (eqToIso (morphismOfTopoi_inverseImage f)).symm

/-- Lower shriek on big Zariski sheaves preserves pullbacks. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- Lower shriek on big Zariski sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S)
    [HasWeakSheafify S.bigZariskiTopology (Type (u + 1))] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

/-- The big Zariski inverse image is a right adjoint. -/
theorem inverseImage_isRightAdjoint (f : T ⟶ S) :
    (inverseImage f).IsRightAdjoint := sorry

end Big
end Zariski
end Scheme
end AlgebraicGeometry
