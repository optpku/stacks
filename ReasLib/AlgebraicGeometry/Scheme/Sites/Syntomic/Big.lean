/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Basic
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big syntomic sheaf functors

This leaf packages the inverse-image, direct-image, and lower-shriek functors
attached to a morphism of schemes on the big syntomic slice sites.  The
underlying slice functors and their Kan-extension assumptions are owned by
`Sites.Syntomic.Basic`; the declarations here expose objectwise computation
and naturality APIs for downstream developments.
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
namespace Syntomic
namespace Big

variable {S T : Scheme.{u}}

/-- The inverse-image functor on sheaves induced by big syntomic postcomposition. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)) ⥤
      Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)) :=
  @Functor.sheafPushforwardContinuous _ _ _ _ (map f) (Type (u + 1)) _
    (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
    (map_isContinuous f)

/-- The inverse image is computed by evaluating on the postcomposed slice object. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S) (𝒢 : Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)))
    (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) =
      𝒢.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S) (𝒢 : Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)))
    (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  @Functor.sheafPushforwardContinuousObjObjIso _ _ _ _ (map f)
    (Type (u + 1)) _ (Scheme.syntomicOverTopology T)
      (Scheme.syntomicOverTopology S) (map_isContinuous f) 𝒢 U

/-- The inverse-image objectwise comparison is an isomorphism. -/
theorem inverseImage_objObjIso_hom_isIso
    (f : T ⟶ S) (𝒢 : Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)))
    (U : Over T) :
    IsIso ((inverseImage_objObjIso f 𝒢 U).hom) := sorry

/-- The inverse-image objectwise comparison is natural in the big syntomic slice object. -/
theorem inverseImage_objObjIso_naturality
    (f : T ⟶ S) (𝒢 : Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)))
    {U V : Over T} (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.obj.map ((map f).map φ).op =
      ((inverseImage f).obj 𝒢).obj.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The direct-image functor on sheaves induced by big syntomic postcomposition. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)) ⥤
      Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)) :=
  @Functor.sheafPushforwardCocontinuous _ _ _ _ (map f) (Type (u + 1)) _
    (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
      (map_isCocontinuous f) (map_op_hasPointwiseRightKanExtension f)

/-- The bundled morphism of topoi presented by big syntomic postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (Scheme.syntomicOverTopology S)
      (Scheme.syntomicOverTopology T) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    @Functor.sheafAdjunctionCocontinuous _ _ _ _ (map f) (Type (u + 1)) _
      (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
        (map_isCocontinuous f) (map_op_hasPointwiseRightKanExtension f)
          (map_isContinuous f)

/-- The inverse-image projection of the bundled big syntomic morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big syntomic morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- The continuous right-adjoint direct-image presentation on big syntomic sheaves. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)) ⥤
      Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)) :=
  @Functor.sheafPushforwardContinuous _ _ _ _
    (AlgebraicGeometry.Scheme.Syntomic.Big.pullback f) (Type (u + 1)) _
      (Scheme.syntomicOverTopology S) (Scheme.syntomicOverTopology T)
        (pullback_isContinuous f)

/-- The continuous direct image is computed by evaluation on the pullback slice object. -/
theorem continuousDirectImage_obj_obj
    (f : T ⟶ S) (ℱ : Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)))
    (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) =
      ℱ.obj.obj (op ((AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).obj U)) := sorry

/-- The continuous direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def continuousDirectImage_objObjIso
    (f : T ⟶ S) (ℱ : Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)))
    (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj
        (op ((AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).obj U)) :=
  @Functor.sheafPushforwardContinuousObjObjIso _ _ _ _
    (AlgebraicGeometry.Scheme.Syntomic.Big.pullback f) (Type (u + 1)) _
      (Scheme.syntomicOverTopology S) (Scheme.syntomicOverTopology T)
        (pullback_isContinuous f) ℱ U

/-- The direct-image functor is objectwise identified with evaluation on the pullback object. -/
noncomputable def directImage_objObjIso
    (f : T ⟶ S) (ℱ : Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)))
    (U : Over S) :
    (((directImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj
        (op ((AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).obj U)) :=
  @Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    _ _ _ _ (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
      (map f) (AlgebraicGeometry.Scheme.Syntomic.Big.pullback f)
        (Type (u + 1)) _ (mapPullbackAdjunction f) (pullback_isContinuous f)
          (map_isCocontinuous f) (map_op_hasPointwiseRightKanExtension f) ℱ U

/-- The direct-image objectwise comparison is an isomorphism. -/
theorem directImage_objObjIso_hom_isIso
    (f : T ⟶ S) (ℱ : Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)))
    (U : Over S) :
    IsIso ((directImage_objObjIso f ℱ U).hom) := sorry

/-- The direct-image objectwise comparison is natural in the big syntomic slice object. -/
theorem directImage_objObjIso_naturality
    (f : T ⟶ S) (ℱ : Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)))
    {U V : Over S} (φ : U ⟶ V) :
    (directImage_objObjIso f ℱ V).hom ≫
        ℱ.obj.map
          ((AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).map φ).op =
      ((directImage f).obj ℱ).obj.map φ.op ≫
        (directImage_objObjIso f ℱ U).hom := sorry

/-- The continuous right-adjoint direct-image presentation is canonically isomorphic to the
cocontinuous presentation. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage f ≅ continuousDirectImage f :=
  (@Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    _ _ _ _ (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
      (map f) (AlgebraicGeometry.Scheme.Syntomic.Big.pullback f)
        (Type (u + 1)) _ (mapPullbackAdjunction f) (pullback_isContinuous f)
          (map_isCocontinuous f) (map_op_hasPointwiseRightKanExtension f)).symm

/-- The bundled big syntomic morphism has the same direct-image comparison as its
cocontinuous presentation. -/
noncomputable def morphismOfTopoi_pushforwardIsoPullbackPresentation (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward ≅ continuousDirectImage f :=
  eqToIso (morphismOfTopoi_pushforward f) ≪≫ directImageIsoPullbackPresentation f

/-- The inverse-image objectwise computation through the bundled morphism. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : T ⟶ S) (𝒢 : Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)))
    (U : Over T) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).obj.obj (op U))
    (morphismOfTopoi_inverseImage f)) ≪≫ inverseImage_objObjIso f 𝒢 U

/-- The direct-image objectwise computation through the bundled morphism. -/
noncomputable def morphismOfTopoi_pushforward_objObjIso
    (f : T ⟶ S) (ℱ : Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)))
    (U : Over S) :
    (((morphismOfTopoi f).pushforward.obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj
        (op ((AlgebraicGeometry.Scheme.Syntomic.Big.pullback f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj ℱ).obj.obj (op U))
    (morphismOfTopoi_pushforward f)) ≪≫ directImage_objObjIso f ℱ U

/-- The forward morphism in the direct-image presentation comparison is an isomorphism. -/
theorem directImageIsoPullbackPresentation_hom_isIso (f : T ⟶ S) :
    IsIso (directImageIsoPullbackPresentation f).hom := sorry

/-- The lower-shriek functor on big syntomic sheaves. -/
abbrev lowerShriek (f : T ⟶ S)
    [HasWeakSheafify (Scheme.syntomicOverTopology S) (Type (u + 1))] :
    Sheaf (Scheme.syntomicOverTopology T) (Type (u + 1)) ⥤
      Sheaf (Scheme.syntomicOverTopology S) (Type (u + 1)) :=
  @Functor.sheafPullback _ _ _ _ (map f) (Type (u + 1)) _
    (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
      (map_isContinuous f)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          _ _ _ _ (map f) (Type (u + 1)) _
            (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
              (map_isContinuous f) (map_op_hasLeftKanExtension f)
                inferInstance).isRightAdjoint

/-- The canonical lower-shriek/inverse-image adjunction on big syntomic sheaves. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S)
    [HasWeakSheafify (Scheme.syntomicOverTopology S) (Type (u + 1))] :
    lowerShriek f ⊣ inverseImage f :=
  @Functor.sheafAdjunctionContinuous _ _ _ _ (map f) (Type (u + 1)) _
    (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
      (map_isContinuous f)
        (@Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          _ _ _ _ (map f) (Type (u + 1)) _
            (Scheme.syntomicOverTopology T) (Scheme.syntomicOverTopology S)
              (map_isContinuous f) (map_op_hasLeftKanExtension f)
                inferInstance).isRightAdjoint

/-- The lower-shriek adjunction with the inverse-image projection of the bundled morphism. -/
noncomputable def lowerShriekAdjunction_via_morphism (f : T ⟶ S)
    [HasWeakSheafify (Scheme.syntomicOverTopology S) (Type (u + 1))] :
    lowerShriek f ⊣ (morphismOfTopoi f)⁻¹ :=
  (lowerShriekAdjunction f).ofNatIsoRight
    (eqToIso (morphismOfTopoi_inverseImage f)).symm

/-- The big syntomic inverse image is a right adjoint. -/
theorem inverseImage_isRightAdjoint (f : T ⟶ S)
    [HasWeakSheafify (Scheme.syntomicOverTopology S) (Type (u + 1))] :
    (inverseImage f).IsRightAdjoint := sorry

/-- The lower-shriek functor on big syntomic sheaves preserves pullbacks. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S)
    [HasWeakSheafify (Scheme.syntomicOverTopology S) (Type (u + 1))] :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- The lower-shriek functor on big syntomic sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S)
    [HasWeakSheafify (Scheme.syntomicOverTopology S) (Type (u + 1))] :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

end Big
end Syntomic
end Scheme
end AlgebraicGeometry
