/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Limits.Over.FiniteConnected
public import ReasLib.CategoryTheory.Sites.Pullback.FiniteConnectedLimits
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big étale sheaf functors

This leaf packages the slice-site functors associated with a morphism of schemes on the big
étale topology.  It exposes both the cocontinuous direct-image presentation and the continuous
right-adjoint presentation, together with objectwise and naturality APIs.
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
namespace Etale
namespace Big

variable {S T : Scheme.{u}}

/-- Postcomposition on the big étale slice categories. -/
abbrev map (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Pullback on the big étale slice categories. -/
abbrev pullback (f : T ⟶ S) : Over S ⥤ Over T :=
  Over.pullback f

/-- The postcomposition functor is continuous for the big étale slice topologies. -/
instance map_isContinuous (f : T ⟶ S) :
    (map f).IsContinuous (T.overGrothendieckTopology @Etale)
      (S.overGrothendieckTopology @Etale) := sorry

/-- The postcomposition functor is cocontinuous for the big étale slice topologies. -/
instance map_isCocontinuous (f : T ⟶ S) :
    (map f).IsCocontinuous (T.overGrothendieckTopology @Etale)
      (S.overGrothendieckTopology @Etale) := sorry

/-- The canonical postcomposition-pullback adjunction on big étale slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Pullback is continuous for the big étale slice topologies. -/
instance pullback_isContinuous (f : T ⟶ S) :
    (pullback f).IsContinuous (S.overGrothendieckTopology @Etale)
      (T.overGrothendieckTopology @Etale) := sorry

/-- The `map f` presentation has the left-Kan-extension hypotheses used by lower shriek. -/
instance map_op_hasLeftKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- The `map f` presentation has the pointwise right-Kan-extension hypotheses used by direct
image computations. -/
instance map_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on big étale sheaves. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤
      Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)) :=
  (map f).sheafPushforwardContinuous (Type (u + 1))
    (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- The inverse image is computed by evaluating on the postcomposed slice object. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S) (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) =
      𝒢.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S) (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (map f) (Type (u + 1)) 𝒢 U

/-- The inverse-image objectwise comparison is an isomorphism. -/
theorem inverseImage_objObjIso_hom_isIso
    (f : T ⟶ S) (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over T) :
    IsIso ((inverseImage_objObjIso f 𝒢 U).hom) := sorry

/-- The inverse-image objectwise comparison is natural in the big étale slice object. -/
theorem inverseImage_objObjIso_naturality
    (f : T ⟶ S) (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    {U V : Over T} (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.obj.map ((map f).map φ).op =
      ((inverseImage f).obj 𝒢).obj.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The direct-image functor on big étale sheaves, presented cocontinuously. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤
      Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) :=
  (map f).sheafPushforwardCocontinuous (Type (u + 1))
    (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- The direct-image functor presented by the continuous pullback right adjoint. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤
      Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) :=
  (pullback f).sheafPushforwardContinuous (Type (u + 1))
    (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale)

/-- The continuous direct image is computed by evaluation on the pullback slice object. -/
theorem continuousDirectImage_obj_obj
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) =
      ℱ.obj.obj (op ((pullback f).obj U)) := sorry

/-- The continuous direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def continuousDirectImage_objObjIso
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (pullback f) (Type (u + 1)) ℱ U

/-- The continuous direct-image objectwise comparison is an isomorphism. -/
theorem continuousDirectImage_objObjIso_hom_isIso
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over S) :
    IsIso ((continuousDirectImage_objObjIso f ℱ U).hom) := sorry

/-- The bundled morphism of topoi presented by big étale postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (S.overGrothendieckTopology @Etale)
      (T.overGrothendieckTopology @Etale) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- The inverse-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- Big étale morphisms of topoi compose along composition of scheme morphisms. -/
theorem morphismOfTopoi_comp
    {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

/-- The direct image is objectwise identified with evaluation on the pullback slice object. -/
noncomputable def directImage_objObjIso
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over S) :
    (((directImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f) ℱ U

/-- The direct-image objectwise comparison is an isomorphism. -/
theorem directImage_objObjIso_hom_isIso
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over S) :
    IsIso ((directImage_objObjIso f ℱ U).hom) := sorry

/-- The direct-image objectwise comparison is natural in the big étale slice object. -/
theorem directImage_objObjIso_naturality
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    {U V : Over S} (φ : U ⟶ V) :
    (directImage_objObjIso f ℱ V).hom ≫
        ℱ.obj.map ((pullback f).map φ).op =
      ((directImage f).obj ℱ).obj.map φ.op ≫
        (directImage_objObjIso f ℱ U).hom := sorry

/-- The continuous right-adjoint direct-image presentation is canonically isomorphic to the
cocontinuous presentation. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage f ≅
      (pullback f).sheafPushforwardContinuous (Type (u + 1))
        (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f)).symm

/-- The bundled inverse-image computation on every big étale slice object. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : T ⟶ S) (𝒢 : Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over T) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).obj.obj (op U))
    (morphismOfTopoi_inverseImage f)) ≪≫ inverseImage_objObjIso f 𝒢 U

/-- The bundled direct-image computation on every big étale slice object. -/
noncomputable def morphismOfTopoi_pushforward_objObjIso
    (f : T ⟶ S) (ℱ : Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)))
    (U : Over S) :
    (((morphismOfTopoi f).pushforward.obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj ℱ).obj.obj (op U))
    (morphismOfTopoi_pushforward f)) ≪≫ directImage_objObjIso f ℱ U

/-- The bundled big étale direct-image presentation agrees with the pullback presentation. -/
noncomputable def morphismOfTopoi_pushforwardIsoPullbackPresentation (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward ≅
      (pullback f).sheafPushforwardContinuous (Type (u + 1))
        (S.overGrothendieckTopology @Etale) (T.overGrothendieckTopology @Etale) :=
  eqToIso (morphismOfTopoi_pushforward f) ≪≫ directImageIsoPullbackPresentation f

/-- The continuous and cocontinuous direct-image presentations are canonically isomorphic. -/
noncomputable def continuousDirectImageIsoDirectImage (f : T ⟶ S) :
    continuousDirectImage f ≅ directImage f :=
  (directImageIsoPullbackPresentation f).symm

/-- The continuous-to-cocontinuous direct-image comparison has an invertible forward morphism. -/
theorem continuousDirectImageIsoDirectImage_hom_isIso (f : T ⟶ S) :
    IsIso (continuousDirectImageIsoDirectImage f).hom := sorry

/-- The forward morphism in the direct-image presentation comparison is an isomorphism. -/
theorem directImageIsoPullbackPresentation_hom_isIso (f : T ⟶ S) :
    IsIso (directImageIsoPullbackPresentation f).hom := sorry

/-- The lower-shriek functor on big étale sheaves. -/
abbrev lowerShriek (f : T ⟶ S) :
    Sheaf (T.overGrothendieckTopology @Etale) (Type (u + 1)) ⥤
      Sheaf (S.overGrothendieckTopology @Etale) (Type (u + 1)) :=
  (map f).sheafPullback (Type (u + 1))
    (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- The lower shriek is a left adjoint. -/
theorem lowerShriek_isLeftAdjoint (f : T ⟶ S) :
    (lowerShriek f).IsLeftAdjoint := sorry

/-- The canonical lower-shriek/inverse-image adjunction. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S) :
    lowerShriek f ⊣ inverseImage f :=
  (map f).sheafAdjunctionContinuous (Type (u + 1))
    (T.overGrothendieckTopology @Etale) (S.overGrothendieckTopology @Etale)

/-- The lower-shriek adjunction with the inverse-image projection of the bundled morphism. -/
noncomputable def lowerShriekAdjunction_via_morphism (f : T ⟶ S) :
    lowerShriek f ⊣ (morphismOfTopoi f)⁻¹ :=
  (lowerShriekAdjunction f).ofNatIsoRight
    (eqToIso (morphismOfTopoi_inverseImage f)).symm

/-- Lower shriek on big étale sheaves preserves pullbacks. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) :=
  (PreservesFiniteConnectedLimits.Pullbacks.iff_equalizers
    (F := lowerShriek f)).mp inferInstance |>.1

/-- Lower shriek on big étale sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) :=
  (PreservesFiniteConnectedLimits.Pullbacks.iff_equalizers
    (F := lowerShriek f)).mp inferInstance |>.2

/-- The big étale inverse image is a right adjoint. -/
theorem inverseImage_isRightAdjoint (f : T ⟶ S) :
    (inverseImage f).IsRightAdjoint := sorry

end Big
end Etale
end Scheme
end AlgebraicGeometry
