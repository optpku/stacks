/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big fppf sheaf functors

This leaf packages the slice-site functors associated with a morphism of
schemes on the big fppf topology.  The underlying functors are the canonical
`Over.map` and `Over.pullback` constructions; the declarations here provide a
stable sheaf-level surface and objectwise computation API for applications.
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
namespace Fppf
namespace Big

variable {S T : Scheme.{u}}

/-- Postcomposition on the big fppf slice categories. -/
abbrev map (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Pullback on the big fppf slice categories. -/
abbrev pullback (f : T ⟶ S) : Over S ⥤ Over T :=
  Over.pullback f

/-- The postcomposition functor is cocontinuous for the big fppf slice topologies. -/
instance map_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (map f)
      (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S) := sorry

/-- The postcomposition functor is continuous for the big fppf slice topologies. -/
instance map_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (map f)
      (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S) := sorry

/-- The canonical postcomposition-pullback adjunction on big fppf slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Pullback is continuous for the big fppf slice topologies. -/
instance pullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (pullback f)
      (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T) := sorry

/-- The postcomposition presentation has the left-Kan-extension hypotheses used by
the sheaf-level lower-shriek construction. -/
instance map_op_hasLeftKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- The postcomposition presentation has the pointwise right-Kan-extension hypotheses used by
the sheaf-level direct-image construction. -/
instance map_op_hasPointwiseRightKanExtension
    (f : T ⟶ S) (P : (Over T)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on sheaves induced by big fppf postcomposition. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) :=
  (map f).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The inverse-image functor is computed by evaluating on the postcomposed slice object. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) =
      𝒢.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) (U : Over T) :
    (((inverseImage f).obj 𝒢).obj.obj (op U)) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (map f) (Type (u + 1)) 𝒢 U

/-- The inverse-image objectwise comparison is an isomorphism. -/
theorem inverseImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) (U : Over T) :
    IsIso ((inverseImage_objObjIso f 𝒢 U).hom) := sorry

/-- The inverse-image objectwise comparison is natural in the slice object. -/
theorem inverseImage_objObjIso_naturality
    (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
    {U V : Over T} (φ : U ⟶ V) :
    (inverseImage_objObjIso f 𝒢 V).hom ≫
        𝒢.obj.map ((map f).map φ).op =
      ((inverseImage f).obj 𝒢).obj.map φ.op ≫
        (inverseImage_objObjIso f 𝒢 U).hom := sorry

/-- The direct-image functor on sheaves induced by big fppf postcomposition. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (map f).sheafPushforwardCocontinuous (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The direct image is objectwise identified with evaluation on the pullback slice object. -/
noncomputable def directImage_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    (((directImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f) ℱ U

/-- The direct-image objectwise comparison is an isomorphism. -/
theorem directImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    IsIso ((directImage_objObjIso f ℱ U).hom) := sorry

/-- The direct-image objectwise comparison is natural in the object of the big fppf slice. -/
theorem directImage_objObjIso_naturality
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)))
    {U V : Over S} (φ : U ⟶ V) :
    (directImage_objObjIso f ℱ V).hom ≫
        ℱ.obj.map ((pullback f).map φ).op =
      ((directImage f).obj ℱ).obj.map φ.op ≫
        (directImage_objObjIso f ℱ U).hom := sorry

/-- The direct-image functor presented by the continuous pullback right adjoint. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (pullback f).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T)

/-- The continuous direct image is computed by evaluation on the pullback slice object. -/
theorem continuousDirectImage_obj_obj
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) =
      ℱ.obj.obj (op ((pullback f).obj U)) := sorry

/-- The continuous direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def continuousDirectImage_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    (((continuousDirectImage f).obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (pullback f) (Type (u + 1)) ℱ U

/-- The continuous direct-image objectwise comparison is an isomorphism. -/
theorem continuousDirectImage_objObjIso_hom_isIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    IsIso ((continuousDirectImage_objObjIso f ℱ U).hom) := sorry

/-- The continuous direct-image objectwise comparison is natural in the slice object. -/
theorem continuousDirectImage_objObjIso_naturality
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)))
    {U V : Over S} (φ : U ⟶ V) :
    (continuousDirectImage_objObjIso f ℱ V).hom ≫
        ℱ.obj.map ((pullback f).map φ).op =
      ((continuousDirectImage f).obj ℱ).obj.map φ.op ≫
        (continuousDirectImage_objObjIso f ℱ U).hom := sorry

/-- The cocontinuous direct image is canonically identified with the continuous right-adjoint
presentation. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage f ≅ continuousDirectImage f :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f)).symm

/-- The direct-image presentation comparison is an isomorphism on its hom component. -/
theorem directImageIsoPullbackPresentation_hom_isIso (f : T ⟶ S) :
    IsIso (directImageIsoPullbackPresentation f).hom := sorry

/-- The bundled morphism of topoi presented by big fppf postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (Scheme.fppfTopology.over S) (Scheme.fppfTopology.over T) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The inverse-image projection of the bundled big fppf morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big fppf morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- The inverse-image computation through the bundled big fppf morphism. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso
    (f : T ⟶ S)
    (𝒢 : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1))) (U : Over T) :
    (((morphismOfTopoi f)⁻¹).obj 𝒢).obj.obj (op U) ≅
      𝒢.obj.obj (op ((map f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj 𝒢).obj.obj (op U))
    (morphismOfTopoi_inverseImage f)) ≪≫ inverseImage_objObjIso f 𝒢 U

/-- The direct-image computation through the bundled big fppf morphism. -/
noncomputable def morphismOfTopoi_pushforward_objObjIso
    (f : T ⟶ S)
    (ℱ : Sheaf (Scheme.fppfTopology.over T) (Type (u + 1))) (U : Over S) :
    (((morphismOfTopoi f).pushforward.obj ℱ).obj.obj (op U)) ≅
      ℱ.obj.obj (op ((pullback f).obj U)) :=
  eqToIso (congrArg (fun F => (F.obj ℱ).obj.obj (op U))
    (morphismOfTopoi_pushforward f)) ≪≫ directImage_objObjIso f ℱ U

/-- The bundled direct image is identified with the continuous pullback presentation. -/
noncomputable def morphismOfTopoi_pushforwardIsoPullbackPresentation (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward ≅ continuousDirectImage f :=
  eqToIso (morphismOfTopoi_pushforward f) ≪≫ directImageIsoPullbackPresentation f

/-- Big fppf morphisms of topoi compose along composition of scheme morphisms. -/
theorem morphismOfTopoi_comp
    {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

/-- The lower-shriek functor on big fppf sheaves. -/
abbrev lowerShriek (f : T ⟶ S) :
    Sheaf (Scheme.fppfTopology.over T) (Type (u + 1)) ⥤
      Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  (map f).sheafPullback (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The canonical lower-shriek/inverse-image adjunction on big fppf sheaves. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S) :
    lowerShriek f ⊣ inverseImage f :=
  (map f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.fppfTopology.over T) (Scheme.fppfTopology.over S)

/-- The lower-shriek functor on big fppf sheaves preserves pullbacks. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- The lower-shriek functor on big fppf sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

/-- The big fppf inverse image is a right adjoint. -/
theorem inverseImage_isRightAdjoint (f : T ⟶ S) :
    (inverseImage f).IsRightAdjoint := sorry

end Big
end Fppf
end Scheme
end AlgebraicGeometry
