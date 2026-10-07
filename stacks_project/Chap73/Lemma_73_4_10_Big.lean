module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap73.Lemma_73_4_7_Relocalization

/-!
# Big étale sheaf functors on algebraic spaces

This leaf packages the slice-site functors associated with a morphism of
algebraic spaces on the big étale topology. The underlying functors are the
canonical postcomposition and pullback functors on over-categories.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry
namespace AlgebraicSpace
namespace Etale
namespace Big

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Postcomposition on the big étale slice categories. -/
abbrev map (f : Y ⟶ X) : Over Y ⥤ Over X :=
  Over.map f

/-- Pullback on the big étale slice categories. -/
abbrev pullback (f : Y ⟶ X) : Over X ⥤ Over Y :=
  Over.pullback f

/-- The canonical postcomposition-pullback adjunction on big étale slices. -/
abbrev mapPullbackAdjunction (f : Y ⟶ X) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Postcomposition admits left Kan extensions of type-valued presheaves on the
source slice. -/
instance map_op_hasLeftKanExtension (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasLeftKanExtension P := sorry

/-- Postcomposition admits pointwise right Kan extensions of type-valued
presheaves on the source slice. -/
instance map_op_hasPointwiseRightKanExtension (f : Y ⟶ X)
    (P : (Over Y)ᵒᵖ ⥤ Type (u + 1)) :
    (map f).op.HasPointwiseRightKanExtension P := sorry

/-- The inverse-image functor on big étale sheaves. -/
abbrev inverseImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology Y) (Type (u + 1)) :=
  (map f).sheafPushforwardContinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Inverse image is computed by evaluation on the postcomposed slice object. -/
theorem inverseImage_obj_obj (f : Y ⟶ X)
    (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y) :
    (((inverseImage f).obj G).obj.obj (op U)) =
      G.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso (f : Y ⟶ X)
    (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y) :
    (((inverseImage f).obj G).obj.obj (op U)) ≅
      G.obj.obj (op ((map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (map f) (Type (u + 1)) G U

/-- The direct-image functor on big étale sheaves, presented by postcomposition. -/
abbrev directImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (map f).sheafPushforwardCocontinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- The direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def directImage_objObjIso (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X) :
    (((directImage f).obj F).obj.obj (op U)) ≅
      F.obj.obj (op ((pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f) F U

/-- The direct-image functor presented by the continuous pullback right adjoint. -/
abbrev continuousDirectImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (pullback f).sheafPushforwardContinuous (Type (u + 1))
    (overEtaleTopology X) (overEtaleTopology Y)

/-- The continuous direct image is computed by evaluation on the pullback slice
object. -/
theorem continuousDirectImage_obj_obj (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X) :
    (((continuousDirectImage f).obj F).obj.obj (op U)) =
      F.obj.obj (op ((pullback f).obj U)) := sorry

/-- The postcomposition and pullback presentations of direct image are
canonically isomorphic. -/
noncomputable def directImageIsoPullbackPresentation (f : Y ⟶ X) :
    directImage f ≅ continuousDirectImage f :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f)).symm

/-- Inverse image of big étale sheaves preserves finite limits. -/
instance inverseImage_preservesFiniteLimits (f : Y ⟶ X) :
    PreservesFiniteLimits (inverseImage f) := sorry

/-- The bundled morphism of topoi presented by big étale postcomposition. -/
noncomputable def morphismOfTopoi (f : Y ⟶ X) :
    MorphismOfTopoiIn (overEtaleTopology X) (overEtaleTopology Y) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (overEtaleTopology Y) (overEtaleTopology X)

/-- The inverse-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : Y ⟶ X) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : Y ⟶ X) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- The bundled inverse-image computation on every big étale slice object. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso (f : Y ⟶ X)
    (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y) :
    (((morphismOfTopoi f)⁻¹).obj G).obj.obj (op U) ≅
      G.obj.obj (op ((map f).obj U)) :=
  inverseImage_objObjIso f G U

/-- The bundled direct-image computation on every big étale slice object. -/
noncomputable def morphismOfTopoi_pushforward_objObjIso (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X) :
    (((morphismOfTopoi f).pushforward.obj F).obj.obj (op U)) ≅
      F.obj.obj (op ((pullback f).obj U)) :=
  directImage_objObjIso f F U

/-- The lower-shriek functor on big étale sheaves. -/
abbrev lowerShriek (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (map f).sheafPullback (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- The canonical lower-shriek/inverse-image adjunction on big étale sheaves. -/
noncomputable def lowerShriekAdjunction (f : Y ⟶ X) :
    lowerShriek f ⊣ inverseImage f :=
  (map f).sheafAdjunctionContinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Lower shriek on big étale sheaves preserves pullbacks. -/
theorem lowerShriek_preservesPullbacks (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- Lower shriek on big étale sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

end Big
end Etale
end AlgebraicSpace
end AlgebraicGeometry
