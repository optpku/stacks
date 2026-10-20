/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.LeftExact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Big
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big étale sheaf functors on algebraic spaces

A morphism of algebraic spaces induces inverse and direct image functors on
big étale sheaves through postcomposition and pullback on slice categories.
Inverse image also admits a lower-shriek left adjoint.
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

/-- The inverse-image functor on big étale sheaves. -/
abbrev inverseImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology X) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology Y) (Type (u + 1)) :=
  (Over.map f).sheafPushforwardContinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Inverse image is computed by evaluation on the postcomposed slice object. -/
theorem inverseImage_obj_obj (f : Y ⟶ X)
    (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y) :
    (((inverseImage f).obj G).obj.obj (op U)) =
      G.obj.obj (op ((Over.map f).obj U)) := rfl

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso (f : Y ⟶ X)
    (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y) :
    (((inverseImage f).obj G).obj.obj (op U)) ≅
      G.obj.obj (op ((Over.map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (Over.map f) (Type (u + 1)) G U

/-- The direct-image functor on big étale sheaves, presented by postcomposition. -/
abbrev directImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (Over.map f).sheafPushforwardCocontinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- The direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def directImage_objObjIso (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X) :
    (((directImage f).obj F).obj.obj (op U)) ≅
      F.obj.obj (op ((Over.pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (Over.map f) (Over.pullback f) (Type (u + 1)) (Over.mapPullbackAdj f) F U

/-- The direct-image functor presented by the continuous pullback right adjoint. -/
abbrev continuousDirectImage (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
    (overEtaleTopology X) (overEtaleTopology Y)

/-- The continuous direct image is computed by evaluation on the pullback slice
object. -/
theorem continuousDirectImage_obj_obj (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X) :
    (((continuousDirectImage f).obj F).obj.obj (op U)) =
      F.obj.obj (op ((Over.pullback f).obj U)) := rfl

/-- The postcomposition and pullback presentations of direct image are
canonically isomorphic. -/
noncomputable def directImageIsoPullbackPresentation (f : Y ⟶ X) :
    directImage f ≅ continuousDirectImage f :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (Over.map f) (Over.pullback f) (Type (u + 1)) (Over.mapPullbackAdj f)).symm

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
    (Over.map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (overEtaleTopology Y) (overEtaleTopology X)

/-- The inverse-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : Y ⟶ X) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := rfl

/-- The direct-image projection of the bundled big étale morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : Y ⟶ X) :
    (morphismOfTopoi f).pushforward = directImage f := rfl

/-- The bundled inverse-image computation on every big étale slice object. -/
noncomputable def morphismOfTopoi_inverseImage_objObjIso (f : Y ⟶ X)
    (G : Sheaf (overEtaleTopology X) (Type (u + 1))) (U : Over Y) :
    (((morphismOfTopoi f)⁻¹).obj G).obj.obj (op U) ≅
      G.obj.obj (op ((Over.map f).obj U)) :=
  inverseImage_objObjIso f G U

/-- The bundled direct-image computation on every big étale slice object. -/
noncomputable def morphismOfTopoi_pushforward_objObjIso (f : Y ⟶ X)
    (F : Sheaf (overEtaleTopology Y) (Type (u + 1))) (U : Over X) :
    (((morphismOfTopoi f).pushforward.obj F).obj.obj (op U)) ≅
      F.obj.obj (op ((Over.pullback f).obj U)) :=
  directImage_objObjIso f F U

/-- The lower-shriek functor on big étale sheaves. -/
abbrev lowerShriek (f : Y ⟶ X) :
    Sheaf (overEtaleTopology Y) (Type (u + 1)) ⥤
      Sheaf (overEtaleTopology X) (Type (u + 1)) :=
  (Over.map f).sheafPullback (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- The canonical lower-shriek/inverse-image adjunction on big étale sheaves. -/
noncomputable def lowerShriekAdjunction (f : Y ⟶ X) :
    lowerShriek f ⊣ inverseImage f :=
  (Over.map f).sheafAdjunctionContinuous (Type (u + 1))
    (overEtaleTopology Y) (overEtaleTopology X)

/-- Lower shriek on big étale sheaves preserves pullbacks. -/
instance lowerShriek_preservesPullbacks (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- Lower shriek on big étale sheaves preserves equalizers. -/
instance lowerShriek_preservesEqualizers (f : Y ⟶ X) :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

end Big
end Etale
end AlgebraicSpace
end AlgebraicGeometry
