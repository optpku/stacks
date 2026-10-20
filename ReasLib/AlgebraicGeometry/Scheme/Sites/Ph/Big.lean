/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
public import ReasLib.CategoryTheory.Sites.Topos.ContinuousRightAdjoint.Computations

/-!
# Big ph sheaf functors

This leaf packages the slice-site functors associated with a morphism of
schemes on the big ph topology. The underlying functors are the canonical
postcomposition and pullback functors on over-categories.
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
namespace Ph
namespace Big

variable {S T : Scheme.{u}}

/-- Postcomposition on the big ph slice categories. -/
abbrev map (f : T ⟶ S) : Over T ⥤ Over S :=
  Over.map f

/-- Pullback on the big ph slice categories. -/
abbrev pullback (f : T ⟶ S) : Over S ⥤ Over T :=
  Over.pullback f

/-- Postcomposition is cocontinuous for the big ph slice topologies. -/
instance map_isCocontinuous (f : T ⟶ S) :
    Functor.IsCocontinuous (map f) (Scheme.bigPhSite T) (Scheme.bigPhSite S) := sorry

/-- Postcomposition is continuous for the big ph slice topologies. -/
instance map_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (map f) (Scheme.bigPhSite T) (Scheme.bigPhSite S) := sorry

/-- The canonical postcomposition-pullback adjunction on big ph slices. -/
abbrev mapPullbackAdjunction (f : T ⟶ S) :
    map f ⊣ pullback f :=
  Over.mapPullbackAdj f

/-- Pullback is continuous for the big ph slice topologies. -/
instance pullback_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (pullback f) (Scheme.bigPhSite S) (Scheme.bigPhSite T) := sorry

/-- The inverse-image functor on big ph sheaves. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (Scheme.bigPhSite S) (Type (u + 1)) ⥤
      Sheaf (Scheme.bigPhSite T) (Type (u + 1)) :=
  (map f).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.bigPhSite T) (Scheme.bigPhSite S)

/-- Inverse image is computed by evaluation on the postcomposed slice object. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S) (G : Sheaf (Scheme.bigPhSite S) (Type (u + 1))) (U : Over T) :
    (((inverseImage f).obj G).obj.obj (op U)) =
      G.obj.obj (op ((map f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S) (G : Sheaf (Scheme.bigPhSite S) (Type (u + 1))) (U : Over T) :
    (((inverseImage f).obj G).obj.obj (op U)) ≅
      G.obj.obj (op ((map f).obj U)) :=
  Functor.sheafPushforwardContinuousObjObjIso (map f) (Type (u + 1)) G U

/-- The direct-image functor on big ph sheaves, presented by postcomposition. -/
abbrev directImage (f : T ⟶ S) :
    Sheaf (Scheme.bigPhSite T) (Type (u + 1)) ⥤
      Sheaf (Scheme.bigPhSite S) (Type (u + 1)) :=
  (map f).sheafPushforwardCocontinuous (Type (u + 1))
    (Scheme.bigPhSite T) (Scheme.bigPhSite S)

/-- Direct image is computed by evaluation on the pullback slice object. -/
theorem directImage_obj_obj
    (f : T ⟶ S) (F : Sheaf (Scheme.bigPhSite T) (Type (u + 1))) (U : Over S) :
    (((directImage f).obj F).obj.obj (op U)) =
      F.obj.obj (op ((pullback f).obj U)) := sorry

/-- The direct-image computation as a canonical objectwise isomorphism. -/
noncomputable def directImage_objObjIso
    (f : T ⟶ S) (F : Sheaf (Scheme.bigPhSite T) (Type (u + 1))) (U : Over S) :
    (((directImage f).obj F).obj.obj (op U)) ≅
      F.obj.obj (op ((pullback f).obj U)) :=
  Functor.ContinuousRightAdjoint.pushforwardCocontinuousObjObjIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f) F U

/-- The direct-image functor presented by the continuous pullback right adjoint. -/
abbrev continuousDirectImage (f : T ⟶ S) :
    Sheaf (Scheme.bigPhSite T) (Type (u + 1)) ⥤
      Sheaf (Scheme.bigPhSite S) (Type (u + 1)) :=
  (pullback f).sheafPushforwardContinuous (Type (u + 1))
    (Scheme.bigPhSite S) (Scheme.bigPhSite T)

/-- The postcomposition and pullback presentations of direct image are canonically isomorphic. -/
noncomputable def directImageIsoPullbackPresentation (f : T ⟶ S) :
    directImage f ≅ continuousDirectImage f :=
  (Functor.ContinuousRightAdjoint.pushforwardContinuousIso
    (map f) (pullback f) (Type (u + 1)) (mapPullbackAdjunction f)).symm

/-- The bundled morphism of topoi presented by big ph postcomposition. -/
noncomputable def morphismOfTopoi (f : T ⟶ S) :
    MorphismOfTopoiIn (Scheme.bigPhSite S) (Scheme.bigPhSite T) where
  inverseImageFunctor :=
    LeftExactFunctor.of (inverseImage f)
  pushforward := directImage f
  adjunction :=
    (map f).sheafAdjunctionCocontinuous (Type (u + 1))
      (Scheme.bigPhSite T) (Scheme.bigPhSite S)

/-- The inverse-image projection of the bundled big ph morphism. -/
@[simp]
theorem morphismOfTopoi_inverseImage (f : T ⟶ S) :
    (morphismOfTopoi f)⁻¹ = inverseImage f := sorry

/-- The direct-image projection of the bundled big ph morphism. -/
@[simp]
theorem morphismOfTopoi_pushforward (f : T ⟶ S) :
    (morphismOfTopoi f).pushforward = directImage f := sorry

/-- Big ph morphisms of topoi compose along composition of scheme morphisms. -/
theorem morphismOfTopoi_comp
    {R S T : Scheme.{u}} (f : R ⟶ S) (g : S ⟶ T) :
    MorphismOfTopoiIn.comp (morphismOfTopoi g) (morphismOfTopoi f) =
      morphismOfTopoi (f ≫ g) := sorry

/-- The lower-shriek functor on big ph sheaves. -/
abbrev lowerShriek (f : T ⟶ S) :
    Sheaf (Scheme.bigPhSite T) (Type (u + 1)) ⥤
      Sheaf (Scheme.bigPhSite S) (Type (u + 1)) :=
  (map f).sheafPullback (Type (u + 1))
    (Scheme.bigPhSite T) (Scheme.bigPhSite S)

/-- The canonical lower-shriek/inverse-image adjunction on big ph sheaves. -/
noncomputable def lowerShriekAdjunction (f : T ⟶ S) :
    lowerShriek f ⊣ inverseImage f :=
  (map f).sheafAdjunctionContinuous (Type (u + 1))
    (Scheme.bigPhSite T) (Scheme.bigPhSite S)

/-- Lower shriek on big ph sheaves preserves pullbacks. -/
theorem lowerShriek_preservesPullbacks (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingCospan (lowerShriek f) := sorry

/-- Lower shriek on big ph sheaves preserves equalizers. -/
theorem lowerShriek_preservesEqualizers (f : T ⟶ S) :
    PreservesLimitsOfShape WalkingParallelPair (lowerShriek f) := sorry

end Big
end Ph
end Scheme
end AlgebraicGeometry
