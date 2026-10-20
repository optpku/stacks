/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pullback

/-!
# Small-to-big pro-étale relocalization

This leaf owns the reusable site and sheaf API for the functor which sends a
weakly étale scheme over `T` to the same scheme over `S` along `f : T ⟶ S`.
-/

@[expose] public section

open CategoryTheory
open Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme
namespace ProEt
namespace SmallToBig

variable {S T : Scheme.{u}}

/-- The relocalization functor from the small pro-étale site of `T` to the big
pro-étale slice site over `S`. -/
abbrev relocalizationFunctor (f : T ⟶ S) : T.ProEt ⥤ Over S :=
  ProEt.forget T ⋙ Over.map f

/-- The relocalization functor is continuous for the small-to-big pro-étale
topologies. -/
instance relocalizationFunctor_isContinuous (f : T ⟶ S) :
    Functor.IsContinuous (relocalizationFunctor f) (ProEt.topology T)
      (proetaleTopology.{u}.over S) :=
  Functor.isContinuous_comp (ProEt.forget T) (Over.map f)
    (ProEt.topology T) (proetaleTopology.{u}.over T) (proetaleTopology.{u}.over S)

/-- The inverse-image functor on sheaves induced by pro-étale relocalization. -/
abbrev inverseImage (f : T ⟶ S) :
    Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology T) (Type (u + 1)) :=
  (relocalizationFunctor f).sheafPushforwardContinuous (Type (u + 1))
    (ProEt.topology T) (proetaleTopology.{u}.over S)

/-- The inverse image is computed by evaluating on the same scheme viewed over
`S`. -/
theorem inverseImage_obj_obj
    (f : T ⟶ S)
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))) (U : T.ProEt) :
    ((inverseImage f).obj 𝒢).1.obj (op U) =
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) := sorry

/-- The inverse-image computation as a canonical objectwise isomorphism. -/
noncomputable def inverseImage_objObjIso
    (f : T ⟶ S)
    (𝒢 : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))) (U : T.ProEt) :
    ((inverseImage f).obj 𝒢).1.obj (op U) ≅
      𝒢.1.obj (op ((relocalizationFunctor f).obj U)) :=
  ((relocalizationFunctor f).sheafPushforwardContinuousCompSheafToPresheafIso
    (Type (u + 1)) (ProEt.topology T) (proetaleTopology.{u}.over S)).app 𝒢 |>.app (op U)

/-- Restriction of sheaves from the big pro-étale site of `S` to the small
pro-étale site, given by continuous sheaf pushforward along `ProEt.forget S`. -/
abbrev restrictToSmall (S : Scheme.{u}) :
    Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology S) (Type (u + 1)) :=
  (ProEt.forget S).sheafPushforwardContinuous (Type (u + 1))
    (ProEt.topology S) (proetaleTopology.{u}.over S)

/-- Restriction to the small pro-étale site evaluates a sheaf on the underlying
object of `S.ProEt`. -/
theorem restrictToSmall_obj_obj (S : Scheme.{u})
    (F : Sheaf (proetaleTopology.{u}.over S) (Type (u + 1))) (U : S.ProEt) :
    ((restrictToSmall S).obj F).1.obj (op U) =
      F.1.obj (op ((ProEt.forget S).obj U)) := sorry

/-- Direct image of sheaves on big pro-étale sites along `f : T ⟶ S`, given by
continuous sheaf pushforward along `Over.pullback f`. -/
abbrev bigPushforward {S T : Scheme.{u}} (f : T ⟶ S) :
    Sheaf (proetaleTopology.{u}.over T) (Type (u + 1)) ⥤
      Sheaf (proetaleTopology.{u}.over S) (Type (u + 1)) :=
  (Over.pullback f).sheafPushforwardContinuous (Type (u + 1))
    (proetaleTopology.{u}.over S) (proetaleTopology.{u}.over T)

/-- The big pro-étale direct image evaluates a sheaf on the base change
`U ×_S T`. -/
theorem bigPushforward_obj_obj {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf (proetaleTopology.{u}.over T) (Type (u + 1))) (U : Over S) :
    ((bigPushforward f).obj F).1.obj (op U) =
      F.1.obj (op ((Over.pullback f).obj U)) := sorry

/-- Direct image of sheaves on small pro-étale sites along `f : T ⟶ S`, given by
continuous sheaf pushforward along `smallProetalePullback f`. -/
abbrev smallPushforward {S T : Scheme.{u}} (f : T ⟶ S) :
    Sheaf (ProEt.topology T) (Type (u + 1)) ⥤
      Sheaf (ProEt.topology S) (Type (u + 1)) :=
  (smallProetalePullback f).sheafPushforwardContinuous (Type (u + 1))
    (ProEt.topology S) (ProEt.topology T)

/-- The small pro-étale direct image evaluates a sheaf on the base change
`U ×_S T`. -/
theorem smallPushforward_obj_obj {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf (ProEt.topology T) (Type (u + 1))) (U : S.ProEt) :
    ((smallPushforward f).obj F).1.obj (op U) =
      F.1.obj (op ((smallProetalePullback f).obj U)) := sorry

/-- Restricting the big pro-étale direct image of a sheaf to the small
pro-étale site equals the small pro-étale direct image of its restriction. -/
theorem bigToSmall_pushforward_eq
    {S T : Scheme.{u}} (f : T ⟶ S)
    (F : Sheaf (proetaleTopology.{u}.over T) (Type (u + 1))) :
    (restrictToSmall S).obj ((bigPushforward f).obj F) =
      (smallPushforward f).obj ((restrictToSmall T).obj F) := sorry

end SmallToBig
end ProEt
end AlgebraicGeometry.Scheme
