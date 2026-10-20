/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Additive
public import ReasLib.Topology.Category.TopCat.DiagramOpens.SimplicialMap
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Constant

/-!
# Augmentation pushforward of abelian sheaves

The composite abelian direct image `a_*` along an augmentation `a : Y ⟶ constSpace X`,
and its right derived functors `R^n a_*`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor TopCat

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ AddCommGrpCat.{u},
    (constProjection X).op.HasPointwiseRightKanExtension F]

/-- Additivity of cocontinuous direct image along the degree-forgetting projection. -/
instance constProjection_sheafPushforwardCocontinuous_additive :
    ((constProjection X).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)).Additive :=
  sorry

/-- The abelian direct image `a_*` of an augmentation, as the composite of continuous
pushforward along `zariskiMap a` with cocontinuous pushforward along `constProjection X`. -/
def augmentationPushforward :
    Sheaf (zariskiTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (zariskiMap a).sheafPushforwardContinuous AddCommGrpCat.{u}
      (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
    (constProjection X).sheafPushforwardCocontinuous AddCommGrpCat.{u}
      (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X)

/-- `augmentationPushforward a` factors as `zariskiMap a` then `constProjection X`. -/
theorem augmentationPushforward_comp :
    augmentationPushforward a =
      (zariskiMap a).sheafPushforwardContinuous AddCommGrpCat.{u}
          (zariskiTopology (constSpace X)) (zariskiTopology Y) ⋙
        (constProjection X).sheafPushforwardCocontinuous AddCommGrpCat.{u}
          (zariskiTopology (constSpace X)) (Opens.grothendieckTopology X) :=
  rfl

/-- Additivity of the abelian augmentation pushforward. -/
instance augmentationPushforward_additive : (augmentationPushforward a).Additive :=
  sorry

variable [HasInjectiveResolutions (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]

/-- The degree-`n` higher direct image functor `R^n a_*` of an augmentation. -/
abbrev augmentationHigherDirectImageFunctor (n : ℕ) :
    Sheaf (zariskiTopology Y) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (augmentationPushforward a).rightDerived n

/-- The degree-`n` higher direct image `R^n a_* F` of an abelian sheaf along an
augmentation. -/
abbrev augmentationHigherDirectImage (F : Sheaf (zariskiTopology Y) AddCommGrpCat.{u})
    (n : ℕ) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (augmentationHigherDirectImageFunctor a n).obj F

/-- In degree zero, the higher direct image functor is the right derived functor of
`augmentationPushforward a`. -/
theorem augmentationHigherDirectImageFunctor_zero :
    augmentationHigherDirectImageFunctor a 0 = (augmentationPushforward a).rightDerived 0 :=
  rfl

end CategoryTheory.SimplicialObject
