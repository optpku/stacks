/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Pushforward

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite TopologicalSpace TopCat

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

variable [HasSheafify (zariskiTopology Y) AddCommGrpCat.{u}]
variable [HasSheafify (zariskiTopology (constSpace X)) AddCommGrpCat.{u}]
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [∀ F : (zariskiSite (constSpace X))ᵒᵖ ⥤ AddCommGrpCat.{u},
    (constProjection X).op.HasPointwiseRightKanExtension F]

/- Abelian pushforward along an augmentation and its higher direct images. -/
#check (CategoryTheory.SimplicialObject.augmentationPushforward a :
  Sheaf (zariskiTopology Y) AddCommGrpCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

variable [HasInjectiveResolutions (Sheaf (zariskiTopology Y) AddCommGrpCat.{u})]

#check (CategoryTheory.SimplicialObject.augmentationHigherDirectImageFunctor a :
  ℕ → Sheaf (zariskiTopology Y) AddCommGrpCat.{u} ⥤
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

end CategoryTheory.SimplicialObject
