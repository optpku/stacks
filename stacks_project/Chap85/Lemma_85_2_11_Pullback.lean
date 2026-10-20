/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaves.Simplicial.Augmentation.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite TopologicalSpace TopCat

universe u

namespace CategoryTheory.SimplicialObject

variable {Y : SimplicialObject TopCat.{u}} {X : TopCat.{u}} (a : Y ⟶ constSpace X)

/- The open preimage of an augmentation and restriction of abelian sheaves to it. -/
#check (CategoryTheory.SimplicialObject.augmentationPreimage a :
  Opens X → SimplicialObject TopCat.{u})
#check (CategoryTheory.SimplicialObject.restrictAugmentationPreimage a :
  (V : Opens X) → Sheaf (zariskiTopology Y) AddCommGrpCat.{u} ⥤
    Sheaf (zariskiTopology (augmentationPreimage a V)) AddCommGrpCat.{u})

end CategoryTheory.SimplicialObject
