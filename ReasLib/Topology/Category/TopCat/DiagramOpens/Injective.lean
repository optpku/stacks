/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Component
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/-- Restriction of abelian sheaves from the diagram-open site of a simplicial
space to any component preserves injective objects. -/
instance sheafComponent_preservesInjectiveObjects
    (X : SimplicialObject TopCat.{u}) (n : ℕ) :
    (sheafComponent X n AddCommGrpCat.{u}).PreservesInjectiveObjects :=
  sorry

end CategoryTheory.SimplicialObject
