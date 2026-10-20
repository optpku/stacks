/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Category.TopCat.DiagramOpens.Injective
import StacksCheckRecall

/-!
# Lemma 85.2.6

Restriction of injective abelian sheaves from `X_Zar` to a degree-`n`
component `X_n`.
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

noncomputable section

universe u

namespace CategoryTheory.SimplicialObject

/- Lemma 85.2.6: restriction of injective abelian sheaves to any component of a
simplicial space preserves injectivity. -/
@[stacks 09W1] #check
  (CategoryTheory.SimplicialObject.sheafComponent_preservesInjectiveObjects :
    ∀ (X : SimplicialObject TopCat.{u}) (n : ℕ),
      (sheafComponent X n AddCommGrpCat.{u}).PreservesInjectiveObjects)

variable (X : SimplicialObject TopCat.{u}) (n : ℕ)
  (I : Sheaf (zariskiTopology X) AddCommGrpCat.{u}) [Injective I]

#check (CategoryTheory.Functor.injective_obj (sheafComponent X n AddCommGrpCat.{u}) I :
  Injective ((sheafComponent X n AddCommGrpCat.{u}).obj I))

end CategoryTheory.SimplicialObject
