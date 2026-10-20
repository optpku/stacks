/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.LocallyInduced.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Pseudofunctor.StrongTrans.Construction
public import ReasLib.CategoryTheory.Fibered.Inertia.Cartesian.Stable.Maps.Construction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stable cartesian-inertia forgetful strong transformation

This leaf owns the strong transformation induced by the stable-universe forgetful map.
-/

@[expose] public section

universe u v vS w

namespace CategoryTheory

open BasedCategory BasedFunctor
open scoped Bicategory

namespace FiberedCategoryOver.Inertia

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- Forgetting the automorphism is a strong transformation from the fibred-inertia
pseudofunctor to the identity pseudofunctor. -/
@[stacks 042H "cartesian inertia forgetful strong transformation"]
def forget.strongTrans :
    Pseudofunctor.StrongTrans
      ((pseudofunctor C) :
        Pseudofunctor
          (FiberedCategoryOver.{u, v, max w vS, vS} C)
          (FiberedCategoryOver.{u, v, max w vS, vS} C))
      (Pseudofunctor.id
        (FiberedCategoryOver.{u, v, max w vS, vS} C)) :=
  Bicategory.LocallyInducedBicategory.StrongTrans.toId
    (objectLift.{u, v, vS, max w vS} C)
    objectLift.map_mem
    (objectLift.forget.strongTrans.{u, v, vS, w} C)
    (objectLift.forget.strongTrans.app_mem.{u, v, vS, w})

end FiberedCategoryOver.Inertia

end CategoryTheory
