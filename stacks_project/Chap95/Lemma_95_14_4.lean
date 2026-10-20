/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SheafTorsor.Relative.Stack
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}} {ℬ : Sheaf (Scheme.fppfTopology.over S) (Type u)}

/- Lemma 95.14.4
The relative torsor projection is a stack in groupoids with essentially small
fibers, permitting the small replacement of Remark 8.4.9.
-/
@[stacks 04UM] #check (AlgebraicGeometry.SheafTorsorsOver.isStackWithSmallFibers :
  ∀ (𝒢 : Grp (Over ℬ)),
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (AlgebraicGeometry.SheafTorsorsOver.forget 𝒢) ∧
    ∀ U : Over S, ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((AlgebraicGeometry.SheafTorsorsOver.forget 𝒢).Fiber U)))
