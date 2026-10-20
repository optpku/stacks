/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SheafTorsor.Stack
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S : Scheme.{u}}

/- Lemma 95.14.2
The projection from torsors under an fppf sheaf of groups is a stack in groupoids,
with essentially small fibers permitting replacement by a small model.
-/
@[stacks 04UK] #check (AlgebraicGeometry.SheafTorsors.isStackWithSmallFibers :
  ∀ (𝒢 : Sheaf (Scheme.fppfTopology.over S) GrpCat.{u}),
    IsStack.InGroupoids (Scheme.fppfTopology.over S)
      (AlgebraicGeometry.SheafTorsors.forget 𝒢) ∧
    ∀ U : Over S, ObjectProperty.EssentiallySmall.{u}
      (⊤ : ObjectProperty ((AlgebraicGeometry.SheafTorsors.forget 𝒢).Fiber U)))
