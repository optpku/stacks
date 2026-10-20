/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreserving
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap97.«97_5_0_1_Restrict»

/-!
# Limit-preserving categories fibred in groupoids

The canonical cocone of fibre Hom-types for restrictions along an inverse system.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

#check (AlgebraicGeometry.Groupoids.homCocone :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} (c : Cone D) {i : I} (x y : X.p.Fiber (D.obj i)),
    Cocone (AlgebraicGeometry.Groupoids.homFunctor x y))
