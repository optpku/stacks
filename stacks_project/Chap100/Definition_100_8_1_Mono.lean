/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
public import stacks_project.Chap94.Definition_94_12_1_Representable

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.Groupoids.Hom.Mono :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S},
    (X ⟶ Y) → Prop)
