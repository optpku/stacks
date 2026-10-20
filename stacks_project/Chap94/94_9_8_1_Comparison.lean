/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.OnSpace

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- A morphism of algebraic spaces represents the first projection of a 2-fibre
product when representing equivalences identify its projection triangle. -/
#check (AlgebraicGeometry.RepresentsTwoFibreProductOnSpace :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    (f : X ⟶ Y) (g : Z ⟶ Y) (F G : AlgebraicSpace S) (f' : F ⟶ G), Prop)
