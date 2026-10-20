/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Monomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 100.8.1: a morphism `f : X ⟶ Y` of algebraic stacks is a
monomorphism if it is representable by algebraic spaces and a monomorphism
in the sense of Section 100.3. -/
@[stacks 04ZW] #check (AlgebraicGeometry.Groupoids.Hom.Mono :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S},
    (X ⟶ Y) → Prop)
