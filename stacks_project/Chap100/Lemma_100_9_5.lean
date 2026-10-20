/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
import StacksCheckRecall

/-!
# Immersions of algebraic stacks are monomorphisms

An immersion of algebraic stacks is a monomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 100.9.5: an immersion of algebraic stacks is a monomorphism. -/
@[stacks 0504]
#check (AlgebraicGeometry.Groupoids.Hom.Immersion.mono :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.GroupoidsOver S}
    {f : X ⟶ Y}, [AlgebraicGeometry.Groupoids.Hom.Immersion f] →
      AlgebraicGeometry.Groupoids.Hom.Mono f)
