/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 100.9.1 (1): a morphism of algebraic stacks is called an open
immersion if it is representable, and an open immersion in the sense of
Section 100.3. -/
@[stacks 04YL] #check (AlgebraicGeometry.Groupoids.Hom.OpenImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

/- Definition 100.9.1 (2): a morphism of algebraic stacks is called a closed
immersion if it is representable, and a closed immersion in the sense of
Section 100.3. -/
@[stacks 04YL] #check (AlgebraicGeometry.Groupoids.Hom.ClosedImmersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)

/- Definition 100.9.1 (3): a morphism of algebraic stacks is called an
immersion if it is representable, and an immersion in the sense of
Section 100.3. -/
@[stacks 04YL] #check (AlgebraicGeometry.Groupoids.Hom.Immersion :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}, (X ⟶ Y) → Prop)
