/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Bicategory
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence of scheme-theoretic images of algebraic stacks

A morphism has a scheme-theoretic image when it admits a factorization through
an algebraic stack satisfying the scheme-theoretic image universal property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks has a scheme-theoretic image if it admits
a scheme-theoretic image factorization through an algebraic stack. -/
def HasSchemeTheoreticImage {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop :=
  ∃ (Z : AlgebraicStacks S) (toImage : X ⟶ Z.toGroupoids)
    (ι : Z.toGroupoids ⟶ Y), IsSchemeTheoreticImage f toImage ι

/-- Existence of a scheme-theoretic image is equivalent to existence of an
algebraic-stack carrier and morphisms satisfying its universal property. -/
theorem HasSchemeTheoreticImage.iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSchemeTheoreticImage f ↔
      ∃ (Z : AlgebraicStacks S) (toImage : X ⟶ Z.toGroupoids)
        (ι : Z.toGroupoids ⟶ Y), IsSchemeTheoreticImage f toImage ι :=
  Iff.rfl

/-- Every morphism of algebraic stacks has a scheme-theoretic image. -/
@[stacks 0CPU]
theorem hasSchemeTheoreticImage {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSchemeTheoreticImage f :=
  sorry

end AlgebraicGeometry.AlgebraicStack
