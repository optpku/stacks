/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty
import StacksCheckRecall

/-!
# Scheme tests versus algebraic-space tests for representable morphisms

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on algebraic-space base changes of a
morphism of algebraic stacks representable by algebraic spaces, not only on
scheme base changes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 100.3.2: A morphism of algebraic stacks representable by algebraic
spaces has a base-change stable, fppf target-local property if and only if
every algebraic-space base-change projection has that property. -/
@[stacks 04XC] #check (AlgebraicGeometry.Groupoids.Hom.has_iff_forall_algebraicSpace :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f),
    AlgebraicGeometry.Groupoids.Hom.has P f ↔
      ∀ (Z : AlgebraicSpace S) (z : Z.toGroupoids ⟶ Y) (W : AlgebraicSpace S)
        (w : W ⟶ Z), RepresentsTwoFibreProductOnSpace f z W Z w → P w)
