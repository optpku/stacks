/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty.Fppf
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 101.27.9: A base-change-stable property of algebraic-space morphisms
that is fppf local on the target holds for a representable morphism of algebraic
stacks if and only if it holds for its base change along a surjective, flat,
locally of finite presentation morphism of algebraic stacks. -/
@[stacks 0CPP]
#check (AlgebraicGeometry.AlgebraicStack.has_iff_of_twoFibreProduct_snd :
  ∀ {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    (f : X ⟶ Y) (hf : relativelyRepresentableByAlgebraicSpaces f) (g : Z ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g],
    Groupoids.Hom.has P f ↔
      Groupoids.Hom.has P (TwoFibreProduct.snd.{u + 1, u, u + 1, u} f g))
