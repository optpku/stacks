/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.MorphismProperty
import StacksCheckRecall

/-!
# Testing representable morphisms of algebraic stacks on one fppf covering

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on the algebraic-space projection
of one surjective, flat, locally of finite presentation base change of a
morphism of algebraic stacks representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Groupoids.Hom
open scoped Bicategory

universe u

/- Lemma 100.3.3: A morphism of algebraic stacks representable by algebraic
spaces has a base-change stable, fppf target-local property if and only if its
projection after a surjective, flat, locally of finite presentation
algebraic-space base change has that property. -/
@[stacks 04XD] #check (AlgebraicGeometry.Groupoids.Hom.has_iff_of_covering :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v),
    AlgebraicGeometry.Groupoids.Hom.has P f ↔ P v)
