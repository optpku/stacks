/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.Scheme.Germ.MorphismProperty

universe u

/- Definition 76.26.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian
(`LocallyNoetherianFibers`). Let `x` in `Points X` and `y = Points.map f x`. We
say that `f` is Cohen–Macaulay at `x` if `f` is flat at `x` and the equivalent
conditions of Lemma 67.22.5 hold for the property `fiberStalkCohenMacaulay` of
Lemma 76.26.1. -/
@[stacks 0E0V] #check
  (AlgebraicGeometry.AlgebraicSpace.CohenMacaulayAt :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Points X → Prop)

/- Definition 76.26.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian. We
say `f` is a Cohen–Macaulay morphism if `f` is Cohen–Macaulay at every point of
`Points X`. -/
@[stacks 0E0V] #check
  (AlgebraicGeometry.AlgebraicSpace.CohenMacaulay :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulayAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ existsEtaleSquareAt fiberStalkCohenMacaulay f x)

#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulayAt_iff_forallEtaleSquareAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    CohenMacaulayAt f x ↔
      FlatAt f x ∧ forallEtaleSquareAt fiberStalkCohenMacaulay f x)

#check (AlgebraicGeometry.AlgebraicSpace.cohenMacaulay_iff_forall_cohenMacaulayAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    CohenMacaulay f ↔ ∀ x : Points X, CohenMacaulayAt f x)
