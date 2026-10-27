/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 76.27.2 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian
(`LocallyNoetherianFibers`). Let `x` in `Points X` and `y = Points.map f x`. We
say that `f` is Gorenstein at `x` if `f` is flat at `x` (`FlatAt`) and the
equivalent conditions of Lemma 67.22.5 hold for the property
`fiberStalkGorenstein` of Lemma 76.27.1 (`existsEtaleSquareAt` and, equivalently,
`forallEtaleSquareAt`). -/
@[stacks 0E14] #check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Points X → Prop)

/- Definition 76.27.2 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume the fibres of `f` are locally Noetherian. We
say `f` is a Gorenstein morphism if `f` is Gorenstein at every point of
`Points X`. -/
@[stacks 0E14] #check
  (AlgebraicGeometry.AlgebraicSpace.Gorenstein :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (X ⟶ Y) → Prop)
