/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.Noetherian
import StacksCheckRecall

/-!
# Finite presentation morphisms into Noetherian algebraic spaces

A morphism of algebraic spaces of finite presentation into a Noetherian
target has Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 67.28.6: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `f` is of finite presentation and `Y` is
Noetherian, then `X` is Noetherian. -/
@[stacks 04ZL] #check
  (AlgebraicGeometry.AlgebraicSpace.FinitePresentation.isNoetherian :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.FinitePresentation f]
      [AlgebraicGeometry.AlgebraicSpace.IsNoetherian Y],
      AlgebraicGeometry.AlgebraicSpace.IsNoetherian X)
