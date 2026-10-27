/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.InternalHom.Pullback

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

universe u

/- Lemma 103.10.9: Pullback along a flat morphism of algebraic stacks commutes
with quasi-coherent internal Hom from a finitely presented module. -/
@[stacks 0GQP] #check
  (AlgebraicGeometry.GroupoidsOver.QCoh.internalHomFP_pullbackIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
      (f : X ⟶ Y) [AlgebraicStack.Flat f]
      (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation],
      (QCoh.pullback f).obj (QCoh.internalHomFP F G) ≅
        QCoh.internalHomFP ((modulePullback f).obj F) ((QCoh.pullback f).obj G))
