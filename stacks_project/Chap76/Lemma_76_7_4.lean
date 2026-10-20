/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Differentials.Quasicoherent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

/- Lemma 76.7.4: the sheaf of relative differentials of a morphism of algebraic spaces
over a scheme is quasi-coherent. -/
@[stacks 04CV] #check
  (AlgebraicGeometry.AlgebraicSpace.isQuasicoherent_relativeDifferentials :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
      (AlgebraicGeometry.AlgebraicSpace.Hom.relativeDifferentials f).IsQuasicoherent)
