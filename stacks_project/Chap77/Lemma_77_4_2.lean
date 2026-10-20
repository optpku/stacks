/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 77.4.2: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is locally of finite type. Let `ℱ` be a
quasi-coherent `𝒪_X`-module of finite type. Let `y ∈ |Y|` and write `F` for
the set-theoretic fibre `fiberOver f y ⊂ |X|`. Then the set of points of `F`
at which `ℱ` is flat over `Y` is open in `F`. -/
@[stacks 0CWK] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.isOpen_flatOverAt_fiber :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsQuasicoherent]
      [ℱ.IsFiniteType] (y : Points Y),
      IsOpen (AlgebraicGeometry.AlgebraicSpace.Modules.fiberFlatOverLocus ℱ f y))

