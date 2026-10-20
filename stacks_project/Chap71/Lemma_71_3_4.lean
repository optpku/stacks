/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Pullback

/-!
# Lemma 71.3.4

If a morphism of algebraic spaces is flat at a point whose fibre local ring has
dimension zero, then weakly associated points of a quasi-coherent module pull
back along that morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 71.3.4: for a scheme `S`, a morphism `f : X ⟶ Y` of algebraic spaces
over `S`, a quasi-coherent `𝒪_Y`-module `𝒢`, and a point `x` of `X`, if
`Points.map f x` is weakly associated to `𝒢`, `f` is flat at `x`, and the
dimension of the local ring of the fibre of `f` at `x` is zero, then `x` is
weakly associated to `(pullback f).obj 𝒢`. -/
@[stacks 0CUA]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_pullback_of_flatAt_of_fiberStalkDimEqAt_zero :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (𝒢 : Y.Modules)
      [𝒢.IsQuasicoherent] (x : Points X),
      FlatAt f x → FiberStalkDimEqAt f 0 x → Points.map f x ∈ 𝒢.weakAss →
        x ∈ ((AlgebraicGeometry.AlgebraicSpace.Modules.pullback f).obj 𝒢).weakAss)
