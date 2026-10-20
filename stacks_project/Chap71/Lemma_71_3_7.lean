/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Pullback
import StacksCheckRecall

/-!
# Lemma 71.3.7

A point is weakly associated to the pullback of a quasi-coherent module along
an étale morphism of algebraic spaces if and only if its image is weakly
associated to the original module.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.3.7: for a scheme `S`, an étale morphism `f : X ⟶ Y` of algebraic
spaces over `S`, and a quasi-coherent `𝒪_Y`-module `𝒢`, a point `x` of `X` is
weakly associated to `(pullback f).obj 𝒢` if and only if its image is weakly
associated to `𝒢`. -/
@[stacks 0CUU] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_pullback_iff_of_etale :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
      (𝒢 : Y.Modules) [𝒢.IsQuasicoherent] (x : Points X),
      x ∈ ((pullback f).obj 𝒢).weakAss ↔ Points.map f x ∈ 𝒢.weakAss)
