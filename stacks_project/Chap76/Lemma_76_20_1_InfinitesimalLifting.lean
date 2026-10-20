/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Smooth.InfinitesimalLifting

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.specMapOver :
    ∀ {S : Scheme.{u}} {B' B : Type u} [CommRing B'] [CommRing B]
      (π : B' →+* B) (σ : Spec (CommRingCat.of B') ⟶ S),
      ofOver (Over.mk (Spec.map (CommRingCat.ofHom π) ≫ σ)) ⟶ ofOver (Over.mk σ))
