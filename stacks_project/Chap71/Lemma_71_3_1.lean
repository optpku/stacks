/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Pushforward
import StacksCheckRecall

/-!
# Lemma 71.3.1

The weakly associated locus of the pushforward of a quasi-coherent module along
an affine morphism of algebraic spaces is contained in the image of the weakly
associated locus of that module.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

universe u

/- Lemma 71.3.1: Let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Then
`((pushforward f).obj F).weakAss ⊆ Points.map f '' F.weakAss`. -/
@[stacks 0CU2] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_pushforward_subset_image_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      (F : X.Modules) [F.IsQuasicoherent],
      ((pushforward f).obj F).weakAss ⊆ Points.map f '' F.weakAss)

#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_pushforward_subset_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      (F : X.Modules) [F.IsQuasicoherent] (y : Points Y),
      y ∈ ((pushforward f).obj F).weakAss →
        ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y)
