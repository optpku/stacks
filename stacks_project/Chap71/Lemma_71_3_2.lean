/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.Pushforward

/-!
# Lemma 71.3.2

The weakly associated locus of a quasi-coherent module is preserved by
pushforward along an affine morphism of algebraic spaces from a locally
Noetherian source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

/- Lemma 71.3.2: Let `S` be a scheme. Let `f : X ⟶ Y` be an affine morphism of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. If `X` is
locally Noetherian, then `((pushforward f).obj F).weakAss = Points.map f '' F.weakAss`. -/
@[stacks 0CU8] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_pushforward_eq_image_of_affine :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
      (F : X.Modules) [F.IsQuasicoherent] [IsLocallyNoetherian X],
      ((pushforward f).obj F).weakAss = Points.map f '' F.weakAss)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.mem_weakAss_pushforward_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Affine f]
    (F : X.Modules) [F.IsQuasicoherent] [IsLocallyNoetherian X] (y : Points Y),
    y ∈ ((pushforward f).obj F).weakAss ↔
      ∃ x : Points X, x ∈ F.weakAss ∧ Points.map f x = y)
