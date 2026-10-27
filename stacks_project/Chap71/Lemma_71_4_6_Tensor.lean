/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.TensorPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Quasicoherent.Tensor

/-!
# Tensor of a module with the pullback of a module on algebraic spaces

The source module `F ⊗_{𝒪_X} f^* G` is the monoidal tensor of `F` with the
module pullback of `G`, obtained by transporting `moduleTensor` along the
commutative presentation of `𝒪_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

universe u

#check (AlgebraicGeometry.AlgebraicSpace.Modules.tensorPullback :
  {S : Scheme.{u}} → {X Y : AlgebraicSpace S} →
    X.Modules → (X ⟶ Y) → Y.Modules → X.Modules)

#check (AlgebraicGeometry.AlgebraicSpace.Modules.tensorPullback_eq :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (G : Y.Modules),
    tensorPullback F f G =
      (ofCommModules X).obj
        (tensorObj ((toCommModules X).obj F)
          ((toCommModules X).obj ((pullback f).obj G))))
