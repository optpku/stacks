/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent.Relative.Flat
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.45.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Let `E` in `D_QCoh(𝒪_X)`. If `f` is flat and locally of finite
presentation, then `E` is pseudo-coherent relative to `Y` if and only if `E` is
pseudo-coherent on `X`. -/
@[stacks 0DII] #check
  (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.isPseudoCoherentOver_iff_isPseudoCoherent :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicGeometry.AlgebraicSpace.Flat f]
      [AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation f]
      {E : ModuleDerived X}, derivedQuasiCoherentModuleProperty X E →
        (AlgebraicGeometry.AlgebraicSpace.ModuleDerived.IsPseudoCoherentOver f E ↔
          AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent X E))
