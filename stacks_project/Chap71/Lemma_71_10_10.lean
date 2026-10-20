/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.RegularPullback
import StacksCheckRecall

/-!
# Lemma 71.10.10

A morphism of algebraic spaces for which pullbacks of meromorphic functions are defined
induces a canonical pullback map on meromorphic sections of any module sheaf, and regular
meromorphic sections of invertible sheaves remain regular after pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

/-- The canonical pullback of meromorphic sections, retained under its source-facing name. -/
@[stacks 0ENC]
def pullbackMeromorphicSections {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [PullbacksMeromorphicFunctionsDefined f] (F : Y.Modules) :
    meromorphicSections Y F → meromorphicSections X ((Modules.pullback f).obj F) :=
  AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Pullback.pullback f F

/- Lemma 71.10.10 (1)
A morphism preserving meromorphic denominators canonically pulls back meromorphic sections
of every module sheaf on its target. -/
@[stacks 0ENC] #check
  (AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Pullback.pullback :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
      [PullbacksMeromorphicFunctionsDefined f] → (F : Y.Modules) →
      meromorphicSections Y F → meromorphicSections X ((Modules.pullback f).obj F))

/- Lemma 71.10.10 (2)
Let `L` be an invertible `𝒪_Y`-module. A regular meromorphic section `s` of `L` pulls back
to a regular meromorphic section of `f^* L`. -/
@[stacks 0ENC] #check
  (AlgebraicGeometry.AlgebraicSpace.isRegularMeromorphicSection_pullback :
    {S : Scheme.{u}} → {X Y : AlgebraicSpace S} → (f : X ⟶ Y) →
      [PullbacksMeromorphicFunctionsDefined f] → (L : Y.Modules) →
      [isInvertibleObject L] → {s : meromorphicSections Y L} →
      IsRegularMeromorphicSection Y L s →
      IsRegularMeromorphicSection X ((Modules.pullback f).obj L)
        (AlgebraicGeometry.AlgebraicSpace.MeromorphicConstruction.Pullback.pullback f L s))
