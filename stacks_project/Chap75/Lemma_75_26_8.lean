/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Pushforward.GeometricFibres

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 75.26.8 (1): if `f` is proper, flat, and of finite presentation, and the
geometric fibres of `f` are reduced and connected, then the canonical map
`𝒪_Y ⟶ f_* 𝒪_X` is an isomorphism. -/
@[stacks 0E0S] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.structureSheafMap_isIso_of_reducedConnectedGeometricFibres :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f]
      [Hom.HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f],
      IsIso (structureSheafMap f))

/- Lemma 75.26.8 (2): the canonical structure-sheaf pushforward map remains an
isomorphism after every base change. -/
@[stacks 0E0S] #check
  (AlgebraicGeometry.AlgebraicSpace.Hom.baseChange_structureSheafMap_isIso_of_reducedConnectedGeometricFibres :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y)
      [Proper f] [Flat f] [FinitePresentation f]
      [Hom.HasReducedGeometricFibres f] [AlgebraicSpace.HasConnectedGeometricFibres f],
      ∀ g : Y' ⟶ Y, IsIso (structureSheafMap (pullback.snd f g)))
