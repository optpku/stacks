/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatBaseChange.Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

/- Lemma 42.67.6 (1): a proper morphism in a scheme slice remains proper after
canonical base change. -/
@[stacks 0FVL] #check
  (AlgebraicGeometry.IsProper.instOverPullbackMap :
    ∀ {S S' : Scheme.{u}} (g : S' ⟶ S) {X Y : Over S}
      (f : X ⟶ Y) [IsProper f.left],
      IsProper ((Over.pullback g).map f).left)

/- Lemma 42.67.6 (2): dimension-shifted flat base change commutes with proper
pushforward on cycle groups. -/
@[stacks 0FVL] #check
  (AlgebraicGeometry.CycleGroup.baseChangePullback_map :
    ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (delta : S → ℤ) [IsDimensionFunction delta]
      (delta' : S' → ℤ) [IsDimensionFunction delta'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible delta delta' c)
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : Y ⟶ X) [IsProper f.left] (k : ℤ),
      (CycleGroup.baseChangePullback g delta delta' c hcompat X.hom k).comp
          (CycleGroup.mapHom f.left (Y.hom.relativeDimensionFunction delta)
            (X.hom.relativeDimensionFunction delta) k) =
        (CycleGroup.mapHom ((Over.pullback g).map f).left
            (((Over.pullback g).obj Y).hom.relativeDimensionFunction delta')
            (((Over.pullback g).obj X).hom.relativeDimensionFunction delta') (k + c)).comp
          (CycleGroup.baseChangePullback g delta delta' c hcompat Y.hom k))

/- Lemma 42.67.6 (3): dimension-shifted flat base change commutes with proper
pushforward on Chow groups. -/
@[stacks 0FVL] #check
  (AlgebraicGeometry.ChowGroup.baseChangePullback_map :
    ∀ {S S' : Scheme.{u}} [UniversallyCatenary S] [UniversallyCatenary S']
      (g : S' ⟶ S) [Flat g] (delta : S → ℤ) [IsDimensionFunction delta]
      (delta' : S' → ℤ) [IsDimensionFunction delta'] (c : ℤ)
      (hcompat : g.IsDimensionFunctionCompatible delta delta' c)
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      (f : Y ⟶ X) [IsProper f.left] (k : ℤ),
      (ChowGroup.baseChangePullback g delta delta' c hcompat X.hom k).comp
          (ChowGroup.map delta Y X f k) =
        (ChowGroup.map delta' ((Over.pullback g).obj Y) ((Over.pullback g).obj X)
            ((Over.pullback g).map f) (k + c)).comp
          (ChowGroup.baseChangePullback g delta delta' c hcompat Y.hom k))
