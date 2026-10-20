/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Composition.BaseChange
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

/-!
# Base change of composition of families of cycles on fibres
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 62.13.3
The formation of `α ∘ β` is compatible with arbitrary base change, for
nonnegative degrees, under the canonical identification of the resulting
fibres.
-/
@[stacks 0H6K] #check (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp_baseChange :
  ∀ {S S' X Y : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (p : Y ⟶ S)
    (f : X ⟶ Y) [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    {r e : ℤ} (hr : 0 ≤ r) (he : 0 ≤ e)
    (α : AlgebraicGeometry.Scheme.Hom.CyclesOnFibers f r)
    (β : AlgebraicGeometry.Scheme.Hom.CyclesOnFibers p e)
    (s' : S')
    (x' : (AlgebraicGeometry.Scheme.Pullback.overMap g p f ≫
      CategoryTheory.Limits.pullback.snd p g).fiber s'),
    AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.toAlgebraicCycle
        (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp
          (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange
            (AlgebraicGeometry.Scheme.Pullback.isPullback_overMap g p f) α)
          (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange
            (CategoryTheory.IsPullback.of_hasPullback p g) β))
        s' x' =
      AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.toAlgebraicCycle
        (AlgebraicGeometry.Scheme.Hom.FiberCycleFamily.baseChange
          (CategoryTheory.IsPullback.of_hasPullback (f ≫ p) g)
          (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.comp α β))
        s'
        (AlgebraicGeometry.Scheme.Hom.CyclesOnFibers.compBaseChangeFiberMap
          g p f s' x'))
