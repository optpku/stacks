/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage.FlatEvaluation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.HigherDirectImage.FlatEvaluation
import StacksCheckRecall

/-!
# Evaluation of direct images on flat objects

The ordinary comparison uses étale direct image. Higher direct images are presented
by étale restriction of the fppf-derived pushforward of a quasi-coherent module.
Both higher-image functors are extended to integer degrees by zero in negative degrees.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open FiberedCategoryOver.Groupoids Functor.Fiber
open scoped Bicategory

universe u

/- Lemma 103.11.2: ordinary and quasi-coherent direct images agree at a flat object. -/
@[stacks 0GQQ] #check (AlgebraicGeometry.GroupoidsOver.QCoh.directImageCounitEval_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f] {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (F : QCoh X),
    IsIso (QCoh.directImageCounitEval f y F))

/- Lemma 103.11.2: higher direct images agree at a flat object in every integer degree. -/
@[stacks 0GQQ] #check (AlgebraicGeometry.GroupoidsOver.QCoh.higherDirectImageCounitEval_isIso :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallAssociatedTypeSections f StandardTopology.fppf]
    [HasInjectiveResolutions (AlgebraicStack.fppfModules X)]
    {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (F : QCoh X) (i : ℤ),
    IsIso (QCoh.higherDirectImageCounitEval f y F i))
