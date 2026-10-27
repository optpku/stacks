/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.DirectImage
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Evaluation

/-! # Direct-image comparison at flat objects -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open FiberedCategoryOver.Groupoids Functor.Fiber Opposite
open scoped Bicategory

noncomputable section
universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [HasSmallCFGTypeSections f]

/-- Evaluation of the canonical comparison from quasi-coherent direct image to étale direct image. -/
def directImageCounitEval {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) :
    (SheafOfModules.evaluation (etaleRingedSite Y).structureSheaf
      (op (fiberInclusion.obj y))).obj
        ((inclusion Y ⋙ restriction Y).obj ((directImage f).obj F)) ⟶
    (SheafOfModules.evaluation (etaleRingedSite Y).structureSheaf
      (op (fiberInclusion.obj y))).obj
        ((LQCohFbc.inclusion Y).obj
          ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))) :=
  LQCohFbc.toQCohCounitEval y
    ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F))

/-- The direct-image comparison is canonical coreflection counit evaluation. -/
theorem directImageCounitEval_eq {V : Over S} (y : Y.p.Fiber V) (F : QCoh X) :
    directImageCounitEval f y F =
      LQCohFbc.toQCohCounitEval y
        ((LQCohFbc.directImage f).obj ((toLQCohFbc X).obj F)) := rfl

/-- Quasi-coherent and étale direct images have isomorphic values at every flat object. -/
instance directImageCounitEval_isIso {V : Over S} (y : Y.p.Fiber V)
    [AlgebraicStack.Flat (YonedaSlice.representative y)] (F : QCoh X) :
    IsIso (directImageCounitEval f y F) := sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
