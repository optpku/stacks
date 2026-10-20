/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteFreeRetract
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

/- Lemma 17.25.2 (1): on a ringed space, the tensor-inverse characterization of invertibility is
the braided-monoidal specialization of the canonical invertible-object criterion. -/
@[stacks 0B8K "(1) iff (2)"]
#check @CategoryTheory.MonoidalCategory.isInvertibleObject.iff_exists_rightTensorInverse

/- Lemma 17.25.2, local-retract consequence: an invertible module is a retract of a finite free
module on a neighborhood of every point. -/
@[stacks 0B8K "local finite-free retract"]
#check @SheafOfModules.RingedSite.FiniteFreeRetract.existsNeighborhood_of_isInvertible

/- Lemma 17.25.2, dual consequence: a specified isomorphism
`L ⊗ N ≅ 𝒪_X` canonically determines the concrete isomorphism
`N ≅ (ihom L).obj 𝒪_X`. The reusable ringed-site bridge only assumes that `L` is closed. -/
@[stacks 0B8K "tensor inverse is dual"]
#check fun {X : RingedSpace.{u}} (L N : X.Modules) [Closed L]
    (e : L ⊗ N ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) ↦
  dual.isoOfTensorInverse L N e
