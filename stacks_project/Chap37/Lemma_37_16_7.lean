/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.FiberCriterion.FreeNeighborhood

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.16.7: a finitely presented module sheaf that is flat over the base at
`x`, with flat restriction to the scheme-theoretic fibre at `f.asFiber x`, is finite free on
an open neighbourhood of `x`. -/
@[stacks 080Q] #check
  (AlgebraicGeometry.Scheme.Modules.existsNeighborhoodFree_of_flatnessByFibers :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FinitePresentation f]
      (F : X.Modules) [F.IsFinitePresentation] (x : X),
      flatOverAt F f x →
      SheafOfModules.IsFlatAt
          ((pullback (f.fiberι (f x))).obj F) (f.asFiber x) →
        ∃ (U : Opens X) (_ : x ∈ U) (I : Type u), Finite I ∧
          Nonempty (F.over U ≅ SheafOfModules.free.{u} I))

end AlgebraicGeometry.Scheme.Modules
