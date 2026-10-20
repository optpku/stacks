/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Divisor
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry.LocallyRingedSpace
open AlgebraicGeometry.Scheme.Modules.MeromorphicSection

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

/- Lemma 42.26.1: flat pullback of the divisor cycle of a nonzero meromorphic section is the
sum of its divisor cycles on the reduced irreducible components of the source, weighted by
their generic multiplicities. -/
@[stacks 0EPJ] #check
  (AlgebraicGeometry.CycleGroup.flatPullback_divisor_eq_sum_components :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
      (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
      [IsIntegral Y.left] (n : ℤ)
      (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
      (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
      (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
      (s : meromorphicSections Y.left.toLocallyRingedSpace ℒ) (hs : s ≠ 0),
      reindex (X.hom.relativeDimensionFunction δ) (flatDivisorDegree n r)
          (flatPullback δ X Y f r (n - 1)
            (relativeDivisorCycle Y.hom δ ℒ s hs (n - 1)
              (hY.trans (sub_add_cancel n 1).symm))) =
        flatComponentDivisorSum δ X Y n hY f r ℒ s hs)

end AlgebraicGeometry.CycleGroup
