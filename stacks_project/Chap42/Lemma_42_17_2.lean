/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicCycle.FlatPullback.Principal

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/- Lemma 42.17.2: flat pullback carries the principal divisor of `g` on `Y` to the
principal divisor of its image in the function field of `X`. -/
@[stacks 02RR] #check (AlgebraicGeometry.AlgebraicCycle.flatPullback_principal :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral X.left] [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (g : Y.left.functionFieldˣ),
    AlgebraicCycle.flatPullback δ X Y f r (n + (r : ℤ) - 1)
        (@AlgebraicCycle.principal Y.left
          (LocallyOfFiniteType.isLocallyNoetherian Y.hom) inferInstance g) =
      @AlgebraicCycle.principal X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance
        (f.left.functionFieldUnitsMap f.left.map_genericPoint_eq_of_isDominant g))
