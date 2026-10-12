/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Components

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 42.25.3: Under the relative dimension bounds and stalkwise regularity hypothesis,
the relative zero cycle of a section of an invertible module equals the
generic-multiplicity-weighted sum of the relative zero cycles on the components. -/
@[stacks 0EPI]
#check (AlgebraicGeometry.Scheme.Modules.relativeZeroCycle_eq_sum_components :
  ∀ {S Y : Scheme.{u}} (f : Y ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (ℒ : Y.Modules) [Scheme.Modules.Invertible ℒ] (s : ℒ.sections) (k : ℤ),
    (∀ y : Y, f.relativeDimensionFunction δ y ≤ k + 1) →
    (∀ z : Scheme.zeroScheme ℒ s,
      f.relativeDimensionFunction δ (Scheme.zeroSchemeι ℒ s z) ≤ k) →
    (∀ ξ : genericPoints (Scheme.zeroScheme ℒ s),
      f.relativeDimensionFunction δ (Scheme.zeroSchemeι ℒ s ξ.1) = k →
        RingedSpace.IsRegularSectionAt ℒ s (Scheme.zeroSchemeι ℒ s ξ.1)) →
    Scheme.Modules.relativeZeroCycle f δ ℒ s k =
      Scheme.Modules.relativeZeroCycleComponentSum f δ ℒ s k)
