module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle.Components

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- 42.25.3.1: The `k`-cycle cut out by a section of an invertible module equals the locally
finite, generic-multiplicity-weighted sum of the `k`-cycles cut out on the `(k + 1)`-dimensional
irreducible components. -/
@[stacks 02SR]
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
