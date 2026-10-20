/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroCycle

/-!
# Component decompositions of zero cycles

This file defines zero cycles on reduced irreducible components, their multiplicity-weighted
locally finite sum, and the resulting decomposition of a zero-section cycle.
-/

@[expose] public section

open CategoryTheory Function Set Topology TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Absolute

variable {Y : Scheme.{u}}

/-- The zero cycle cut out on an irreducible component, pushed forward to the ambient scheme. -/
noncomputable def componentZeroCycle [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) (η : genericPoints Y) : AlgebraicCycle Y ℤ :=
  let i := Y.irreducibleComponentSubschemeι (genericPoints.component η)
  AlgebraicCycle.map i (d ∘ i) d
    (zeroCycle (d ∘ i) ((pullback i).obj ℒ) (sectionsPullback i ℒ s) k)

/-- The component zero cycle uses the restricted module and section on the canonical reduced
irreducible-component subscheme. -/
theorem componentZeroCycle_def [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) (η : genericPoints Y) :
    componentZeroCycle d ℒ s k η =
      let i := Y.irreducibleComponentSubschemeι (genericPoints.component η)
      AlgebraicCycle.map i (d ∘ i) d
        (zeroCycle (d ∘ i) ((pullback i).obj ℒ) (sectionsPullback i ℒ s) k) := sorry

/-- The multiplicity-weighted component zero cycles of degree `k + 1` form a locally finite
family. -/
theorem componentZeroCyclesLocallyFinite [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) :
    LocallyFinite fun η : genericPoints Y ↦
      (if d η.1 = k + 1 then
        (AlgebraicCycle.genericMultiplicity Y η : ℤ) • componentZeroCycle d ℒ s k η
      else 0).support := sorry

/-- The locally finite, multiplicity-weighted sum of the zero cycles cut out on the
`(k + 1)`-dimensional irreducible components. -/
noncomputable def zeroCycleComponentSum [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) : AlgebraicCycle Y ℤ :=
  AlgebraicCycle.locallyFiniteSum
    (fun η : genericPoints Y ↦
      if d η.1 = k + 1 then
        (AlgebraicCycle.genericMultiplicity Y η : ℤ) • componentZeroCycle d ℒ s k η
      else 0)
    (componentZeroCyclesLocallyFinite d ℒ s k)

/-- Evaluation of the component sum is the pointwise finite sum of its weighted component
cycles. -/
theorem zeroCycleComponentSum_apply [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) (y : Y) :
    zeroCycleComponentSum d ℒ s k y = ∑ᶠ η : genericPoints Y,
      if d η.1 = k + 1 then
        (AlgebraicCycle.genericMultiplicity Y η : ℤ) * componentZeroCycle d ℒ s k η y
      else 0 := sorry

/-- The zero-section cycle is the multiplicity-weighted sum of the cycles cut out on the
top-dimensional irreducible components. -/
theorem zeroCycle_eq_sum_components [IsLocallyNoetherian Y]
    (d : Y → ℤ) [IsDimensionFunction d]
    (ℒ : Y.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ)
    (hY : ∀ y : Y, d y ≤ k + 1)
    (hZ : ∀ z : zeroScheme ℒ s, d (zeroSchemeι ℒ s z) ≤ k)
    (hregular : ∀ ξ : genericPoints (zeroScheme ℒ s),
      d (zeroSchemeι ℒ s ξ.1) = k →
        RingedSpace.IsRegularSectionAt ℒ s (zeroSchemeι ℒ s ξ.1)) :
    zeroCycle d ℒ s k = zeroCycleComponentSum d ℒ s k := sorry

end Absolute

section Relative

variable {S Y : Scheme.{u}} (f : Y ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ]

/-- The component sum measured by the relative dimension function induced by `f` and `δ`. -/
noncomputable def relativeZeroCycleComponentSum (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) : AlgebraicCycle Y ℤ :=
  @zeroCycleComponentSum Y (LocallyOfFiniteType.isLocallyNoetherian f)
    (f.relativeDimensionFunction δ) ℒ _ s k

/-- The relative component sum is the core component sum for
`f.relativeDimensionFunction δ`. -/
theorem relativeZeroCycleComponentSum_def (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycleComponentSum f δ ℒ s k =
      @zeroCycleComponentSum Y (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) ℒ _ s k := sorry

/-- A relative zero-section cycle is the multiplicity-weighted sum of the zero cycles cut out
on its top-dimensional irreducible components. -/
theorem relativeZeroCycle_eq_sum_components
    (ℒ : Y.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ)
    (hY : ∀ y : Y, f.relativeDimensionFunction δ y ≤ k + 1)
    (hZ : ∀ z : zeroScheme ℒ s,
      f.relativeDimensionFunction δ (zeroSchemeι ℒ s z) ≤ k)
    (hregular : ∀ ξ : genericPoints (zeroScheme ℒ s),
      f.relativeDimensionFunction δ (zeroSchemeι ℒ s ξ.1) = k →
        RingedSpace.IsRegularSectionAt ℒ s (zeroSchemeι ℒ s ξ.1)) :
    relativeZeroCycle f δ ℒ s k = relativeZeroCycleComponentSum f δ ℒ s k := sorry

end Relative

end AlgebraicGeometry.Scheme.Modules
