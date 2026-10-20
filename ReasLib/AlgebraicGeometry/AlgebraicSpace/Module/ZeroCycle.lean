/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Multiplicity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.ZeroSection
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.UniversallyCatenary
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Noetherian

/-!
# Zero-section cycles on algebraic spaces
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function Set Topology TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The zero scheme of a section of an invertible module on a locally Noetherian algebraic
space is locally Noetherian. -/
instance instIsLocallyNoetherian_zeroScheme {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (ℒ : Y.Modules) [isInvertibleObject ℒ] (s : ℒ.sections) :
    IsLocallyNoetherian (zeroScheme ℒ s).X :=
  instIsLocallyNoetherian_of_isClosedImmersion (zeroScheme ℒ s)

/-- The coefficient of `[Z(s)]_k` at a point `y` of `|Y|`. -/
noncomputable def zeroCycleCoeff {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (y : Points Y) : ℤ :=
  ∑ᶠ η : genericPoints (zeroScheme ℒ s).X,
    @dite ℤ (Points.map (zeroSchemeι ℒ s) η.1 = y ∧ d y = k)
      (Classical.propDecidable _)
      (fun _ ↦ (genericMultiplicity η : ℤ)) (fun _ ↦ 0)

/-- The coefficient function of `[Z(s)]_k` has locally finite support. -/
theorem zeroCycleCoeff_locallyFiniteSupport {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    LocallyFiniteSupport (zeroCycleCoeff d ℒ s k) :=
  sorry

/-- The degree-`k` cycle of the zero scheme of `s`, as a locally finite function on
`|Y|`. -/
noncomputable def zeroCycle {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ where
  toFun := zeroCycleCoeff d ℒ s k
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun y _ ↦
    zeroCycleCoeff_locallyFiniteSupport d ℒ s k y

/-- Evaluation of `[Z(s)]_k` recovers the associated coefficient function. -/
theorem zeroCycle_apply {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) (y : Points Y) :
    zeroCycle d ℒ s k y = zeroCycleCoeff d ℒ s k y :=
  rfl

/-- The zero cycle is the locally finite packaging of `zeroCycleCoeff`. -/
theorem zeroCycle_def {S : Scheme.{u}} {Y : AlgebraicSpace S}
    [IsLocallyNoetherian Y] (d : Points Y → ℤ) (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    (zeroCycle d ℒ s k : Points Y → ℤ) = zeroCycleCoeff d ℒ s k :=
  rfl

/-- The zero-section cycle measured by the relative dimension function induced by `p` and
`δ`. -/
noncomputable def relativeZeroCycle {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) : Function.locallyFinsupp (Points Y) ℤ :=
  @zeroCycle S Y (LocallyOfFiniteType.isLocallyNoetherian p)
    (Hom.relativeDimensionFunction p δ) ℒ _ s k

/-- The relative zero cycle is the core zero cycle for `p.relativeDimensionFunction δ`. -/
theorem relativeZeroCycle_def {S : Scheme.{u}} {B Y : AlgebraicSpace S}
    [UniversallyCatenary B] (p : Y ⟶ B) [QuasiSeparated p] [LocallyOfFiniteType p]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (ℒ : Y.Modules) [isInvertibleObject ℒ]
    (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycle p δ ℒ s k =
      @zeroCycle S Y (LocallyOfFiniteType.isLocallyNoetherian p)
        (Hom.relativeDimensionFunction p δ) ℒ _ s k :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Modules
