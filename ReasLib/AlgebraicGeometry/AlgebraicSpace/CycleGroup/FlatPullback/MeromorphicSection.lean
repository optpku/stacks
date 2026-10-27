/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.RegularPullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.MeromorphicFunction.Pullback.Criteria
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InvertiblePullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType.Composition

/-! # Flat pullback of meromorphic-section divisor cycles -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The restriction of a good structure morphism to an irreducible component
remains quasi-separated. -/
def quasiSeparated_flatComponent_structure {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] (η : genericPoints X) :
    QuasiSeparated ((flatComponent pX η).ι ≫ pX) :=
  @quasiSeparated_comp S (flatComponent pX η).X X B (flatComponent pX η).ι pX
    (@QuasiSeparated.of_separated S (flatComponent pX η).X X (flatComponent pX η).ι
      (@IsClosedImmersion.separated S (flatComponent pX η).X X
        (flatComponent pX η).ι (flatComponent pX η).isClosedImmersion)) inferInstance

/-- The restriction of a good structure morphism to an irreducible component
remains locally of finite type. -/
def locallyOfFiniteType_flatComponent_structure {S : Scheme.{u}}
    {B X : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (η : genericPoints X) :
    LocallyOfFiniteType ((flatComponent pX η).ι ≫ pX) :=
  locallyOfFiniteType_closedSubspace_comp (flatComponent pX η) pX

/-- Pullbacks of meromorphic functions along the restriction of a flat morphism
to an irreducible component of the source are defined. -/
def pullbacksMeromorphicFunctionsDefined_flatComponent
    {S : Scheme.{u}} {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) [Flat f] [IsIntegral Y] (η : genericPoints X) :
    PullbacksMeromorphicFunctionsDefined ((flatComponent pX η).ι ≫ f) :=
  sorry

/-- The pullback `s_i = f|_{X_i}^*(s)` of a meromorphic section of `L` to an
irreducible component of the source. -/
noncomputable def meromorphicSectionPullbackToFlatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (η : genericPoints X) :
    meromorphicSections (flatComponent pX η).X
      ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L) :=
  @MeromorphicConstruction.Pullback.pullback S (flatComponent pX η).X Y
    ((flatComponent pX η).ι ≫ f)
    (pullbacksMeromorphicFunctionsDefined_flatComponent pX f η) L s

/-- The pulled-back meromorphic section on an irreducible component remains
regular. -/
theorem isRegularMeromorphicSection_flatComponent {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r] [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s)
    (η : genericPoints X) :
    IsRegularMeromorphicSection (flatComponent pX η).X
      ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L)
      (meromorphicSectionPullbackToFlatComponent pX f r L s η) :=
  @isRegularMeromorphicSection_pullback S (flatComponent pX η).X Y
    ((flatComponent pX η).ι ≫ f)
    (pullbacksMeromorphicFunctionsDefined_flatComponent pX f η) L inferInstance s hs

/-- The cycle `n_i (X_i → X)_* div_{f^* L|_{X_i}}(s_i)` of the pulled-back
meromorphic section on an irreducible component of `X`. -/
noncomputable def flatComponentMeromorphicDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s)
    (η : genericPoints X) :
    Function.locallyFinsupp (Points X) ℤ :=
  (@ClosedSubspace.componentMultiplicity S X
      (LocallyOfFiniteType.isLocallyNoetherian pX) (ClosedSubspace.id X) η : ℤ) •
    closedImmersionCyclePushforward (flatComponent pX η).ι
      (hClosed := (flatComponent pX η).isClosedImmersion)
      (@meromorphicSectionDivisorCycle S B (flatComponent pX η).X
        inferInstance inferInstance ((flatComponent pX η).ι ≫ pX)
        (quasiSeparated_flatComponent_structure pX η)
        (locallyOfFiniteType_flatComponent_structure pX η) δ inferInstance
        (isIntegral_flatComponent pX η)
        ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L) inferInstance
        (meromorphicSectionPullbackToFlatComponent pX f r L s η)
        (isRegularMeromorphicSection_flatComponent pX f r L s hs η))

/-- A component meromorphic divisor cycle is the multiplicity-weighted
closed-immersion pushforward of `div_{f^* L|_{X_i}}(s_i)`. -/
theorem flatComponentMeromorphicDivisor_eq {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s)
    (η : genericPoints X) :
    flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η =
      (@ClosedSubspace.componentMultiplicity S X
          (LocallyOfFiniteType.isLocallyNoetherian pX)
          (ClosedSubspace.id X) η : ℤ) •
        closedImmersionCyclePushforward (flatComponent pX η).ι
          (hClosed := (flatComponent pX η).isClosedImmersion)
          (@meromorphicSectionDivisorCycle S B (flatComponent pX η).X
            inferInstance inferInstance ((flatComponent pX η).ι ≫ pX)
            (quasiSeparated_flatComponent_structure pX η)
            (locallyOfFiniteType_flatComponent_structure pX η) δ inferInstance
            (isIntegral_flatComponent pX η)
            ((Modules.pullback ((flatComponent pX η).ι ≫ f)).obj L) inferInstance
            (meromorphicSectionPullbackToFlatComponent pX f r L s η)
            (isRegularMeromorphicSection_flatComponent pX f r L s hs η)) :=
  rfl

/-- The family of multiplicity-weighted component meromorphic divisor cycles is
locally finite on `|X|`. -/
theorem locallyFinite_flatComponentMeromorphicDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y]
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    LocallyFinite fun η : genericPoints X ↦
      (flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η).support :=
  sorry

/-- An irreducible component of `X` has `δ`-dimension `n + r` when `Y` is
integral of `δ`-dimension `n` and `f` is flat of relative dimension `r`. -/
theorem flatComponent_deltaDimension {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (η : genericPoints X) :
    @deltaDimension S B (flatComponent pX η).X inferInstance inferInstance
      ((flatComponent pX η).ι ≫ pX) (quasiSeparated_flatComponent_structure pX η)
      (locallyOfFiniteType_flatComponent_structure pX η) δ inferInstance
      (@univIrreducibleClosed S (flatComponent pX η).X (isIntegral_flatComponent pX η)) = n + (r : ℤ) :=
  sorry

/-- Flat pullback of the divisor of a nonzero meromorphic section on a good integral
algebraic space is the locally finite sum of the divisors of its pullbacks to the
reduced irreducible components, pushed forward and weighted by their multiplicities. -/
theorem flatPullback_meromorphicSectionDivisor {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    flatPullback pY pX δ f r hf (n - 1)
        (meromorphicSectionDivisorCycle pY δ s hs) =
      AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η)
        (locallyFinite_flatComponentMeromorphicDivisor pY pX δ f r hf L s hs) :=
  sorry

/-- The flat pullback of `div_L(s)` is an `(n + r - 1)`-cycle on `X`. -/
theorem flatPullback_meromorphicSectionDivisor_mem_cycleGroup {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    flatPullback pY pX δ f r hf (n - 1)
        (meromorphicSectionDivisorCycle pY δ s hs) ∈
      (cycleGroup pX) δ (n + (r : ℤ) - 1) :=
  sorry

/-- The multiplicity-weighted sum of component meromorphic divisor cycles is an
`(n + r - 1)`-cycle on `X`. -/
theorem flatComponentMeromorphicDivisorSum_mem_cycleGroup {S : Scheme.{u}}
    {B X Y : AlgebraicSpace S} [UniversallyCatenary B] [IsAbsolutelyQuasiSeparated B]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (f : X ⟶ Y) (r : ℕ) [Flat f] [RelativeDimension f r]
    (hf : f ≫ pY = pX) [IsIntegral Y] (n : ℤ)
    (hY : deltaDimension pY δ (univIrreducibleClosed Y) = n)
    (L : Y.Modules) [isInvertibleObject L]
    (s : meromorphicSections Y L) (hs : IsRegularMeromorphicSection Y L s) :
    AlgebraicCycle.locallyFiniteSum
        (fun η : genericPoints X ↦
          flatComponentMeromorphicDivisor pY pX δ f r hf L s hs η)
        (locallyFinite_flatComponentMeromorphicDivisor pY pX δ f r hf L s hs) ∈
      (cycleGroup pX) δ (n + (r : ℤ) - 1) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
