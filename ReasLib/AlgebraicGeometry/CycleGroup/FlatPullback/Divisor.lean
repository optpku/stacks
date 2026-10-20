/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Pullback

/-!
# Flat pullback of divisors by irreducible components

This file constructs the multiplicity-weighted sum of divisor cycles obtained by pulling a
meromorphic section back to the reduced irreducible components of the source of a flat morphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

open Scheme.Modules.MeromorphicSection

/-- The two natural expressions for the degree of a flat component divisor agree. -/
theorem flatDivisorDegree (n : ℤ) (r : ℕ) :
    (n - 1) + (r : ℤ) = n + (r : ℤ) - 1 := sorry

/-- The divisor of a section pulled back to a reduced irreducible component has degree
`(n - 1) + r`. -/
theorem flatComponentDivisorCycle_mem
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X.left) :
    @Scheme.nonzeroMeromorphicSectionDivisorCycle
        (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
        (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (genericPoints.ofComponent C).1)
        inferInstance
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left)).obj ℒ)
        (Scheme.Modules.Invertible.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left) inferInstance)
        (pullbackToFlatComponent f.left ℒ s C)
        (pullbackToFlatComponent_ne_zero f.left ℒ s hs C) ∈
      AlgebraicCycle.dimensionSubgroup
        ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom).relativeDimensionFunction δ)
        ((n - 1) + (r : ℤ)) := sorry

/-- The divisor cycle of a section pulled back to a reduced irreducible component, pushed
forward to the source and expressed in degree `n + r - 1`. -/
noncomputable def flatComponentDivisorCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X.left) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1) :=
  reindex (X.hom.relativeDimensionFunction δ) (flatDivisorDegree n r)
    (mapHom (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)
      ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom).relativeDimensionFunction δ)
      (X.hom.relativeDimensionFunction δ) ((n - 1) + (r : ℤ))
      ⟨@Scheme.nonzeroMeromorphicSectionDivisorCycle
          (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (genericPoints.ofComponent C).1)
          inferInstance
          ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left)).obj ℒ)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left) inferInstance)
          (pullbackToFlatComponent f.left ℒ s C)
          (pullbackToFlatComponent_ne_zero f.left ℒ s hs C),
        flatComponentDivisorCycle_mem δ X Y n hY f r ℒ s hs C⟩)

/-- Forgetting the degree of a component divisor cycle gives the pushforward of its divisor on
the reduced component closure. -/
theorem flatComponentDivisorCycle_toAlgebraicCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X.left) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        (flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C) =
      AlgebraicCycle.map (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)
        ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom).relativeDimensionFunction δ)
        (X.hom.relativeDimensionFunction δ)
        (@Scheme.nonzeroMeromorphicSectionDivisorCycle
          (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (genericPoints.ofComponent C).1)
          inferInstance
          ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left)).obj ℒ)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left) inferInstance)
          (pullbackToFlatComponent f.left ℒ s C)
          (pullbackToFlatComponent_ne_zero f.left ℒ s hs C)) := sorry

/-- The generic-multiplicity-weighted component divisor cycles form a locally finite family. -/
theorem flatComponentDivisorsLocallyFinite
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    LocallyFinite fun C : irreducibleComponents X.left ↦
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        ((@AlgebraicCycle.genericMultiplicity X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (genericPoints.ofComponent C) : ℤ) •
          flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C)).support := sorry

/-- The locally finite sum of component divisor cycles weighted by their generic
multiplicities. -/
noncomputable def flatComponentDivisorSum
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1) :=
  locallyFiniteSum (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
    (fun C : irreducibleComponents X.left ↦
      (@AlgebraicCycle.genericMultiplicity X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (genericPoints.ofComponent C) : ℤ) •
        flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C)
    (flatComponentDivisorsLocallyFinite δ X Y n hY f r ℒ s hs)

/-- Evaluation of the component divisor sum is the corresponding pointwise finite sum. -/
theorem flatComponentDivisorSum_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (x : X.left) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        (flatComponentDivisorSum δ X Y n hY f r ℒ s hs) x =
      ∑ᶠ C : irreducibleComponents X.left,
        toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
          ((@AlgebraicCycle.genericMultiplicity X.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (genericPoints.ofComponent C) : ℤ) •
            flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C) x := sorry

/-- Flat pullback of the divisor cycle of a nonzero meromorphic section is the sum of its
divisor cycles on the reduced irreducible components of the source, weighted by their generic
multiplicities. -/
theorem flatPullback_divisor_eq_sum_components
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    reindex (X.hom.relativeDimensionFunction δ) (flatDivisorDegree n r)
        (flatPullback δ X Y f r (n - 1)
          (relativeDivisorCycle Y.hom δ ℒ s hs (n - 1)
            (hY.trans (sub_add_cancel n 1).symm))) =
      flatComponentDivisorSum δ X Y n hY f r ℒ s hs := sorry

end AlgebraicGeometry.CycleGroup
