/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.FlatPullback
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.Cartier
public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin.FirstChern
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Relative.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

/-!
# Pullback along a relative effective Cartier divisor

This file constructs coefficientwise pullback along the restriction of a flat morphism
to a relative effective Cartier divisor, descends it to Chow groups, and compares it with
Cartier Gysin pullback and first-Chern intersection.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

namespace AlgebraicCycle

/-- The coefficient formula for relative Cartier pullback has locally finite support. -/
theorem relativeCartierPullbackLocallyFiniteSupport
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : AlgebraicCycle Y.left ℤ) :
    LocallyFiniteSupport (fun x : D.subscheme ↦
      ∑ᶠ y : Y.left, c y *
        ((@Scheme.IdealSheafData.associatedCycle D.subscheme
          (LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ X.hom))
          ((Scheme.PointClosure.reducedStructure y).ideal.comap (D.restrictedHom p).left)
          ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
          (n + (r : ℤ) - 1) :
            dimensionSubgroup ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
              (n + (r : ℤ) - 1)) : AlgebraicCycle D.subscheme ℤ) x) := sorry

/-- Coefficientwise pullback of algebraic cycles along the restriction of a flat morphism
to a relative effective Cartier divisor. -/
noncomputable def relativeCartierPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : AlgebraicCycle Y.left ℤ) : AlgebraicCycle D.subscheme ℤ where
  toFun := fun x ↦
    ∑ᶠ y : Y.left, c y *
      ((@Scheme.IdealSheafData.associatedCycle D.subscheme
        (LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ X.hom))
        ((Scheme.PointClosure.reducedStructure y).ideal.comap (D.restrictedHom p).left)
        ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
        (n + (r : ℤ) - 1) :
          dimensionSubgroup ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
            (n + (r : ℤ) - 1)) : AlgebraicCycle D.subscheme ℤ) x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    relativeCartierPullbackLocallyFiniteSupport δ X Y p D r n c x

/-- Relative Cartier pullback is given by its coefficientwise inverse-image formula. -/
theorem relativeCartierPullback_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : AlgebraicCycle Y.left ℤ) (x : D.subscheme) :
    relativeCartierPullback δ X Y p D r n c x =
      ∑ᶠ y : Y.left, c y *
        ((@Scheme.IdealSheafData.associatedCycle D.subscheme
          (LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ X.hom))
          ((Scheme.PointClosure.reducedStructure y).ideal.comap (D.restrictedHom p).left)
          ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
          (n + (r : ℤ) - 1) :
            dimensionSubgroup ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
              (n + (r : ℤ) - 1)) : AlgebraicCycle D.subscheme ℤ) x := sorry

/-- Relative Cartier pullback lands in the expected relative-dimension subgroup. -/
theorem relativeCartierPullback_mem_dimensionSubgroup
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : AlgebraicCycle Y.left ℤ) :
    relativeCartierPullback δ X Y p D r n c ∈
      dimensionSubgroup ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
        (n + (r : ℤ) - 1) := sorry

end AlgebraicCycle

namespace CycleGroup

/-- The value of relative Cartier pullback on a dimension-graded cycle. -/
noncomputable def relativeCartierPullbackValue
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) n) :
    CycleGroup D.subscheme ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
      (n + (r : ℤ) - 1) :=
  ⟨AlgebraicCycle.relativeCartierPullback δ X Y p D r n
      (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) n c),
    AlgebraicCycle.relativeCartierPullback_mem_dimensionSubgroup δ X Y p D r n
      (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) n c)⟩

/-- Relative Cartier pullback sends the zero dimension-graded cycle to zero. -/
theorem relativeCartierPullbackValue_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D] (n : ℤ) :
    relativeCartierPullbackValue δ X Y p D r n 0 = 0 := sorry

/-- Relative Cartier pullback preserves addition of dimension-graded cycles. -/
theorem relativeCartierPullbackValue_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D] (n : ℤ)
    (c₁ c₂ : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) n) :
    relativeCartierPullbackValue δ X Y p D r n (c₁ + c₂) =
      relativeCartierPullbackValue δ X Y p D r n c₁ +
        relativeCartierPullbackValue δ X Y p D r n c₂ := sorry

/-- Relative Cartier pullback as an additive map on dimension-graded cycle groups. -/
noncomputable def relativeCartierPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) :
    CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) n →+
      CycleGroup D.subscheme ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
        (n + (r : ℤ) - 1) where
  toFun := relativeCartierPullbackValue δ X Y p D r n
  map_zero' := relativeCartierPullbackValue_zero δ X Y p D r n
  map_add' := relativeCartierPullbackValue_add δ X Y p D r n

/-- Forgetting the grading exposes the coefficientwise relative Cartier pullback. -/
theorem toAlgebraicCycle_relativeCartierPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) n) :
    toAlgebraicCycle ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ)
        (n + (r : ℤ) - 1) (relativeCartierPullback δ X Y p D r n c) =
      AlgebraicCycle.relativeCartierPullback δ X Y p D r n
        (toAlgebraicCycle (Y.hom.relativeDimensionFunction δ) n c) := sorry

end CycleGroup

namespace RationalEquivalence

/-- Relative Cartier pullback sends rational boundaries to rational boundaries. -/
theorem relativeCartierPullback_mem_boundaries
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) :
    @boundaries Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
        (Y.hom.relativeDimensionFunction δ) inferInstance n ≤
      (@boundaries D.subscheme
        (LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ X.hom))
        ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ) inferInstance
        (n + (r : ℤ) - 1)).comap
        (CycleGroup.relativeCartierPullback δ X Y p D r n) := sorry

end RationalEquivalence

namespace ChowGroup

/-- Pullback on Chow groups along the restriction of a flat morphism to a relative
effective Cartier divisor. -/
noncomputable def relativeCartierPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) :
    RelativeChow δ Y n →+
      RelativeChow δ (Over.mk (D.subschemeι ≫ X.hom)) (n + (r : ℤ) - 1) :=
  QuotientAddGroup.map
    (@RationalEquivalence.boundaries Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
      (Y.hom.relativeDimensionFunction δ) inferInstance n)
    (@RationalEquivalence.boundaries D.subscheme
      (LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ X.hom))
      ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ) inferInstance
      (n + (r : ℤ) - 1))
    (CycleGroup.relativeCartierPullback δ X Y p D r n)
    (RationalEquivalence.relativeCartierPullback_mem_boundaries δ X Y p D r n)

/-- Relative Cartier pullback on Chow classes is induced by the coefficientwise cycle map. -/
theorem relativeCartierPullback_chowClass
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (D : X.left.IdealSheafData) (r : ℕ)
    [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    [IsRelativeEffectiveCartierDivisor p.left D]
    (n : ℤ) (c : CycleGroup Y.left (Y.hom.relativeDimensionFunction δ) n) :
    relativeCartierPullback δ X Y p D r n
        (@chowClass Y.left (LocallyOfFiniteType.isLocallyNoetherian Y.hom)
          (Y.hom.relativeDimensionFunction δ) inferInstance n c) =
      @chowClass D.subscheme
        (LocallyOfFiniteType.isLocallyNoetherian (D.subschemeι ≫ X.hom))
        ((D.subschemeι ≫ X.hom).relativeDimensionFunction δ) inferInstance
        (n + (r : ℤ) - 1) (CycleGroup.relativeCartierPullback δ X Y p D r n c) := sorry

/-- Cartier Gysin pullback after flat pullback agrees with pullback along the restriction
to the relative effective Cartier divisor. -/
theorem gysin_flatPullback_eq_relativeCartierPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (r : ℕ) [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    (D : X.left.IdealSheafData) [IsRelativeEffectiveCartierDivisor p.left D]
    (k : ℤ) (α : RelativeChow δ Y (k + 1)) :
    cartierGysin δ X D ((k + 1) + (r : ℤ))
        (flatPullback δ X Y p r (k + 1) α) =
      relativeCartierPullback δ X Y p D r (k + 1) α := sorry

/-- Capping a flat pullback with `c₁(D.associatedSheaf)` equals the pushforward of
pullback along the restriction to the relative effective Cartier divisor. -/
theorem firstChernClassCap_flatPullback_eq_map_relativeCartierPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (p : X ⟶ Y) (r : ℕ) [Flat p.left] [Scheme.Hom.RelativeDimension p.left r]
    (D : X.left.IdealSheafData) [IsRelativeEffectiveCartierDivisor p.left D]
    (k : ℤ) (α : RelativeChow δ Y (k + 1)) :
    firstChernClassCap δ X D.associatedSheaf ((k + 1) + (r : ℤ))
        (flatPullback δ X Y p r (k + 1) α) =
      map δ (Over.mk (D.subschemeι ≫ X.hom)) (Over.mk X.hom)
        (Over.homMk D.subschemeι rfl :
          Over.mk (D.subschemeι ≫ X.hom) ⟶ Over.mk X.hom)
        ((k + 1) + (r : ℤ) - 1)
        (relativeCartierPullback δ X Y p D r (k + 1) α) := sorry

end ChowGroup

end AlgebraicGeometry
