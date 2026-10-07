module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

/-!
# Flat pullback of algebraic cycles

This file defines the raw flat pullback of algebraic cycles and records its support,
coefficient, and additive properties.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- The coefficients defining flat pullback have locally finite support. -/
theorem flatPullbackLocallyFiniteSupport
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (c : AlgebraicCycle Y.left ℤ) :
    LocallyFiniteSupport (fun x : X.left ↦
      ∑ᶠ y : Y.left, c y *
        ((@Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          ((Scheme.PointClosure.reducedStructure y).ideal.comap f.left)
          (X.hom.relativeDimensionFunction δ) k :
            dimensionSubgroup (X.hom.relativeDimensionFunction δ) k) :
          AlgebraicCycle X.left ℤ) x) := sorry

/-- Flat pullback of an algebraic cycle, computed from the associated cycles of the
scheme-theoretic inverse images of reduced point closures. -/
noncomputable def flatPullback
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (c : AlgebraicCycle Y.left ℤ) : AlgebraicCycle X.left ℤ where
  toFun := fun x ↦
    ∑ᶠ y : Y.left, c y *
      ((@Scheme.IdealSheafData.associatedCycle X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        ((Scheme.PointClosure.reducedStructure y).ideal.comap f.left)
        (X.hom.relativeDimensionFunction δ) k :
          dimensionSubgroup (X.hom.relativeDimensionFunction δ) k) :
        AlgebraicCycle X.left ℤ) x
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    flatPullbackLocallyFiniteSupport δ X Y f r k c x

/-- The coefficient of a flat pullback is the sum of the multiplicity-weighted coefficients
of the inverse images of the source cycle's point closures. -/
theorem flatPullback_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (c : AlgebraicCycle Y.left ℤ) (x : X.left) :
    flatPullback δ X Y f r k c x =
      ∑ᶠ y : Y.left, c y *
        ((@Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          ((Scheme.PointClosure.reducedStructure y).ideal.comap f.left)
          (X.hom.relativeDimensionFunction δ) k :
            dimensionSubgroup (X.hom.relativeDimensionFunction δ) k) :
          AlgebraicCycle X.left ℤ) x := sorry

/-- Flat pullback at target degree `k` is supported in relative `δ`-dimension `k`. -/
theorem flatPullback_mem_dimensionSubgroup
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (c : AlgebraicCycle Y.left ℤ) :
    flatPullback δ X Y f r k c ∈
      dimensionSubgroup (X.hom.relativeDimensionFunction δ) k := sorry

/-- Flat pullback sends the zero cycle to zero. -/
theorem flatPullback_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) :
    flatPullback δ X Y f r k (0 : AlgebraicCycle Y.left ℤ) = 0 := sorry

/-- Flat pullback preserves addition of algebraic cycles. -/
theorem flatPullback_add
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (k : ℤ) (a b : AlgebraicCycle Y.left ℤ) :
    flatPullback δ X Y f r k (a + b) =
      flatPullback δ X Y f r k a + flatPullback δ X Y f r k b := sorry

end AlgebraicGeometry.AlgebraicCycle
