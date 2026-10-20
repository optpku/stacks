/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.RationalFunction.GraphClosure

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RationalFunctionGraph

/-- On the graph closure of a rational function represented by an invertible section, its
principal cycle is the zero-divisor cycle minus the infinity-divisor cycle. -/
theorem principal_eq_zero_sub_infinity
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] (n : ℤ) (f : X.left.functionFieldˣ)
    (U : X.left.Opens) [Nonempty U] (s : Γ(X.left, U)ˣ)
    (hX : X.hom.relativeDimensionFunction delta (genericPoint X.left) = n)
    (hs : Units.map (X.left.germToFunctionField U).hom s = f) :
    @AlgebraicCycle.principal (closure X U s)
        (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom)) inferInstance
        (function X U s f) =
      (@Scheme.IdealSheafData.associatedCycle (closure X U s)
          (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom))
          (zeroDivisor X U s)
          ((fst X U s ≫ X.hom).relativeDimensionFunction delta) (n - 1) :
        AlgebraicCycle (closure X U s) ℤ) -
      (@Scheme.IdealSheafData.associatedCycle (closure X U s)
          (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom))
          (infinityDivisor X U s)
          ((fst X U s ≫ X.hom).relativeDimensionFunction delta) (n - 1) :
        AlgebraicCycle (closure X U s) ℤ) := sorry

/-- The principal cycle of a rational function is the proper pushforward of its principal
cycle from the graph closure of any invertible-section representative. -/
theorem principal_eq_pushforward
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] (n : ℤ) (f : X.left.functionFieldˣ)
    (U : X.left.Opens) [Nonempty U] (s : Γ(X.left, U)ˣ)
    (hX : X.hom.relativeDimensionFunction delta (genericPoint X.left) = n)
    (hs : Units.map (X.left.germToFunctionField U).hom s = f) :
    @AlgebraicCycle.principal X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance f =
      AlgebraicCycle.map (fst X U s)
        ((fst X U s ≫ X.hom).relativeDimensionFunction delta)
        (X.hom.relativeDimensionFunction delta)
        (@AlgebraicCycle.principal (closure X U s)
          (LocallyOfFiniteType.isLocallyNoetherian (fst X U s ≫ X.hom)) inferInstance
          (function X U s f)) := sorry

/-- A principal cycle equals the zero-image cycle minus the infinity-image cycle obtained
from the graph closure of an invertible-section representative. -/
theorem principal_eq_zeroImage_sub_infinityImage
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ)
    [IsDimensionFunction delta] (X : Over S) [LocallyOfFiniteType X.hom]
    [IsIntegral X.left] (n : ℤ) (f : X.left.functionFieldˣ)
    (U : X.left.Opens) [Nonempty U] (s : Γ(X.left, U)ˣ)
    (hX : X.hom.relativeDimensionFunction delta (genericPoint X.left) = n)
    (hs : Units.map (X.left.germToFunctionField U).hom s = f) :
    @AlgebraicCycle.principal X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom) inferInstance f =
      (@Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom) (zeroImage X U s)
          (X.hom.relativeDimensionFunction delta) (n - 1) : AlgebraicCycle X.left ℤ) -
      (@Scheme.IdealSheafData.associatedCycle X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom) (infinityImage X U s)
          (X.hom.relativeDimensionFunction delta) (n - 1) :
        AlgebraicCycle X.left ℤ) := sorry

end AlgebraicGeometry.RationalFunctionGraph
