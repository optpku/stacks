/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import ReasLib.AlgebraicGeometry.ChowGroup
public import ReasLib.AlgebraicGeometry.ChowGroup.FieldExtension.AlgebraicPullback
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Smooth.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine
public import ReasLib.RingTheory.Catenary.Field

/-!
# Rational points in Chow groups

This module records the degree-zero Chow class of a rational point of a scheme over a field,
and the finite-separable n-divisibility of a difference of two such classes.
-/

@[expose] public section

open CategoryTheory Limits
open scoped MonoidalCategory
open AlgebraicGeometry.FieldExtension

noncomputable section

universe u

namespace AlgebraicGeometry

namespace SchemeOverField

/-- A rational point has relative dimension zero over the constant-zero dimension
function on the spectrum of its base field. -/
theorem rationalPoint_relativeDimensionFunction_eq_zero
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
      (x.left (IsLocalRing.closedPoint k)) = 0 := sorry

end SchemeOverField

namespace ChowGroup

/-- The degree-zero Chow class represented by a rational point. -/
noncomputable def rationalPointClass
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    @ChowGroup X.left
      (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
        inferInstance
        (@AlgebraicGeometry.instUniversallyCatenarySpec k _
          (@instUniversallyCatenaryRingOfField.{u, u} k _)).toIsLocallyNoetherian)
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ)))
      (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction X.left
        (Spec (CommRingCat.of k)) X.hom
        (@AlgebraicGeometry.instUniversallyCatenarySpec k _
          (@instUniversallyCatenaryRingOfField.{u, u} k _))
        inferInstance (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
        (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)) 0 :=
  @chowClass X.left
    (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
      inferInstance
      (@AlgebraicGeometry.instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _)).toIsLocallyNoetherian)
    (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ)))
    (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction X.left
      (Spec (CommRingCat.of k)) X.hom
      (@AlgebraicGeometry.instUniversallyCatenarySpec k _
        (@instUniversallyCatenaryRingOfField.{u, u} k _))
      inferInstance (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
      (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)) 0
    (CycleGroup.point
      (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) 0
      (x.left (IsLocalRing.closedPoint k))
      (SchemeOverField.rationalPoint_relativeDimensionFunction_eq_zero X x))

/-- A rational-point class is the Chow class of its singleton point cycle. -/
theorem rationalPointClass_eq_chowClass
    {k : Type u} [Field k] (X : SchemeOverField k) [LocallyOfFiniteType X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    rationalPointClass X x =
      @chowClass X.left
        (@LocallyOfFiniteType.isLocallyNoetherian X.left (Spec (CommRingCat.of k)) X.hom
          inferInstance
          (@AlgebraicGeometry.instUniversallyCatenarySpec k _
            (@instUniversallyCatenaryRingOfField.{u, u} k _)).toIsLocallyNoetherian)
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ)))
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction X.left
          (Spec (CommRingCat.of k)) X.hom
          (@AlgebraicGeometry.instUniversallyCatenarySpec k _
            (@instUniversallyCatenaryRingOfField.{u, u} k _))
          inferInstance (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))
          (@instIsDimensionFunctionZero (Spec (CommRingCat.of k)) inferInstance inferInstance)) 0
        (CycleGroup.point
          (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of k) ↦ (0 : ℤ))) 0
          (x.left (IsLocalRing.closedPoint k))
          (SchemeOverField.rationalPoint_relativeDimensionFunction_eq_zero X x)) := sorry

/-- For two rational points on a geometrically irreducible smooth projective scheme over a
field `k`, their degree-zero Chow-class difference becomes divisible by an integer `n` after
some finite separable extension of `k`, provided `n` is invertible in `k`. -/
theorem rationalPointSub_divisible
    {k : Type u} [Field k] (X : SchemeOverField k)
    [GeometricallyIrreducible X.hom] [Smooth X.hom] [Projective X.hom]
    (x x' : 𝟙_ (SchemeOverField k) ⟶ X) (n : ℤ) (hn : IsUnit (n : k)) :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
      (_ : Algebra.IsSeparable k K)
      (z : @ChowGroup (pullback X.hom (specMap k K))
        (@LocallyOfFiniteType.isLocallyNoetherian (pullback X.hom (specMap k K))
          (Spec (CommRingCat.of K)) (pullback.snd X.hom (specMap k K)) inferInstance
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _)).toIsLocallyNoetherian)
        ((pullback.snd X.hom (specMap k K)).relativeDimensionFunction
          (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ)))
        (@Scheme.Hom.instIsDimensionFunctionRelativeDimensionFunction
          (pullback X.hom (specMap k K)) (Spec (CommRingCat.of K))
          (pullback.snd X.hom (specMap k K))
          (@AlgebraicGeometry.instUniversallyCatenarySpec K _
            (@instUniversallyCatenaryRingOfField.{u, u} K _))
          inferInstance (fun _ : Spec (CommRingCat.of K) ↦ (0 : ℤ))
          (@instIsDimensionFunctionZero (Spec (CommRingCat.of K)) inferInstance inferInstance)) 0),
      FieldExtension.algebraicExtensionPullback k K X 0
          (rationalPointClass X x - rationalPointClass X x') = n • z := sorry

end ChowGroup

end AlgebraicGeometry
