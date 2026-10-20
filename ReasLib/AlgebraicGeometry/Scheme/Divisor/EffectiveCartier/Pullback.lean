/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.AssociatedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.WeaklyAssociatedPoints

/-!
# Pullbacks of effective Cartier divisors

This file defines when the inverse image of ideal-sheaf data determines an
effective Cartier divisor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {S S' : Scheme.{u}}

/-- The pullback of ideal-sheaf data along a scheme morphism is defined when its inverse-image
closed subscheme is an effective Cartier divisor. -/
def pullbackDefined (D : S.IdealSheafData) (f : S' ⟶ S) : Prop :=
  AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι

/-- Pullback-definedness is equivalent to the inverse-image closed subscheme being an effective
Cartier divisor. -/
theorem pullbackDefined_iff (D : S.IdealSheafData) (f : S' ⟶ S) :
    pullbackDefined D f ↔
      AlgebraicGeometry.IsEffectiveCartierDivisor (D.comap f).subschemeι :=
  Iff.rfl

/-- If every weakly associated point of the source maps outside an effective Cartier divisor,
then its pullback is defined. -/
theorem pullbackDefined_of_weakAss_outside_support
    {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hweak : ∀ x : X, x ∈ X.weakAss → f.base x ∉ D.support) :
    pullbackDefined D f := sorry

/-- The pullback of an effective Cartier divisor along a dominant morphism between integral
schemes is defined. -/
theorem pullbackDefined_of_isIntegral_of_isDominant
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
    (D : Y.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    pullbackDefined D f := sorry

/-- If a scheme is reduced and all of its generic points map outside an effective Cartier
divisor, then the divisor's pullback is defined. -/
theorem pullbackDefined_of_genericPoints_outside_support_of_isReduced
    {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hgeneric : ∀ ξ : X, ξ ∈ genericPoints X → f.base ξ ∉ D.support) :
    pullbackDefined D f := sorry

/-- If a locally Noetherian scheme's associated points map outside an effective Cartier
divisor, then the divisor's pullback is defined. -/
theorem pullbackDefined_of_associatedPoints
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hassoc : ∀ x : X, x ∈ X.associatedPoints → f.base x ∉ D.support) :
    pullbackDefined D f := sorry

/-- If a locally Noetherian scheme has no embedded points and all of its generic points map
outside an effective Cartier divisor, then the divisor's pullback is defined. -/
theorem pullbackDefined_of_genericPoints_of_noEmbeddedPoints
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι]
    (hembedded : X.embeddedPoints = (∅ : Set X))
    (hgeneric : ∀ ξ : X, ξ ∈ genericPoints X → f.base ξ ∉ D.support) :
    pullbackDefined D f := sorry

/-- The pullback of an effective Cartier divisor along a flat morphism is defined. -/
theorem pullbackDefined_of_flat
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (D : Y.IdealSheafData)
    [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] :
    pullbackDefined D f := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
