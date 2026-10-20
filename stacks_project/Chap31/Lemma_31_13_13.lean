/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback
import StacksCheckRecall

open AlgebraicGeometry

universe u

/- Lemma 31.13.13 (1): if every weakly associated point of `X` maps outside `D.support`, then
the pullback of the effective Cartier divisor `D` along `f` is defined. -/
@[stacks 02OO] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_of_weakAss_outside_support :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      (∀ x : X, x ∈ X.weakAss → f.base x ∉ D.support) →
        AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f)

/- Lemma 31.13.13 (2): the pullback of an effective Cartier divisor along a dominant morphism
between integral schemes is defined. -/
@[stacks 02OO] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_of_isIntegral_of_isDominant :
    ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsDominant f]
      (D : Y.IdealSheafData) [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f)

/- Lemma 31.13.13 (3): if `X` is reduced and all of its generic points map outside `D.support`,
then the pullback of the effective Cartier divisor `D` along `f` is defined. -/
@[stacks 02OO] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_of_genericPoints_outside_support_of_isReduced :
    ∀ {X Y : Scheme.{u}} [IsReduced X] (f : X ⟶ Y) (D : Y.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      (∀ ξ : X, ξ ∈ genericPoints X → f.base ξ ∉ D.support) →
        AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f)

/- Lemma 31.13.13 (4): if `X` is locally Noetherian and all of its associated points map
outside `D.support`, then the pullback of the effective Cartier divisor `D` along `f` is defined. -/
@[stacks 02OO] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_of_associatedPoints :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (D : Y.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      (∀ x : X, x ∈ X.associatedPoints → f.base x ∉ D.support) →
        AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f)

/- Lemma 31.13.13 (5): if `X` is locally Noetherian, has no embedded points, and all of its
generic points map outside `D.support`, then the pullback of the effective Cartier divisor `D`
along `f` is defined. -/
@[stacks 02OO] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_of_genericPoints_of_noEmbeddedPoints :
    ∀ {X Y : Scheme.{u}} [IsLocallyNoetherian X] (f : X ⟶ Y) (D : Y.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      X.embeddedPoints = (∅ : Set X) →
        (∀ ξ : X, ξ ∈ genericPoints X → f.base ξ ∉ D.support) →
          AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f)

/- Lemma 31.13.13 (6): the pullback of an effective Cartier divisor along a flat morphism is
defined. -/
@[stacks 02OO] #check
  (AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined_of_flat :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] (D : Y.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D f)
