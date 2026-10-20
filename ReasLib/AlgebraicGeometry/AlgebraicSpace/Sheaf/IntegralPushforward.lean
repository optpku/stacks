/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Exactness of small étale abelian pushforward along integral morphisms

For an integral morphism of algebraic spaces, the small étale abelian
direct image is exact, and the higher direct images vanish in positive degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIntegralHom f]

/-- The small étale abelian direct image along an integral morphism of algebraic spaces
is an exact functor. -/
@[stacks 0A4K]
theorem sheafPushforwardAbelian_exact_of_isIntegralHom :
    exactFunctor _ _ (sheafPushforwardAbelian f) :=
  sorry

/-- The small étale abelian direct image along an integral morphism of algebraic spaces
preserves finite colimits. -/
instance sheafPushforwardAbelian_preservesFiniteColimits_of_isIntegralHom :
    PreservesFiniteColimits (sheafPushforwardAbelian f) :=
  ((exactFunctor_iff (sheafPushforwardAbelian f)).mp
    (sheafPushforwardAbelian_exact_of_isIntegralHom f)).2

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- Every positive-degree higher direct image of an abelian sheaf along an integral
morphism of algebraic spaces is zero. -/
@[stacks 0A4K]
theorem higherDirectImage_isZero_of_isIntegralHom
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [(sheafPushforward AddCommGrpCat.{u + 1} f).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (p : ℕ) (hp : 0 < p) :
    IsZero (higherDirectImage f F p) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
