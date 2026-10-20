/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.FlatPullback.BaseChange

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits AlgebraicGeometry.AlgebraicSpace.Hom

universe u

/- Lemma 82.11.1. Flat pullback commutes with proper pushforward on cycles
in a cartesian square of good algebraic spaces; the base-changed morphisms
are proper and flat of the same relative dimension, respectively. -/
@[stacks 0EPD] #check (AlgebraicGeometry.AlgebraicSpace.Hom.flatPullbackHom_comp_properPushforwardHom :
    ∀ {S : Scheme.{u}}
    {B X Y X' Y' : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (pX : X ⟶ B) [QuasiSeparated pX] [LocallyOfFiniteType pX]
    (pY : Y ⟶ B) [QuasiSeparated pY] [LocallyOfFiniteType pY]
    (pY' : Y' ⟶ B) [QuasiSeparated pY'] [LocallyOfFiniteType pY']
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiSeparated (g' ≫ pX)] [LocallyOfFiniteType (g' ≫ pX)]
    (square : IsPullback g' f' f g) (r : ℕ)
    [Proper f] [Flat g] [RelativeDimension g r]
    (hf : f ≫ pY = pX) (hg : g ≫ pY = pY')
    (hf' : f' ≫ pY' = g' ≫ pX) (k : ℤ),
    -- Local instance justification (proof-local temporary data): The over-base equation transfers local finite type to the composite needed for cancellation.
    letI : LocallyOfFiniteType (g ≫ pY) := by rw [hg]; infer_instance
    -- Local instance justification (proof-local temporary data): Cancellation supplies local finite type of the morphism whose exact relative dimension is transferred.
    letI : LocallyOfFiniteType g := LocallyOfFiniteType.of_comp g pY
    -- Local instance justification (proof-local temporary data): The explicit cartesian square supplies properness needed for the base-changed pushforward.
    letI : Proper f' := Proper.of_isPullback square inferInstance
    -- Local instance justification (proof-local temporary data): The flipped cartesian square supplies flatness needed for the base-changed pullback.
    letI : Flat g' := Flat.of_isPullback square.flip inferInstance
    -- Local instance justification (proof-local temporary data): Exact relative dimension transferred along the square supplies the degree of the base-changed pullback.
    letI : RelativeDimension g' r := RelativeDimension.of_isPullback square.flip inferInstance
    (flatPullbackHom pY pY' δ g r hg k).comp
        (properPushforwardHom pX pY δ f hf k) =
      (properPushforwardHom (g' ≫ pX) pY' δ f' hf' (k + (r : ℤ))).comp
        (flatPullbackHom pX (g' ≫ pX) δ g' r rfl k))
