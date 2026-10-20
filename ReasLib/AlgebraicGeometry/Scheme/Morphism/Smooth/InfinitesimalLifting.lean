/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.RingTheory.RingHom.SmallExtension
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Artinian

/-!
# Infinitesimal lifting criterion for smoothness at a point
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- For a locally finite type morphism to a locally Noetherian scheme, smoothness at a point
is equivalent to the infinitesimal lifting property at that point for square-zero extensions,
small extensions, and small extensions inducing a bijection on the relevant residue fields. -/
theorem smoothAt_tfae_infinitesimalLifting {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    List.TFAE
      [ f.SmoothAt x
      , ∀ (B' B : Type u) [CommRing B'] [CommRing B]
          [IsLocalRing B'] [IsLocalRing B] (π : B' →+* B) [π.IsSquareZeroExtension]
          (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S),
          α ≫ f = Spec.map (CommRingCat.ofHom π) ≫ β →
            α (IsLocalRing.closedPoint B) = x →
              ∃ γ : Spec (CommRingCat.of B') ⟶ X,
                Spec.map (CommRingCat.ofHom π) ≫ γ = α ∧ γ ≫ f = β
      , ∀ (B' B : Type u) [CommRing B'] [CommRing B]
          [IsLocalRing B'] [IsLocalRing B] (π : B' →+* B) [π.IsSmallExtension]
          (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S),
          α ≫ f = Spec.map (CommRingCat.ofHom π) ≫ β →
            α (IsLocalRing.closedPoint B) = x →
              ∃ γ : Spec (CommRingCat.of B') ⟶ X,
                Spec.map (CommRingCat.ofHom π) ≫ γ = α ∧ γ ≫ f = β
      , ∀ (B' B : Type u) [CommRing B'] [CommRing B]
          [IsLocalRing B'] [IsLocalRing B] (π : B' →+* B) [π.IsSmallExtension]
          (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S),
          α ≫ f = Spec.map (CommRingCat.ofHom π) ≫ β →
            α (IsLocalRing.closedPoint B) = x →
              Function.Bijective (α.residueFieldMap (IsLocalRing.closedPoint B)).hom →
                ∃ γ : Spec (CommRingCat.of B') ⟶ X,
                  Spec.map (CommRingCat.ofHom π) ≫ γ = α ∧ γ ≫ f = β
      ] := sorry

/-- A locally finite type morphism to a locally Noetherian scheme is smooth exactly when every
commutative square over a small extension whose bottom morphism is finite type admits a lift. -/
theorem smooth_iff_smallExtensionLifting {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] :
    Smooth f ↔
      ∀ (B' B : Type u) [CommRing B'] [CommRing B]
        (π : B' →+* B) [π.IsSmallExtension]
        (α : Spec (CommRingCat.of B) ⟶ X) (β : Spec (CommRingCat.of B') ⟶ S)
        [FiniteType β],
        CommSq α (Spec.map (CommRingCat.ofHom π)) f β →
          ∃ γ : Spec (CommRingCat.of B') ⟶ X,
            Spec.map (CommRingCat.ofHom π) ≫ γ = α ∧ γ ≫ f = β := sorry

end AlgebraicGeometry.Scheme.Hom
