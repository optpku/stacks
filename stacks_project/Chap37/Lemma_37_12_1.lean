/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.InfinitesimalLifting

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.12.1: for a locally finite type morphism `f : X ⟶ S` over a locally
Noetherian scheme and a point `x : X`, smoothness of `f` at `x` is equivalent to the
infinitesimal lifting property at `x` for square-zero extensions of local rings, for small
extensions, and for small extensions whose induced residue-field map at the closed point is
an isomorphism. -/
@[stacks 02HX] #check
  (AlgebraicGeometry.Scheme.Hom.smoothAt_tfae_infinitesimalLifting :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
      [IsLocallyNoetherian S] [LocallyOfFiniteType f],
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
        ])

end AlgebraicGeometry.Scheme.Hom
