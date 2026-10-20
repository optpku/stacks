/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Lifting
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/-
Lemma 37.81.1: for affine schemes, a morphism is a closed immersion exactly when it
has the right lifting property against `Spec.map φ : Spec B ⟶ Spec A` for every injective
commutative-ring morphism `φ : A ⟶ B`; this encodes the displayed square and its diagonal
lift making both triangles commute.
-/
@[stacks 0H2P] #check
  (AlgebraicGeometry.IsClosedImmersion.iff_hasLiftingProperty_spec_injective :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
      [AlgebraicGeometry.IsAffine Y] (f : X ⟶ Y),
      AlgebraicGeometry.IsClosedImmersion f ↔
        ∀ {A B : CommRingCat.{u}} (φ : A ⟶ B), Function.Injective φ →
          HasLiftingProperty (AlgebraicGeometry.Spec.map φ) f)
