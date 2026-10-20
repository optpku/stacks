/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.Lifting
import StacksCheckRecall

/-!
# Uniqueness of lifts for formally unramified morphisms of algebraic spaces

A formally unramified morphism of algebraic spaces over a scheme `S` admits at
most one lift through an arbitrary first-order thickening of algebraic spaces
over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.14.3: If `f : X ⟶ Y` is a formally unramified morphism of algebraic
spaces over a scheme `S`, then a solid commutative square against any first-order
thickening `i : T ⟶ T'` of algebraic spaces over `S` admits at most one dotted
lift `T' ⟶ X`. -/
@[stacks 05ZY] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.subsingleton_liftStruct :
    ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyUnramified f] (i : T ⟶ T') [IsFirstOrderThickening i]
    (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
    Subsingleton sq.LiftStruct)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.hom_ext :
    ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyUnramified f] {i : T ⟶ T'} [IsFirstOrderThickening i]
    {a₁ a₂ : T' ⟶ X} (hT : i ≫ a₁ = i ≫ a₂) (hY : a₁ ≫ f = a₂ ≫ f),
    a₁ = a₂)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.iff_subsingleton_liftStruct :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y),
    FormallyUnramified f ↔
      ∀ {T T' : AlgebraicSpace S} (i : T ⟶ T') [IsFirstOrderThickening i]
        (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
        Subsingleton sq.LiftStruct)
