/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale.Lifting
import StacksCheckRecall

/-!
# Unique lifts for formally étale morphisms of algebraic spaces

A formally étale morphism of algebraic spaces over a scheme `S` admits
exactly one lift through an arbitrary first-order thickening of algebraic
spaces over `Y`. Equivalently, the affineness hypothesis in the functor-of-points
definition may be dropped.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 76.16.3: If `f : X ⟶ Y` is a formally étale morphism of algebraic
spaces over a scheme `S`, then a solid commutative square against any first-order
thickening `i : T ⟶ T'` of algebraic spaces over `Y` admits exactly one dotted
lift `T' ⟶ X`. -/
@[stacks 0611] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.existsUnique_lift :
    ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyEtale f] (i : T ⟶ T') [IsFirstOrderThickening i]
    (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
    Nonempty (Unique sq.LiftStruct))

#check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.hasLiftingProperty :
    ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyEtale f] (i : T ⟶ T') [IsFirstOrderThickening i],
    HasLiftingProperty i f)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.hom_ext :
    ∀ {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyEtale f] {i : T ⟶ T'} [IsFirstOrderThickening i]
    {a₁ a₂ : T' ⟶ X} (hT : i ≫ a₁ = i ≫ a₂) (hY : a₁ ≫ f = a₂ ≫ f),
    a₁ = a₂)

#check (AlgebraicGeometry.AlgebraicSpace.FormallyEtale.iff_existsUnique_lift :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    FormallyEtale f ↔
      ∀ {T T' : AlgebraicSpace S} (i : T ⟶ T') [IsFirstOrderThickening i]
        (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
        Nonempty (Unique sq.LiftStruct))
