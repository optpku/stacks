/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.LiftingProperties.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyEtale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder

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

namespace AlgebraicGeometry.AlgebraicSpace.FormallyEtale

/-- If `f : X ⟶ Y` is a formally étale morphism of algebraic
spaces over a scheme `S`, then a solid commutative square against any first-order
thickening `i : T ⟶ T'` of algebraic spaces over `Y` admits exactly one dotted
lift `T' ⟶ X`. -/
@[stacks 0611]
theorem existsUnique_lift {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyEtale f] (i : T ⟶ T') [IsFirstOrderThickening i]
    (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b) :
    Nonempty (Unique sq.LiftStruct) :=
  sorry

/-- A formally étale morphism of algebraic spaces has the right lifting property
against every first-order thickening, with no affineness hypotheses. -/
instance hasLiftingProperty {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyEtale f] (i : T ⟶ T') [IsFirstOrderThickening i] :
    HasLiftingProperty i f :=
  sorry

/-- Two morphisms `T' ⟶ X` that agree after composition with a first-order
thickening `i : T ⟶ T'` and over `Y` are equal, when `X ⟶ Y` is formally
étale. -/
theorem hom_ext {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyEtale f] {i : T ⟶ T'} [IsFirstOrderThickening i]
    {a₁ a₂ : T' ⟶ X} (hT : i ≫ a₁ = i ≫ a₂) (hY : a₁ ≫ f = a₂ ≫ f) :
    a₁ = a₂ :=
  sorry

/-- A morphism of algebraic spaces is formally étale if and only if every solid
commutative square against a first-order thickening of algebraic spaces admits
exactly one dotted lift, with no affineness hypotheses. -/
theorem iff_existsUnique_lift {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔
      ∀ {T T' : AlgebraicSpace S} (i : T ⟶ T') [IsFirstOrderThickening i]
        (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
        Nonempty (Unique sq.LiftStruct) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyEtale
