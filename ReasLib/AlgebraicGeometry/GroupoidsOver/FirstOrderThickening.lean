/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.FirstOrder
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# First-order thickenings of groupoid fibrations

A representable morphism of groupoid fibrations is a first-order thickening
when every scheme-slice representing morphism is a first-order thickening
of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A 1-morphism of categories fibred in groupoids over `Over S` is a
first-order thickening when it is representable by algebraic spaces and every
representing morphism `fy : Fy ⟶ ofOver U` is a first-order thickening of
algebraic spaces. -/
class IsFirstOrderThickening {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) : Prop where
  /-- The 1-morphism is representable by algebraic spaces. -/
  representable : relativelyRepresentableByAlgebraicSpaces f
  /-- Every representing morphism of algebraic spaces is a first-order
  thickening. -/
  of_represents : ∀ ⦃U : Over S⦄ (y : GroupoidsOver.slice U ⟶ Y)
    (Fy : AlgebraicSpace S) (fy : Fy ⟶ AlgebraicSpace.ofOver U),
    RepresentsBaseChange f y Fy fy → AlgebraicSpace.IsFirstOrderThickening fy

namespace IsFirstOrderThickening

/-- The identity 1-morphism of a category fibred in groupoids is a first-order
thickening. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    IsFirstOrderThickening (𝟙 X) :=
  sorry

/-- A representing morphism of algebraic spaces for a first-order thickening of
groupoid fibrations is a first-order thickening. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [IsFirstOrderThickening f] {U : Over S} (y : GroupoidsOver.slice U ⟶ Y)
    {Fy : AlgebraicSpace S} {fy : Fy ⟶ AlgebraicSpace.ofOver U}
    (h : RepresentsBaseChange f y Fy fy) :
    AlgebraicSpace.IsFirstOrderThickening fy := sorry

/-- A first-order thickening of groupoid fibrations is representable by
algebraic spaces. -/
theorem relativelyRepresentable {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [IsFirstOrderThickening f] :
    relativelyRepresentableByAlgebraicSpaces f := sorry

/-- A 1-morphism is a first-order thickening if and only if it is representable
by algebraic spaces and has the algebraic-space first-order-thickening
property in the sense of scheme-slice tests. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y) :
    IsFirstOrderThickening f ↔ relativelyRepresentableByAlgebraicSpaces f ∧
      has (@AlgebraicSpace.IsFirstOrderThickening S) f := sorry

/-- A first-order thickening of groupoid fibrations has the algebraic-space
first-order-thickening property on scheme-slice representing morphisms. -/
theorem has_isFirstOrderThickening {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [IsFirstOrderThickening f] :
    has (@AlgebraicSpace.IsFirstOrderThickening S) f := sorry

/-- A first-order thickening of groupoid fibrations is a closed immersion. -/
instance instClosedImmersion {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (f : X ⟶ Y) [IsFirstOrderThickening f] : ClosedImmersion f :=
  sorry

/-- A first-order thickening of algebraic spaces induces a first-order
thickening of the associated groupoid fibrations. -/
instance of_algebraicSpace {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [AlgebraicSpace.IsFirstOrderThickening i] :
    IsFirstOrderThickening (AlgebraicSpace.toGroupoids.map i) :=
  sorry

end IsFirstOrderThickening

end AlgebraicGeometry.Groupoids.Hom

