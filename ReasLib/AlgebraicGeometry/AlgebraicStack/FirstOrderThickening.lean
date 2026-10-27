/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Substack
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FirstOrderThickening

/-!
# First-order thickenings of algebraic stacks

First-order substacks are replete full subcategories whose canonical inclusions
are closed immersions and first-order thickenings of groupoid fibrations.
The map-level presentation property also records full faithfulness.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is a first-order thickening presentation when
its total functor is full and faithful and it is a first-order thickening of
groupoid fibrations. -/
class IsFirstOrderThickening {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') : Prop
    extends Groupoids.Hom.IsFirstOrderThickening i where
  /-- The underlying total functor is full. -/
  full : (toFunctor i).Full
  /-- The underlying total functor is faithful. -/
  faithful : (toFunctor i).Faithful

namespace IsFirstOrderThickening

/-- A morphism of algebraic stacks is a first-order thickening presentation if
and only if it is a first-order thickening of groupoid fibrations and its total
functor is full and faithful. -/
theorem iff_full_faithful {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') :
    IsFirstOrderThickening i ↔
      Groupoids.Hom.IsFirstOrderThickening i ∧
        (toFunctor i).Full ∧ (toFunctor i).Faithful := sorry

/-- The total functor of a first-order thickening presentation is full. -/
instance instFull {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [h : IsFirstOrderThickening i] : (toFunctor i).Full :=
  h.full

/-- The total functor of a first-order thickening presentation is faithful. -/
instance instFaithful {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [h : IsFirstOrderThickening i] : (toFunctor i).Faithful :=
  h.faithful

/-- The identity morphism of an algebraic stack is a first-order thickening
presentation. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsFirstOrderThickening (𝟙 X) :=
  sorry

/-- A first-order thickening presentation of algebraic stacks is a closed
immersion. -/
instance instClosedImmersion {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [IsFirstOrderThickening i] : Groupoids.Hom.ClosedImmersion i :=
  sorry

end IsFirstOrderThickening

/-- A replete full subcategory of an algebraic stack is a first-order substack
when its canonical inclusion is a closed immersion and a first-order thickening
of groupoid fibrations. -/
def IsFirstOrderSubstack {S : Scheme.{u}} (X' : GroupoidsOver S)
    [AlgebraicStack X'] (P : ObjectProperty X'.total)
    [P.IsClosedUnderIsomorphisms]
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X'.p))
    [AlgebraicStack (Substack.category X' P h)] : Prop :=
  Groupoids.Hom.ClosedImmersion (Substack.inclusion X' P h) ∧
    Groupoids.Hom.IsFirstOrderThickening (Substack.inclusion X' P h)

/-- Being a first-order substack is equivalent to the closed-immersion and
first-order-thickening conditions on the same canonical inclusion. -/
theorem isFirstOrderSubstack_iff {S : Scheme.{u}} (X' : GroupoidsOver S)
    [AlgebraicStack X'] (P : ObjectProperty X'.total)
    [P.IsClosedUnderIsomorphisms]
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X'.p))
    [AlgebraicStack (Substack.category X' P h)] :
    IsFirstOrderSubstack X' P h ↔
      Groupoids.Hom.ClosedImmersion (Substack.inclusion X' P h) ∧
        Groupoids.Hom.IsFirstOrderThickening (Substack.inclusion X' P h) :=
  Iff.rfl

/-- A replete full subcategory of an algebraic stack is a first-order substack
if and only if its canonical inclusion is a first-order thickening presentation. -/
theorem isFirstOrderSubstack_iff_inclusion {S : Scheme.{u}} (X' : GroupoidsOver S)
    [AlgebraicStack X'] (P : ObjectProperty X'.total)
    [P.IsClosedUnderIsomorphisms]
    (h : Functor.IsFibered.InGroupoids (P.ι ⋙ X'.p))
    [AlgebraicStack (Substack.category X' P h)] :
    IsFirstOrderSubstack X' P h ↔
      IsFirstOrderThickening (Substack.inclusion X' P h) := sorry

end AlgebraicGeometry.AlgebraicStack
