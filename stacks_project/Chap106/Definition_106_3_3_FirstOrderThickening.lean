/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap76.Lemma_76_18_1_Thickening
public import stacks_project.Chap94.Definition_94_12_1_Representable
public import stacks_project.Chap100.Definition_100_9_1_Immersion
public import stacks_project.Chap100.Lemma_100_9_10_Substack

/-!
# First-order thickenings of algebraic stacks

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` is a
first-order thickening in the sense of Properties of Stacks, Section 100.3
when it is representable by algebraic spaces and every representing morphism
of algebraic spaces is a first-order thickening. An algebraic stack `X'` is a
first-order thickening of an algebraic stack `X` when the inclusion `X ⟶ X'`
is strictly full and such a 100.3 first-order thickening.
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

namespace AlgebraicGeometry.AlgebraicStack

/-- An inclusion `i : X ⟶ X'` of algebraic stacks is a first-order thickening
when it presents `X` as a strictly full subcategory of `X'` and is a
first-order thickening in the sense of Properties of Stacks, Section 100.3. -/
class IsFirstOrderThickening {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') : Prop
    extends Groupoids.Hom.IsFirstOrderThickening i,
      Groupoids.Hom.IsStrictlyFull i

namespace IsFirstOrderThickening

/-- The identity 1-morphism of an algebraic stack is a first-order
thickening. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsFirstOrderThickening (𝟙 X) :=
  sorry

/-- A strictly full 1-morphism of algebraic stacks which is a first-order
thickening in the sense of Section 100.3 is a first-order thickening of
algebraic stacks. -/
instance of_hom {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [h_fot : Groupoids.Hom.IsFirstOrderThickening i]
    [h_full : Groupoids.Hom.IsStrictlyFull i] : IsFirstOrderThickening i where
  toIsFirstOrderThickening := h_fot
  toIsStrictlyFull := h_full

/-- An inclusion of algebraic stacks is a first-order thickening if and only if
it is strictly full and a first-order thickening in the sense of Section
100.3. -/
theorem iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') :
    IsFirstOrderThickening i ↔
      Groupoids.Hom.IsStrictlyFull i ∧
        Groupoids.Hom.IsFirstOrderThickening i := sorry

/-- A first-order thickening of algebraic stacks is a strictly full closed
immersion whose scheme-slice representing morphisms are first-order
thickenings of algebraic spaces. -/
theorem spec {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [IsFirstOrderThickening i] :
    Groupoids.Hom.ClosedImmersion i ∧ Groupoids.Hom.IsStrictlyFull i ∧
      Groupoids.Hom.has (@AlgebraicSpace.IsFirstOrderThickening S) i :=
  sorry

/-- A first-order thickening of algebraic stacks is a closed immersion. -/
instance instClosedImmersion {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [IsFirstOrderThickening i] : Groupoids.Hom.ClosedImmersion i :=
  sorry

/-- The inclusion of a closed substack is a first-order thickening of algebraic
stacks as soon as it is a first-order thickening in the sense of Section
100.3. -/
instance of_closedSubstack {S : Scheme.{u}} {X' : GroupoidsOver S}
    [AlgebraicStack X'] (X : ClosedSubstack X')
    [h : Groupoids.Hom.IsFirstOrderThickening X.ι] :
    IsFirstOrderThickening X.ι where
  toIsFirstOrderThickening := h
  toIsStrictlyFull := X.isStrictlyFull

end IsFirstOrderThickening

end AlgebraicGeometry.AlgebraicStack
