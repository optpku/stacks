/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Lemma_67_14_1_Quotient
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# First-order thickenings of algebraic spaces

A morphism of algebraic spaces is a first-order thickening when it is a closed
immersion whose associated ideal sheaf has square zero, in the sense that the
ideal-sheaf action of `I` on itself vanishes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is a first-order thickening if it is a closed
immersion whose associated ideal sheaf acts trivially on itself. -/
class IsFirstOrderThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') : Prop extends IsClosedImmersion i where
  /-- The associated ideal sheaf has square zero. -/
  square_zero :
    Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i) = 0

/-- A morphism of algebraic spaces is a first-order thickening if and only if it
is a closed immersion whose associated ideal sheaf acts trivially on itself. -/
theorem isFirstOrderThickening_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') :
    IsFirstOrderThickening i ↔
      IsClosedImmersion i ∧
        Modules.idealAction (Hom.idealSheafSubobject i) (Hom.idealSheaf i) = 0 :=
  sorry

namespace IsFirstOrderThickening

/-- The identity morphism of an algebraic space is a first-order thickening. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsFirstOrderThickening (𝟙 X) :=
  sorry

/-- A first-order thickening of algebraic spaces is a closed immersion. -/
instance instIsClosedImmersion {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [h : IsFirstOrderThickening i] : IsClosedImmersion i :=
  h.toIsClosedImmersion

/-- A first-order thickening of algebraic spaces is a thickening. -/
instance instIsThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsFirstOrderThickening i] : IsThickening i :=
  sorry

end IsFirstOrderThickening

end AlgebraicGeometry.AlgebraicSpace
