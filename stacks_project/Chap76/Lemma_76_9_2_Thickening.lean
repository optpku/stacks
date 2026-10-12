/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Thickenings of algebraic spaces

A morphism of algebraic spaces is a thickening when it is a closed immersion and
surjective on associated points, matching the scheme-theoretic thickening class.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is a thickening if it is a closed immersion and
surjective on associated points. -/
class IsThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') : Prop
    extends IsClosedImmersion i, Surjective i

/-- A closed immersion of algebraic spaces that is surjective on associated points is a
thickening. -/
instance instIsThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X')
    [IsClosedImmersion i] [Surjective i] : IsThickening i where
  toIsClosedImmersion := inferInstance
  toSurjective := inferInstance

/-- Being a thickening is equivalent to being both a closed immersion and surjective on
associated points. -/
theorem isThickening_iff {S : Scheme.{u}} {X X' : AlgebraicSpace S} (i : X ⟶ X') :
    IsThickening i ↔ IsClosedImmersion i ∧ Surjective i := sorry

/-- The identity morphism of an algebraic space is a thickening. -/
instance IsThickening.id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    IsThickening (𝟙 X) := inferInstance

end AlgebraicGeometry.AlgebraicSpace
