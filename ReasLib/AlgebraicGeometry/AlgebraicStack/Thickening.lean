module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Immersion

/-!
# Thickenings of algebraic stacks

A morphism of algebraic stacks is a thickening when it is a closed immersion
and surjective on associated points, so the source is a closed substack whose
associated point space agrees with the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Groupoids.Hom (ClosedImmersion)
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism of algebraic stacks is a thickening if it is a closed immersion
and the induced map of associated point spaces is surjective. -/
class IsThickening {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') : Prop
    extends ClosedImmersion i, Surjective i

/-- A closed immersion of algebraic stacks that is surjective on associated
points is a thickening. -/
instance instIsThickening {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X')
    [ClosedImmersion i] [Surjective i] : IsThickening i where
  toClosedImmersion := inferInstance
  toSurjective := inferInstance

/-- Being a thickening is equivalent to being both a closed immersion and
surjective on associated point spaces. -/
theorem isThickening_iff {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') :
    IsThickening i ↔ ClosedImmersion i ∧ Surjective i := sorry

namespace IsThickening

/-- The identity morphism of an algebraic stack is a thickening. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    IsThickening (𝟙 X) :=
  inferInstance

/-- A thickening is a closed immersion that is surjective on associated point
spaces. -/
theorem spec {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    ClosedImmersion i ∧ Surjective i := sorry

/-- A closed immersion of algebraic stacks is a thickening if and only if
it is surjective on associated point spaces. -/
theorem iff_surjective {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [ClosedImmersion i] :
    IsThickening i ↔ Surjective i := sorry

/-- A thickening induces a surjective map of associated point spaces. -/
theorem points_surjective {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    Function.Surjective (Points.map i) := sorry

/-- A thickening induces a bijective map of associated point spaces. -/
theorem points_bijective {S : Scheme.{u}} {X X' : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack X'] (i : X ⟶ X') [IsThickening i] :
    Function.Bijective (Points.map i) := sorry

end IsThickening

end AlgebraicGeometry.AlgebraicStack
