module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SurjectiveOnObjects
public import ReasLib.AlgebraicGeometry.GroupoidsOver.MorphismProperty
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Surjective on objects versus surjective morphisms of groupoid fibrations

A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that is
representable by algebraic spaces is surjective on objects if and only if it is
surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

namespace SurjectiveOnObjects

/-- A 1-morphism of categories fibred in groupoids over `(Sch/S)_fppf` that
is representable by algebraic spaces is surjective on objects if and only if
it is surjective. -/
@[stacks 06D7]
theorem iff_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    SurjectiveOnObjects p ↔ Surjective p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is surjective is
surjective on objects. -/
instance of_surjective {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) [Surjective p] :
    SurjectiveOnObjects p :=
  sorry

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces is surjective on objects if and only if it has the
surjectivity property on every algebraic-space base change. -/
theorem iff_has {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p) :
    SurjectiveOnObjects p ↔ has (@AlgebraicSpace.Surjective S) p :=
  sorry

end SurjectiveOnObjects

namespace Surjective

/-- A 1-morphism of categories fibred in groupoids that is representable by
algebraic spaces and surjective on objects is surjective. -/
theorem of_surjectiveOnObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) (hp : relativelyRepresentableByAlgebraicSpaces p)
    [SurjectiveOnObjects p] :
    Surjective p :=
  sorry

end Surjective

end AlgebraicGeometry.Groupoids.Hom
