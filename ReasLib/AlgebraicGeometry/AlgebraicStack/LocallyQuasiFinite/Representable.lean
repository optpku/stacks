module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyQuasiFinite
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property

/-!
# Representable locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is locally
quasi-finite on scheme-slice tests if and only if it is locally of finite type
and has discrete field fibers.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- A morphism of algebraic stacks representable by algebraic spaces is locally
quasi-finite on scheme-slice tests of algebraic spaces if and only if it is
locally of finite type and every field-valued 2-fibre has discrete space of
points. -/
@[stacks 06UA]
theorem has_locallyQuasiFinite_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.LocallyQuasiFinite S) f ↔
      AlgebraicStack.LocallyOfFiniteType f ∧ AlgebraicStack.discreteFieldFibers f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
