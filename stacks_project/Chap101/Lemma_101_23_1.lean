module

public import stacks_project.Chap67.Lemma_67_27_7_LocallyQuasiFinite
public import stacks_project.Chap100.Lemma_100_3_2_MorphismProperty
public import stacks_project.Chap101.Definition_101_23_2_LocallyQuasiFinite

/-!
# Representable locally quasi-finite morphisms of algebraic stacks

A morphism of algebraic stacks representable by algebraic spaces is locally
quasi-finite in the scheme-slice sense of algebraic spaces if and only if it is
locally of finite type and every field-valued 2-fibre has discrete space of
points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Lemma 101.23.1: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Assume
`f` is representable by algebraic spaces. The following are equivalent: `f` is
locally quasi-finite as in Properties of Stacks, Section 100.3, and `f` is
locally of finite type and for every morphism `Spec(k) ⟶ Y` where `k` is a
field the space `|Spec(k) ×_Y X|` is discrete. -/
@[stacks 06UA]
theorem has_locallyQuasiFinite_iff {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has (@AlgebraicSpace.LocallyQuasiFinite S) f ↔
      AlgebraicStack.LocallyOfFiniteType f ∧ AlgebraicStack.discreteFieldFibers f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that is
locally of finite type and has discrete field fibers is locally quasi-finite on
scheme-slice tests of algebraic spaces. -/
theorem has_locallyQuasiFinite_of {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    [AlgebraicStack.LocallyOfFiniteType f]
    (h : AlgebraicStack.discreteFieldFibers f) :
    has (@AlgebraicSpace.LocallyQuasiFinite S) f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that is
locally quasi-finite on scheme-slice tests of algebraic spaces is locally of
finite type. -/
theorem locallyOfFiniteType_of_has_locallyQuasiFinite
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : has (@AlgebraicSpace.LocallyQuasiFinite S) f) :
    AlgebraicStack.LocallyOfFiniteType f :=
  sorry

/-- A morphism of algebraic stacks representable by algebraic spaces that is
locally quasi-finite on scheme-slice tests of algebraic spaces has discrete
field fibers. -/
theorem discreteFieldFibers_of_has_locallyQuasiFinite
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y}
    (hf : relativelyRepresentableByAlgebraicSpaces f)
    (h : has (@AlgebraicSpace.LocallyQuasiFinite S) f) :
    AlgebraicStack.discreteFieldFibers f :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
