module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Representable.OnSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Flat
public import ReasLib.AlgebraicGeometry.GroupoidsOver.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.MorphismProperty.Local

/-!
# Scheme tests versus algebraic-space tests for representable morphisms

A property of morphisms of algebraic spaces that is fppf local on the target
and stable under base change may be tested on algebraic-space base changes of a
morphism of algebraic stacks representable by algebraic spaces, not only on
scheme base changes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

/-- Let `P` be a property of morphisms of algebraic spaces that is
fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Then `f` has `P`
if and only if for every algebraic space `Z` and morphism `Z.toGroupoids ⟶ Y`,
every morphism of algebraic spaces representing `Z ×_Y X ⟶ Z` has `P`. -/
@[stacks 04XC]
theorem has_iff_forall_algebraicSpace {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f) :
    has P f ↔
      ∀ (Z : AlgebraicSpace S) (z : Z.toGroupoids ⟶ Y) (W : AlgebraicSpace S)
        (w : W ⟶ Z), RepresentsTwoFibreProductOnSpace f z W Z w → P w :=
  sorry

/-- Let `P` be a property of morphisms of algebraic spaces that is
fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Let `W` be an
algebraic space and let `g : W.toGroupoids ⟶ Y` be surjective, locally of finite
presentation, and flat. If `v : V ⟶ W` represents the projection
`W ×_Y X ⟶ W`, then `f` has `P` if and only if `v` has `P`. -/
@[stacks 04XD]
theorem has_iff_of_covering {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    {W : AlgebraicSpace S} (g : W.toGroupoids ⟶ Y)
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {V : AlgebraicSpace S} {v : V ⟶ W}
    (hv : RepresentsTwoFibreProductOnSpace f g V W v) :
    has P f ↔ P v :=
  sorry

/-- Let `P` be a property of morphisms of algebraic spaces that is
fppf local on the target and stable under base change. Let `f : X ⟶ Y` be a
morphism of algebraic stacks representable by algebraic spaces. Let
`g : Z ⟶ Y` be a morphism of algebraic stacks which is representable by
algebraic spaces, surjective, flat, and locally of finite presentation. Set
`W = Z ×_Y X`. Then `f` has `P` if and only if the projection
`TwoFibreProduct.fst g f : W ⟶ Z` has `P`. -/
@[stacks 06TY]
theorem has_iff_of_weak_covering {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (P : MorphismProperty (AlgebraicSpace S))
    [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget (AlgebraicSpace.fppfPrecoverage S)]
    {f : X ⟶ Y} (hf : relativelyRepresentableByAlgebraicSpaces f)
    (g : Z ⟶ Y) [Surjective g] [Flat g] [LocallyOfFinitePresentation g] :
    has P f ↔ has P (TwoFibreProduct.fst.{u + 1, u, u + 1, u} g f) :=
  sorry

end AlgebraicGeometry.Groupoids.Hom
