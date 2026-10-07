module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap76.Lemma_76_9_2_Thickening

/-!
# Pushouts of algebraic spaces along a thickening and an affine morphism

A thickening and an affine morphism of algebraic spaces over a scheme `S` admit a
pushout in `AlgebraicSpace S`, and the canonical (and any isomorphic) morphism
`Y ⟶ Y ⨿_X X'` is a thickening.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

/-- A thickening and an affine morphism of algebraic spaces over `S` have a pushout in
the category of algebraic spaces over `S`. -/
instance instHasPushout {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] : HasPushout i f :=
  sorry

/-- The canonical morphism from the target of an affine morphism to the pushout along a
thickening is a thickening. -/
instance instInrIsThickening {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f] :
    IsThickening (pushout.inr i f) :=
  sorry

/-- In any pushout square of a thickening along an affine morphism, the morphism
`Y ⟶ Y'` is a thickening. -/
theorem isThickening_inr {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    [IsThickening i] [Affine f] (h : IsPushout i f i' g) : IsThickening g :=
  sorry

/-- A thickening of algebraic spaces is representable by schemes. -/
theorem relativelyRepresentable_of_isThickening {S : Scheme.{u}} {X X' : AlgebraicSpace S}
    (i : X ⟶ X') [IsThickening i] : yoneda.relativelyRepresentable i :=
  sorry

/-- An affine morphism of algebraic spaces is representable by schemes. -/
theorem relativelyRepresentable_of_affine {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Affine f] : yoneda.relativelyRepresentable f :=
  sorry

/-- In a pushout square of a thickening along an affine morphism, the morphism
`X' ⟶ Y'` is representable by schemes. -/
theorem relativelyRepresentable_inl {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    [IsThickening i] [Affine f] (h : IsPushout i f i' g) :
    yoneda.relativelyRepresentable i' :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
