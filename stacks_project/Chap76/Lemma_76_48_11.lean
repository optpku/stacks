module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_48_11_KoszulLocus

/-!
# Koszul locus of a morphism of algebraic spaces over a triangle

In a commutative triangle of algebraic spaces `X ⟶ Y` over `Z` with both
structure maps flat and locally of finite presentation, the Koszul locus of
`f` is an open subspace of `X`, and formation of this open commutes with
arbitrary base change of the triangle.

The algebraic-space `Flat` owner currently rebuilds the broken
`Chap66.Lemma_66_4_2_Comparison`. This file reconstructs the étale-scheme-square
flatness class so the labeled theorems can assume `Flat` of `p` and `q`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is flat if every
commutative square with étale vertical arrows from schemes has flat top
arrow. -/
class Flat {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has flat top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Flat h.left

/-- A morphism of algebraic spaces is flat if and only if every commutative
square with étale vertical arrows from schemes has flat top arrow. -/
theorem flat_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Flat f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Flat h.left :=
  sorry

namespace Flat

/-- The identity morphism of an algebraic space is flat. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Flat (𝟙 X) :=
  sorry

end Flat

/-- Lemma 76.48.11 (1): Let `S` be a scheme. Consider a commutative triangle of
algebraic spaces over `S` given by `f : X ⟶ Y`, `p : X ⟶ Z`, and `q : Y ⟶ Z`
with `f ≫ q = p`. Assume that both `p` and `q` are flat and locally of finite
presentation. Then `(koszulLocus f).pointsSet` is the set of points of
`Points X` at which `f` is Koszul. -/
@[stacks 06CA]
theorem koszulLocus_pointsSet_eq_of_over {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (h_over : f ≫ q = p) [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q] :
    (koszulLocus f).pointsSet = {x | KoszulAt f x} :=
  sorry

/-- Lemma 76.48.11 (2): Let `S` be a scheme. Consider a commutative triangle of
algebraic spaces over `S` given by `f : X ⟶ Y`, `p : X ⟶ Z`, and `q : Y ⟶ Z`
with `f ≫ q = p`. Assume that both `p` and `q` are flat and locally of finite
presentation. For any morphism `g : Z' ⟶ Z` of algebraic spaces over `S`, if
`f' : X' ⟶ Y'` is the base change of `f` by `g`, then
`(koszulLocus f').pointsSet` is the inverse image of
`(koszulLocus f).pointsSet` under the projection `X' ⟶ X`. -/
@[stacks 06CA]
theorem koszulLocus_pointsSet_eq_preimage_of_baseChange {S : Scheme.{u}}
    {X Y Z X' Y' Z' : AlgebraicSpace S} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (f' : X' ⟶ Y') (p' : X' ⟶ Z') (q' : Y' ⟶ Z') (gX : X' ⟶ X) (gY : Y' ⟶ Y)
    (g : Z' ⟶ Z) (h_over : f ≫ q = p) (h_over' : f' ≫ q' = p')
    (sq : CommSq f' gX gY f) (hX : IsPullback gX p' p g)
    (hY : IsPullback gY q' q g) [Flat p] [LocallyOfFinitePresentation p]
    [Flat q] [LocallyOfFinitePresentation q] :
    (koszulLocus f').pointsSet = Points.map gX ⁻¹' (koszulLocus f).pointsSet :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
