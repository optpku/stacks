module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import stacks_project.Chap66.Lemma_66_4_3_Comparison
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_34_3_FiberDimension

/-!
# Fibre dimensions after base change of algebraic spaces

In a fibre-product diagram of algebraic spaces, local fibre dimension is
invariant, while fibre-stalk dimension and residue-field transcendence degree
change by the same nonnegative integer.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.34.3 (1): Let `S` be a scheme and let
`g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, `g : Y' ⟶ Y` be a fibre-product
diagram of algebraic spaces over `S`. Let `x'` be a point of `X'`, and write
`x` for `Points.map g' x'`. If `f` is locally of finite type, then the
relative dimension of `f` at `x` equals the relative dimension of `f'` at
`x'`. -/
@[stacks 04NS]
theorem fiberDimensionAt_eq_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hpb : IsPullback g' f' f g)
    (x' : Points X') :
    fiberDimensionAt f' x' = fiberDimensionAt f (Points.map g' x') :=
  sorry

/-- Lemma 67.34.3 (2): In the same fibre-product diagram, with `f` locally of
finite type, the difference of the dimensions of the local rings of the fibres
of `f'` at `x'` and of `f` at `x = Points.map g' x'` equals the difference of
the residue-field transcendence degrees of `x/f(x)` and of `x'/f'(x')`, and
this common value is a nonnegative integer. -/
@[stacks 04NS]
theorem fiberStalkDimAt_sub_eq_residueFieldTrdegAt_sub_of_isPullback
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hpb : IsPullback g' f' f g) (x' : Points X') :
    ∃ n : ℕ,
      fiberStalkDimAt f' x' = fiberStalkDimAt f (Points.map g' x') + n ∧
        residueFieldTrdegAt f (Points.map g' x') =
          residueFieldTrdegAt f' x' + n :=
  sorry

/-- Lemma 67.34.3 (3): In the same fibre-product diagram, with `f` locally of
finite type, given points `x` of `X` and `y'` of `Y'` mapping to the same
point of `Y` there exists a point `x'` of `X'` mapping to both for which the
integer in (2) is `0`. -/
@[stacks 04NS]
theorem exists_point_fiberStalkDimAt_eq_and_residueFieldTrdegAt_eq_of_isPullback
    {S : Scheme.{u}} {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (hpb : IsPullback g' f' f g) (x : Points X) (y' : Points Y')
    (hxy : Points.map f x = Points.map g y') :
    ∃ x' : Points X',
      Points.map g' x' = x ∧
        Points.map f' x' = y' ∧
          fiberStalkDimAt f' x' = fiberStalkDimAt f x ∧
            residueFieldTrdegAt f' x' = residueFieldTrdegAt f x :=
  sorry

/-- In a fibre-product diagram, the dimension of the local ring of the fibre
does not decrease under pullback. -/
theorem fiberStalkDimAt_le_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hpb : IsPullback g' f' f g)
    (x' : Points X') :
    fiberStalkDimAt f (Points.map g' x') ≤ fiberStalkDimAt f' x' :=
  sorry

/-- In a fibre-product diagram, the residue-field transcendence degree at a
pullback point is at most that at its image. -/
theorem residueFieldTrdegAt_le_of_isPullback {S : Scheme.{u}}
    {X Y X' Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y') (hpb : IsPullback g' f' f g)
    (x' : Points X') :
    residueFieldTrdegAt f' x' ≤ residueFieldTrdegAt f (Points.map g' x') :=
  sorry

/-- The canonical pullback projection preserves relative dimension at a point. -/
theorem fiberDimensionAt_eq_of_pullback_snd {S : Scheme.{u}}
    {X Y Y' : AlgebraicSpace S} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) [HasPullback f g] (x' : Points (pullback f g)) :
    fiberDimensionAt (pullback.snd f g) x' =
      fiberDimensionAt f (Points.map (pullback.fst f g) x') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
