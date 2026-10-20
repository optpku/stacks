/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Surjective-and-flat base loci of morphisms of algebraic spaces

The intersection of the flat base locus with the locus whose fibres lie in
the image gives a concrete open subspace of the base. A test morphism factors
through this open precisely when the induced morphism is surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat

/-- The set of points of `Z` over which the fibre of `q` is contained in the
image of `f`, as the complement of the image under `q` of the complement of
the image of `f`. -/
def surjectiveLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map q '' (Set.range (Points.map f))ᶜ)ᶜ

/-- The set of points of `Z` over which `f` is flat on the fibre in `X` and
the fibre of `q` is contained in the image of `f`. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  Flat.baseLocusPointsSet f q ∩ surjectiveLocusPointsSet f q

/-- The surjective-and-flat base locus of the triangle is open in `Points Z`
when `f ≫ q` is locally of finite presentation, flat, and closed, and `q` is
locally of finite type and closed. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The surjective-and-flat base locus of the triangle, as an open of
`Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is surjective and flat after base change to the point. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    OpenSubspace Z :=
  OpenSubspace.fromOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the surjective-and-flat base locus if and only if
`f` is flat at every point of `X` above it and the fibre of `q` over it is
contained in the image of `f`. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q]
    (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → FlatAt f x) ∧
        ∀ y : Points Y, Points.map q y = z → ∃ x : Points X, Points.map f x = y :=
  sorry

/-- Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite presentation, flat, and closed, and that `q` is locally of finite type
and closed. Then a morphism `g : Z' ⟶ Z` factors through the open subspace
`baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is surjective and flat. -/
@[stacks 05XC]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Surjective (overBaseChange f q g) ∧ Flat (overBaseChange f q g) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat
