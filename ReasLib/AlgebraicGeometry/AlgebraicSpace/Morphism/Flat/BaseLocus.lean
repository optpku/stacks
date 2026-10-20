/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.Locus.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed

/-!
# Flat base loci of morphisms of algebraic spaces

For a triangle `X ⟶ Y ⟶ Z`, the complement of the image of the nonflat
locus is an open subspace of `Z` under finite presentation, flatness,
closedness, and finite type hypotheses. A test morphism factors through
this open precisely when the induced morphism after base change is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

/-- The set of points of `Z` over which `f` is flat on the fibre in `X`,
as the complement of the image of the non-flat locus of `f` under
`f ≫ q`. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (f ≫ q) '' {x | FlatAt f x}ᶜ)ᶜ

/-- The flat base locus of the triangle is open in `Points Z` when
`f ≫ q` is locally of finite presentation, flat, and closed, and `q` is
locally of finite type. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The flat base locus of the triangle, as an open of `Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is flat at every point of the fibre in `X`. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    OpenSubspace Z :=
  OpenSubspace.fromOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the flat base locus if and only if `f` is flat at
every point of `X` above it. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q]
    (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      ∀ x : Points X, Points.map (f ≫ q) x = z → FlatAt f x :=
  sorry

/-- Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite presentation, flat, and closed, and that `q` is locally of finite type.
Then a morphism `g : Z' ⟶ Z` factors through the open subspace
`baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is flat. -/
@[stacks 05XB]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Flat (overBaseChange f q g) :=
  sorry


end AlgebraicGeometry.AlgebraicSpace.Flat
