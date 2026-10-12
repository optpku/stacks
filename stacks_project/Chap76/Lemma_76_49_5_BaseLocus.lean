/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap76.Lemma_76_49_4_BaseLocus

/-!
# Surjective-and-flat base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which the base
change of `f` is simultaneously surjective and flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace SurjectiveFlat

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
  OpenSubspace.ofOpens (baseLocusPoints f q)

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

/-- The inclusion of the surjective-and-flat base locus is an open immersion. -/
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the surjective-and-flat
base locus is surjective. -/
instance instSurjective_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    Surjective (overBaseChange f q (baseLocus f q).ι) :=
  sorry

/-- The base change of `f` along the inclusion of the surjective-and-flat
base locus is flat. -/
instance instFlat_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q] :
    Flat (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end SurjectiveFlat

end AlgebraicGeometry.AlgebraicSpace
