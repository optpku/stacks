module

public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap76.Lemma_76_23_5
public import stacks_project.Chap76.Definition_76_48_1_LocalCompleteIntersection

/-!
# Local complete intersection base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which `f` is
Koszul at every point of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsLocalCompleteIntersection

/-- The set of points of `Z` over which `f` is Koszul on the fibre in `X`,
as the complement of the image of the non-Koszul locus of `f` under
`f ≫ q`. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (f ≫ q) '' {x | KoszulAt f x}ᶜ)ᶜ

/-- The local complete intersection base locus of the triangle is open in
`Points Z` when `f ≫ q` is flat, locally of finite presentation, and closed,
and `q` is flat and locally of finite presentation. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Flat (f ≫ q)]
    [LocallyOfFinitePresentation (f ≫ q)] [Closed (f ≫ q)]
    [Flat q] [LocallyOfFinitePresentation q] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The local complete intersection base locus of the triangle, as an open of
`Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Flat (f ≫ q)]
    [LocallyOfFinitePresentation (f ≫ q)] [Closed (f ≫ q)]
    [Flat q] [LocallyOfFinitePresentation q] : Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is Koszul. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Flat (f ≫ q)]
    [LocallyOfFinitePresentation (f ≫ q)] [Closed (f ≫ q)]
    [Flat q] [LocallyOfFinitePresentation q] : OpenSubspace Z :=
  OpenSubspace.ofOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Flat (f ≫ q)]
    [LocallyOfFinitePresentation (f ≫ q)] [Closed (f ≫ q)]
    [Flat q] [LocallyOfFinitePresentation q] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the local complete intersection base locus if and
only if `f` is Koszul at every point of `X` above it. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Flat (f ≫ q)]
    [LocallyOfFinitePresentation (f ≫ q)] [Closed (f ≫ q)]
    [Flat q] [LocallyOfFinitePresentation q] (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      ∀ x : Points X, Points.map (f ≫ q) x = z → KoszulAt f x :=
  sorry

/-- The inclusion of the local complete intersection base locus is an open
immersion. -/
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [Flat (f ≫ q)] [LocallyOfFinitePresentation (f ≫ q)]
    [Closed (f ≫ q)] [Flat q] [LocallyOfFinitePresentation q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the local complete
intersection base locus is a local complete intersection. -/
instance instIsLocalCompleteIntersection_overBaseChange_baseLocus
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [Flat (f ≫ q)] [LocallyOfFinitePresentation (f ≫ q)]
    [Closed (f ≫ q)] [Flat q] [LocallyOfFinitePresentation q] :
    IsLocalCompleteIntersection (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end IsLocalCompleteIntersection

end AlgebraicGeometry.AlgebraicSpace
