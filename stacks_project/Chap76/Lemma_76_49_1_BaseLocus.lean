/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Lemma_67_38_10_SourceLocus
public import stacks_project.Chap67.Remark_67_12_5_Opens

/-!
# Unramified base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which `f` is
unramified at every point of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Unramified

/-- The set of points of `Z` over which `f` is unramified on the fibre in `X`,
as the complement of the image of the non-unramified locus of `f` under
`f ≫ q`. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (f ≫ q) '' (sourceLocus f).pointsSetᶜ)ᶜ

/-- The unramified base locus of the triangle is open in `Points Z` when
`f ≫ q` is closed. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The unramified base locus of the triangle, as an open of `Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] : Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is unramified. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] : OpenSubspace Z :=
  OpenSubspace.ofOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the unramified base locus if and only if `f` is
unramified at every point of `X` above it. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] [LocallyOfFiniteType (f ≫ q)]
    (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      ∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x :=
  sorry

/-- The inclusion of the unramified base locus is an open immersion. -/
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the unramified base locus is
unramified. -/
instance instUnramified_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)]
    [LocallyOfFiniteType (f ≫ q)] :
    Unramified (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end Unramified

end AlgebraicGeometry.AlgebraicSpace
