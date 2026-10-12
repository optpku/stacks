/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_49_3_BaseLocus
public import stacks_project.Chap76.Lemma_76_49_5_BaseLocus

/-!
# Isomorphism base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which the base
change of `f` is an isomorphism, obtained as the intersection of the
surjective-and-flat locus and the closed-immersion locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Isomorphism

/-- The set of points of `Z` over which `f` is surjective and flat on the
fibre and a closed immersion after base change to the point, as the
intersection of the corresponding point-sets. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  SurjectiveFlat.baseLocusPointsSet f q ∩ IsClosedImmersion.baseLocusPointsSet f q

/-- The isomorphism base locus of the triangle is open in `Points Z` when
`f ≫ q` is locally of finite presentation, flat, and universally closed,
and `q` is locally of finite type, closed, and separated. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The isomorphism base locus of the triangle, as an open of `Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is an isomorphism after base change to the point. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    OpenSubspace Z :=
  OpenSubspace.ofOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the isomorphism base locus if and only if it lies
in both the surjective-and-flat locus and the closed-immersion locus. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      z ∈ SurjectiveFlat.baseLocusPointsSet f q ∧
        z ∈ IsClosedImmersion.baseLocusPointsSet f q :=
  sorry

/-- The inclusion of the isomorphism base locus is an open immersion. -/
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the isomorphism base locus
is an isomorphism. -/
instance instIsIso_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    IsIso (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end Isomorphism

end AlgebraicGeometry.AlgebraicSpace
