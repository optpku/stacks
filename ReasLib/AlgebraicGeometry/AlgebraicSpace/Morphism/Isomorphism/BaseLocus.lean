/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SurjectiveFlat.BaseLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.BaseLocus

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
  SurjectiveFlat.baseLocusPointsSet f q ∩ UnramifiedUniversallyInjective.baseLocusPointsSet f q

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
  OpenSubspace.fromOpens (baseLocusPoints f q)

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
        z ∈ UnramifiedUniversallyInjective.baseLocusPointsSet f q :=
  sorry

/-- The inclusion of the isomorphism base locus is an open immersion. -/
def baseLocus_isOpenImmersion {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the isomorphism base locus
is an isomorphism. -/
def baseLocus_isIso {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    IsIso (overBaseChange f q (baseLocus f q).ι) :=
  sorry

/-- Consider a commutative triangle of algebraic spaces over `S`
given by `f : X ⟶ Y` and `q : Y ⟶ Z`. Assume that `p = f ≫ q` is locally of
finite presentation, flat, and universally closed, and that `q` is locally of
finite type, closed, and separated. Then a morphism `g : Z' ⟶ Z` factors
through the open subspace `baseLocus f q ⊂ Z` if and only if the base change
`overBaseChange f q g : X_{Z'} ⟶ Y_{Z'}` is an isomorphism. -/
@[stacks 05XD]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [LocallyOfFiniteType q]
    [Closed q] [Separated q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      IsIso (overBaseChange f q g) :=
  sorry

end Isomorphism

end AlgebraicGeometry.AlgebraicSpace
