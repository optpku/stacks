/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.UniversallyInjectiveBaseLocus

/-!
# Closed-immersion base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which the base
change of `f` is a closed immersion, under the standing hypotheses that
`X ⟶ Z` is locally of finite type and universally closed and `Y ⟶ Z` is
separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

/-- The closed-immersion base locus of the triangle is open in `Points Z` when
`f ≫ q` is locally of finite type and universally closed and `q` is
separated. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] :
    IsOpen (UnramifiedUniversallyInjective.baseLocusPointsSet f q) :=
  sorry

/-- The closed-immersion base locus of the triangle, as an open of
`Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] : Opens (Points Z) :=
  Opens.mk (UnramifiedUniversallyInjective.baseLocusPointsSet f q)
    (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is a closed immersion after base change to the point. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] : OpenSubspace Z :=
  OpenSubspace.fromOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is the combined unramified
and diagonal-fibre locus. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] :
    (baseLocus f q).pointsSet = UnramifiedUniversallyInjective.baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the closed-immersion base locus if and only if `f`
is unramified at every point of `X` above it and the fibre of
`selfFiberToBase` over it lies in the image of the relative diagonal. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x) ∧
        ∀ t : Points (pullback f f),
          Points.map (UnramifiedUniversallyInjective.selfFiberToBase f q) t = z →
            t ∈ Set.range (Points.map (pullback.diagonal f)) :=
  sorry

/-- The inclusion of the closed-immersion base locus is an open immersion. -/
def baseLocus_isOpenImmersion {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the closed-immersion base
locus is a closed immersion. -/
def baseLocus_isClosedImmersion {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q] :
    IsClosedImmersion (Unramified.overBaseChange f q (baseLocus f q).ι) :=
  sorry

/-- For a triangle whose composite is locally of finite type and universally
closed and whose second morphism is separated, a morphism to the base factors
through the closed-immersion base locus if and only if the induced base change
is a closed immersion. -/
@[stacks 05XA]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      IsClosedImmersion (Unramified.overBaseChange f q g) :=
  sorry

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
