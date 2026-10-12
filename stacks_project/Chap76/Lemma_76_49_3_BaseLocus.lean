/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap76.Lemma_76_49_2_BaseLocus

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

/-- The base change of `f : X ⟶ Y` over `Z` along `g : Z' ⟶ Z`, as the
comparison `X ×_Z Z' ⟶ Y ×_Z Z'`. -/
abbrev overBaseChange {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    pullback (f ≫ q) g ⟶ pullback q g :=
  UnramifiedUniversallyInjective.overBaseChange f q g

/-- `overBaseChange` is `UnramifiedUniversallyInjective.overBaseChange`. -/
theorem overBaseChange_eq {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g = UnramifiedUniversallyInjective.overBaseChange f q g :=
  sorry

/-- The set of points of `Z` over which `f` is unramified on the fibre in `X`
and the fibre of `selfFiberToBase` lies in the image of the relative
diagonal. -/
abbrev baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  UnramifiedUniversallyInjective.baseLocusPointsSet f q

/-- The closed-immersion base locus of the triangle is open in `Points Z` when
`f ≫ q` is locally of finite type and universally closed and `q` is
separated. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The closed-immersion base locus of the triangle, as an open of
`Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] : Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is a closed immersion after base change to the point. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] : OpenSubspace Z :=
  OpenSubspace.ofOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
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
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the closed-immersion base
locus is a closed immersion. -/
instance instIsClosedImmersion_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q] :
    IsClosedImmersion (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
