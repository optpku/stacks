/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.BaseLocus

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

/-- The set of points of `Z` over which `f` is unramified on the fibre in `X`
and the fibre of `selfFiberToBase` lies in the image of the relative
diagonal. -/
abbrev baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  UnramifiedUniversallyInjective.baseLocusPointsSet f q

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.isOpen_baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q],
    IsOpen (UnramifiedUniversallyInjective.baseLocusPointsSet f q))

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.baseLocusPoints :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q],
    Opens (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q],
    OpenSubspace Z)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.baseLocus_pointsSet_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q],
    (baseLocus f q).pointsSet = UnramifiedUniversallyInjective.baseLocusPointsSet f q)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.mem_baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)]
    [UniversallyClosed (f ≫ q)] [Separated q] (z : Points Z),
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x) ∧
        ∀ t : Points (pullback f f),
          Points.map (UnramifiedUniversallyInjective.selfFiberToBase f q) t = z →
            t ∈ Set.range (Points.map (pullback.diagonal f)))

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.baseLocus_isOpenImmersion :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q],
    IsOpenImmersion (baseLocus f q).ι)

#check (AlgebraicGeometry.AlgebraicSpace.IsClosedImmersion.baseLocus_isClosedImmersion :
    ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [UniversallyClosed (f ≫ q)]
    [Separated q],
    IsClosedImmersion (Unramified.overBaseChange f q (baseLocus f q).ι))

end IsClosedImmersion

end AlgebraicGeometry.AlgebraicSpace
