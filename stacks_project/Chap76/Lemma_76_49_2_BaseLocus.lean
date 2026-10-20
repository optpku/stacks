/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.UniversallyInjectiveBaseLocus
public import stacks_project.Chap76.Lemma_76_49_1_BaseLocus

/-!
# Unramified-and-universally-injective base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which the base
change of `f` is simultaneously unramified and universally injective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UnramifiedUniversallyInjective

/-- The base change of `f : X ⟶ Y` over `Z` along `g : Z' ⟶ Z`, as the
comparison `X ×_Z Z' ⟶ Y ×_Z Z'`. -/
abbrev overBaseChange {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    pullback (f ≫ q) g ⟶ pullback q g :=
  Unramified.overBaseChange f q g

#check (selfFiberToBase : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    pullback f f ⟶ Z)

#check (selfFiberToBase_eq : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    selfFiberToBase f q = pullback.fst f f ≫ f ≫ q)

#check (selfFiberToBase_fst_eq_snd : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    pullback.fst f f ≫ f ≫ q = pullback.snd f f ≫ f ≫ q)

#check (diagonalFiberLocusPointsSet : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    Set (Points Z))

#check (baseLocusPointsSet : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    Set (Points Z))

#check (isOpen_baseLocusPointsSet : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    IsOpen (baseLocusPointsSet f q))

#check (baseLocusPoints : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    Opens (Points Z))

#check (baseLocus : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    OpenSubspace Z)

#check (baseLocus_pointsSet_eq : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    (baseLocus f q).pointsSet = baseLocusPointsSet f q)

#check (mem_baseLocus : ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] (z : Points Z),
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x) ∧
        ∀ t : Points (pullback f f),
          Points.map (selfFiberToBase f q) t = z →
            t ∈ Set.range (Points.map (pullback.diagonal f)))

#check (exists_lift_iff_overBaseChange : ∀ {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Unramified (Unramified.overBaseChange f q g) ∧
        UniversallyInjective (Unramified.overBaseChange f q g))

#check (baseLocus_unramified : ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    Unramified (Unramified.overBaseChange f q (baseLocus f q).ι))

#check (baseLocus_universallyInjective : ∀ {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)],
    UniversallyInjective (Unramified.overBaseChange f q (baseLocus f q).ι))

end UnramifiedUniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
