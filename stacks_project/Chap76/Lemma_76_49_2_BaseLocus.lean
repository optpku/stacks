/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import stacks_project.Chap67.Lemma_67_19_5_UniversallyInjective
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

/-- `overBaseChange` is `Unramified.overBaseChange`. -/
theorem overBaseChange_eq {S : Scheme.{u}} {X Y Z Z' : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z) :
    overBaseChange f q g = Unramified.overBaseChange f q g :=
  sorry

/-- The morphism `p₂ : X ×_Y X ⟶ Z` obtained by composing a projection of
the self-fibre product with `f ≫ q`. -/
def selfFiberToBase {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : pullback f f ⟶ Z :=
  pullback.fst f f ≫ f ≫ q

/-- `selfFiberToBase f q` is `pullback.fst f f ≫ f ≫ q`. -/
theorem selfFiberToBase_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) :
    selfFiberToBase f q = pullback.fst f f ≫ f ≫ q :=
  sorry

/-- The two projections of `X ×_Y X` compose equally with `f ≫ q`. -/
theorem selfFiberToBase_fst_eq_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) :
    pullback.fst f f ≫ f ≫ q = pullback.snd f f ≫ f ≫ q :=
  sorry

/-- The set of points of `Z` whose `selfFiberToBase`-fibre lies in the image of
the relative diagonal, as the complement of the image under `selfFiberToBase`
of the complement of the image of `pullback.diagonal f`. -/
def diagonalFiberLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (selfFiberToBase f q) ''
      (Set.range (Points.map (pullback.diagonal f)))ᶜ)ᶜ

/-- The set of points of `Z` over which `f` is unramified on the fibre in `X`
and the fibre of `selfFiberToBase` lies in the image of the relative
diagonal. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  Unramified.baseLocusPointsSet f q ∩ diagonalFiberLocusPointsSet f q

/-- The unramified-and-universally-injective base locus of the triangle is open
in `Points Z` when `f ≫ q` is locally of finite type and closed and
`selfFiberToBase f q` is closed. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The unramified-and-universally-injective base locus of the triangle, as an
open of `Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] : Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is unramified and universally injective after base change to the point. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    OpenSubspace Z :=
  OpenSubspace.ofOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the unramified-and-universally-injective base locus
if and only if `f` is unramified at every point of `X` above it and the fibre
of `selfFiberToBase` over it lies in the image of the relative diagonal. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x) ∧
        ∀ t : Points (pullback f f),
          Points.map (selfFiberToBase f q) t = z →
            t ∈ Set.range (Points.map (pullback.diagonal f)) :=
  sorry

/-- The inclusion of the unramified-and-universally-injective base locus is an
open immersion. -/
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the
unramified-and-universally-injective base locus is unramified. -/
instance instUnramified_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    Unramified (overBaseChange f q (baseLocus f q).ι) :=
  sorry

/-- The base change of `f` along the inclusion of the
unramified-and-universally-injective base locus is universally injective. -/
instance instUniversallyInjective_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)]
    [Closed (selfFiberToBase f q)] :
    UniversallyInjective (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end UnramifiedUniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
