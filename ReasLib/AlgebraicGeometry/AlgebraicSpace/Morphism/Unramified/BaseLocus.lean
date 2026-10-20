/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.SourceLocus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Factorization

/-!
# Unramified base loci of triangles of algebraic spaces

The complement of the image of the non-unramified source locus determines an
open subspace of the base when the composite morphism is closed. For a locally
finite-type composite, factorization through this open characterizes unramified
base change.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Unramified

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

/-- The canonical open subspace of `Z` whose fibres in `X` lie in the
unramified source locus of `f`. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] : OpenSubspace Z :=
  OpenSubspace.fromOpens (baseLocusPoints f q)

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

/-- For a triangle with locally finite-type closed composite, a morphism to the
base factors through the unramified base locus if and only if the induced
base-changed morphism is unramified. -/
@[stacks 05X8]
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [LocallyOfFiniteType (f ≫ q)] [Closed (f ≫ q)] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      Unramified (overBaseChange f q g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Unramified
