module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Koszul.Locus
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Factorization

/-!
# Local complete intersection base loci

For a triangle `X ⟶ Y ⟶ Z` with closed composite, the points of `Z` over
which the first morphism is Koszul everywhere form a canonical open subspace.
When both structure maps are flat and locally of finite presentation, this
open subspace represents the local complete intersection base-change locus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection

/-- The set of points over which a morphism is Koszul at every point of its
source, given by the complement of the image of its non-Koszul locus. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (f ≫ q) '' {x | KoszulAt f x}ᶜ)ᶜ

/-- If the composite structure map is closed, the set of points over which
the morphism is Koszul everywhere is open. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The open set of points over which a morphism is Koszul everywhere, when
the composite structure map is closed. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] : Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace of the base over which a morphism is Koszul
at every point of its source. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] : OpenSubspace Z :=
  OpenSubspace.fromOpens (baseLocusPoints f q)

/-- The point set of the canonical base locus is the complement of the image
of the non-Koszul locus under the composite structure map. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of the base lies in the canonical base locus if and only if the
morphism is Koszul at every point of the source above it. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      ∀ x : Points X, Points.map (f ≫ q) x = z → KoszulAt f x :=
  sorry

/-- For a morphism between algebraic spaces flat and locally of finite
presentation over a common base, with closed source structure map, a test
morphism factors through the canonical base locus if and only if the induced
base-change morphism is a local complete intersection. -/
theorem exists_lift_iff_overBaseChange {S : Scheme.{u}}
    {X Y Z Z' : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z) (g : Z' ⟶ Z)
    [Flat (f ≫ q)] [LocallyOfFinitePresentation (f ≫ q)]
    [Closed (f ≫ q)] [Flat q] [LocallyOfFinitePresentation q] :
    (∃ ℓ : Z' ⟶ (baseLocus f q).X, ℓ ≫ (baseLocus f q).ι = g) ↔
      IsLocalCompleteIntersection (overBaseChange f q g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsLocalCompleteIntersection
