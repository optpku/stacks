module

public import stacks_project.Chap67.Definition_67_9_2_Closed
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap76.Lemma_76_23_6

/-!
# Flat base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which `f` is
flat at every point of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Flat

/-- The set of points of `Z` over which `f` is flat on the fibre in `X`,
as the complement of the image of the non-flat locus of `f` under
`f ≫ q`. -/
def baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) : Set (Points Z) :=
  (Points.map (f ≫ q) '' {x | FlatAt f x}ᶜ)ᶜ

/-- The flat base locus of the triangle is open in `Points Z` when
`f ≫ q` is locally of finite presentation, flat, and closed, and `q` is
locally of finite type. -/
theorem isOpen_baseLocusPointsSet {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    IsOpen (baseLocusPointsSet f q) :=
  sorry

/-- The flat base locus of the triangle, as an open of `Points Z`. -/
def baseLocusPoints {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    Opens (Points Z) :=
  Opens.mk (baseLocusPointsSet f q) (isOpen_baseLocusPointsSet f q)

/-- The canonical open subspace `W ⊂ Z` whose points are those over which `f`
is flat. -/
def baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    OpenSubspace Z :=
  OpenSubspace.ofOpens (baseLocusPoints f q)

/-- The underlying point-set of `baseLocus f q` is `baseLocusPointsSet f q`. -/
theorem baseLocus_pointsSet_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    (baseLocus f q).pointsSet = baseLocusPointsSet f q :=
  sorry

/-- A point of `Z` lies in the flat base locus if and only if `f` is flat at
every point of `X` above it. -/
theorem mem_baseLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q]
    (z : Points Z) :
    z ∈ (baseLocus f q).pointsSet ↔
      ∀ x : Points X, Points.map (f ≫ q) x = z → FlatAt f x :=
  sorry

/-- The inclusion of the flat base locus is an open immersion. -/
instance instIsOpenImmersion_baseLocus_ι {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    IsOpenImmersion (baseLocus f q).ι :=
  (baseLocus f q).isOpenImmersion

/-- The base change of `f` along the inclusion of the flat base locus is
flat. -/
instance instFlat_overBaseChange_baseLocus {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (q : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ q)] [Flat (f ≫ q)]
    [Closed (f ≫ q)] [LocallyOfFiniteType q] :
    Flat (overBaseChange f q (baseLocus f q).ι) :=
  sorry

end Flat

end AlgebraicGeometry.AlgebraicSpace
