module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.BaseLocus
public import stacks_project.Chap67.Remark_67_12_5_Opens

/-!
# Unramified base locus of a triangle of algebraic spaces

The canonical open subspace `W ⊂ Z` of the base of a commutative triangle
`X ⟶ Y` over `Z` consisting of those points of `Z` over which `f` is
unramified at every point of `X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

open AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.49.1: The unramified base-locus point set. -/
#check (AlgebraicGeometry.AlgebraicSpace.Unramified.baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z), Set (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.isOpen_baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)],
      IsOpen (Unramified.baseLocusPointsSet f q))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.baseLocusPoints :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)], Opens (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)], OpenSubspace Z)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.baseLocus_pointsSet_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)],
      (Unramified.baseLocus f q).pointsSet = Unramified.baseLocusPointsSet f q)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.mem_baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
      (f : X ⟶ Y) (q : Y ⟶ Z) [Closed (f ≫ q)] [LocallyOfFiniteType (f ≫ q)]
      (z : Points Z),
      z ∈ (Unramified.baseLocus f q).pointsSet ↔
        ∀ x : Points X, Points.map (f ≫ q) x = z → UnramifiedAt f x)

