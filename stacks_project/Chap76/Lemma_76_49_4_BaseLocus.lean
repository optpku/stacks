module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseLocus
public import stacks_project.Chap67.Remark_67_12_5_Opens

/-!
# Flat base locus of a triangle of algebraic spaces

The flat base-locus API and the opens constructor are publicly available
through this compatibility entry point.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Flat

#check (AlgebraicGeometry.AlgebraicSpace.Flat.baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z), Set (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.Flat.isOpen_baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q],
    IsOpen (baseLocusPointsSet f q))

#check (AlgebraicGeometry.AlgebraicSpace.Flat.baseLocusPoints :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q],
    Opens (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.Flat.baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q],
    OpenSubspace Z)

#check (AlgebraicGeometry.AlgebraicSpace.Flat.baseLocus_pointsSet_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q],
    (baseLocus f q).pointsSet = baseLocusPointsSet f q)

#check (AlgebraicGeometry.AlgebraicSpace.Flat.mem_baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] (z : Points Z),
    z ∈ (baseLocus f q).pointsSet ↔
      ∀ x : Points X, Points.map (f ≫ q) x = z → FlatAt f x)

end AlgebraicGeometry.AlgebraicSpace.Flat
