module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SurjectiveFlat.BaseLocus
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap76.Lemma_76_49_4_BaseLocus

/-!
# Surjective-and-flat base locus of a triangle of algebraic spaces

The canonical base-locus API is available through this compatibility entry
point, together with the existing open-subspace constructor imports.
-/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.surjectiveLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    Set (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z),
    Set (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.isOpen_baseLocusPointsSet :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q],
    IsOpen (baseLocusPointsSet f q))

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.baseLocusPoints :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q],
    Opens (Points Z))

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q],
    OpenSubspace Z)

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.baseLocus_pointsSet_eq :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q],
    (baseLocus f q).pointsSet = baseLocusPointsSet f q)

#check (AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat.mem_baseLocus :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (q : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ q)]
    [Flat (f ≫ q)] [Closed (f ≫ q)] [LocallyOfFiniteType q] [Closed q]
    (z : Points Z),
    z ∈ (baseLocus f q).pointsSet ↔
      (∀ x : Points X, Points.map (f ≫ q) x = z → FlatAt f x) ∧
        ∀ y : Points Y, Points.map q y = z → ∃ x : Points X, Points.map f x = y)

end AlgebraicGeometry.AlgebraicSpace.SurjectiveFlat
