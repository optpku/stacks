module

public import stacks_project.Chap42.«42_50_2_1_BivariantPushforward»
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Proper.Over

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry

/- The finite-type slice-morphism instance is now provided by its reusable owner. -/
#check
  (AlgebraicGeometry.instLocallyOfFiniteTypeNestedOverHomMk :
    ∀ {S : Scheme.{u}} {X : Over S} {Z Z' : Scheme.{u}}
      (j : Z' ⟶ Z) (i : Z ⟶ X.left) [LocallyOfFiniteType j],
      LocallyOfFiniteType
        (Over.homMk j (Category.assoc j i X.hom).symm :
          Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom)).left)

/- The proper slice-morphism instance is now provided by its reusable owner. -/
#check
  (AlgebraicGeometry.instIsProperNestedOverHomMk :
    ∀ {S : Scheme.{u}} {X : Over S} {Z Z' : Scheme.{u}}
      (j : Z' ⟶ Z) (i : Z ⟶ X.left) [IsProper j],
      IsProper
        (Over.homMk j (Category.assoc j i X.hom).symm :
          Over.mk ((j ≫ i) ≫ X.hom) ⟶ Over.mk (i ≫ X.hom)).left)

end AlgebraicGeometry
