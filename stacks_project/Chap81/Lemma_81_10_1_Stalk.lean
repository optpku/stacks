module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Lemma_66_19_7_Point
public import stacks_project.Chap66.Lemma_66_19_9_Exact
public import stacks_project.Chap69.Lemma_69_9_4_Supported

/-!
# Derived étale stalks of algebraic spaces

The abelian étale stalk at a geometric point is the site-point sheaf fiber. Because that
functor is exact, it induces a derived stalk `D(X_étale) ⥤ D(Ab)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stalk functor on abelian étale sheaves at a geometric point, as the sheaf fiber of
the associated small étale site point. -/
abbrev etaleAbelianStalk {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X) :
    EtaleSheaf X ⥤ AddCommGrpCat.{u + 1} :=
  (GeometricPoint.toSmallEtalePoint xbar).sheafFiber

/-- The abelian étale stalk functor at a geometric point is additive. -/
instance etaleAbelianStalk_additive {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] (xbar : GeometricPoint X) :
    (etaleAbelianStalk xbar).Additive :=
  sorry

/-- The abelian étale stalk functor at a geometric point preserves finite limits. -/
instance etaleAbelianStalk_preservesFiniteLimits {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] (xbar : GeometricPoint X) :
    PreservesFiniteLimits (etaleAbelianStalk xbar) :=
  sorry

/-- The abelian étale stalk functor at a geometric point preserves finite colimits. -/
instance etaleAbelianStalk_preservesFiniteColimits {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] (xbar : GeometricPoint X) :
    PreservesFiniteColimits (etaleAbelianStalk xbar) :=
  sorry

/-- The derived stalk functor `EtaleDerived X ⥤ DerivedCategory AddCommGrpCat.{u + 1}` at a
geometric point, induced by the exact abelian étale stalk. -/
abbrev etaleDerivedStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (xbar : GeometricPoint X) :
    EtaleDerived X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  (etaleAbelianStalk xbar).mapDerivedCategory

/-- Exactness of the abelian étale stalk identifies cohomology of the derived stalk with the
stalk of cohomology. -/
theorem etaleDerivedStalk_homology {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (xbar : GeometricPoint X) (n : ℤ) :
    IsIsomorphic
      (DerivedCategory.homologyFunctor (EtaleSheaf X) n ⋙ etaleAbelianStalk xbar)
      (etaleDerivedStalk xbar ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n) :=
  sorry

/-- The derived stalk of an inverse image along `f` at `ybar` identifies with the derived
stalk at `ybar.map f`. -/
theorem etaleDerivedInverseImage_stalkIso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X)
    [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Y)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Y)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    (ybar : GeometricPoint Y) (G : EtaleDerived X) :
    IsIsomorphic
      ((etaleDerivedStalk ybar).obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj G))
      ((etaleDerivedStalk (ybar.map f)).obj G) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
