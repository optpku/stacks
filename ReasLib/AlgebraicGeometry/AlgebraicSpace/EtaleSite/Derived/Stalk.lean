/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GeometricPoint.SmallEtalePoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Supported

/-!
# Derived étale stalks of algebraic spaces

The abelian étale stalk at a geometric point is the site-point sheaf fiber. Because that
functor is exact, it induces a derived stalk `D(X_étale) ⥤ D(Ab)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

-- Local instance justification (defeq pin): sheaf preadditive inference otherwise differs from the Abelian-induced structures fixed by DerivedCategory.Qh and exact-derived factorization; pin the existing canonical projections consistently for homotopy categories, additive binders, and derived models.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

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

/-- The derived stalk functor `EtaleDerived X ⥤ DerivedCategory AddCommGrpCat.{u + 1}` at a
geometric point, induced by the exact abelian étale stalk. -/
abbrev etaleDerivedStalk {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (xbar : GeometricPoint X) :
    EtaleDerived X ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _ (etaleAbelianStalk xbar) inferInstance
    (@GrothendieckTopology.Point.instPreservesFiniteLimitsSheafSheafFiberOfLocallySmallOfHasFiniteLimitsOfAB5OfSize
      (smallEtaleSite X) inferInstance (smallEtaleTopology X)
      (GeometricPoint.toSmallEtalePoint xbar) AddCommGrpCat.{u + 1}
      inferInstance inferInstance inferInstance inferInstance
      (AB5OfSize_shrink.{u, u, u + 1, u + 1} AddCommGrpCat.{u + 1}))
    inferInstance

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
