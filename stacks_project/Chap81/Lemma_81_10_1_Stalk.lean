/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Derived.Stalk
public import stacks_project.Chap69.Lemma_69_9_4_Supported

/-! # Derived étale stalks of algebraic spaces -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

#check (AlgebraicGeometry.AlgebraicSpace.etaleAbelianStalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (xbar : GeometricPoint X),
    EtaleSheaf X ⥤ AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.etaleAbelianStalk_additive :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] (xbar : GeometricPoint X),
    (etaleAbelianStalk xbar).Additive)

#check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedStalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (xbar : GeometricPoint X),
    EtaleDerived X ⥤ DerivedCategory AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedStalk_homology :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [Abelian (EtaleSheaf X)] [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory AddCommGrpCat.{u + 1}]
    (xbar : GeometricPoint X) (n : ℤ),
    IsIsomorphic
      (DerivedCategory.homologyFunctor (EtaleSheaf X) n ⋙ etaleAbelianStalk xbar)
      (etaleDerivedStalk xbar ⋙ DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} n))

#check (AlgebraicGeometry.AlgebraicSpace.etaleDerivedInverseImage_stalkIso :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : Y ⟶ X)
    [Abelian (EtaleSheaf X)] [Abelian (EtaleSheaf Y)]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology Y) AddCommGrpCat.{u + 1}]
    [HasDerivedCategory (EtaleSheaf X)] [HasDerivedCategory (EtaleSheaf Y)]
    [HasDerivedCategory AddCommGrpCat.{u + 1}]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    (ybar : GeometricPoint Y) (G : EtaleDerived X),
    IsIsomorphic
      ((etaleDerivedStalk ybar).obj
        ((sheafInverseImage AddCommGrpCat.{u + 1} f).mapDerivedCategory.obj G))
      ((etaleDerivedStalk (ybar.map f)).obj G))
