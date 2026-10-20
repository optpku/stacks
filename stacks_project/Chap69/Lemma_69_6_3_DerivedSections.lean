/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero

/-! Compatibility interface for the Hom-from-integers model of global sections. -/

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.globalSections :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})],
    Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1})

#check (AlgebraicGeometry.AlgebraicSpace.globalSections_obj :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}),
    (globalSections X).obj F =
      (preadditiveYoneda.obj F).obj (op (constantIntegerSheaf X)))

#check (AlgebraicGeometry.AlgebraicSpace.globalSections_map :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G),
    (globalSections X).map φ =
      (preadditiveYoneda.map φ).app (op (constantIntegerSheaf X)))

#check (AlgebraicGeometry.AlgebraicSpace.globalSections_additive :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})],
    (globalSections X).Additive)

#check (AlgebraicGeometry.AlgebraicSpace.globalSections_isomorphic_gamma :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S)
    [HasWeakSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasGlobalSectionsFunctor (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})],
    IsIsomorphic (globalSections X) (Sheaf.Γ (smallEtaleTopology X) AddCommGrpCat.{u + 1}))

