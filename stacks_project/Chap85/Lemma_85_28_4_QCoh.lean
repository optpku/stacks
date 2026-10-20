module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Basic
public import stacks_project.Chap85.Lemma_85_28_1_Ringed

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Basic

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.SimplicialObject.QCoh.inclusion :
  ∀ (U : SimplicialObject Scheme.{u}),
    AlgebraicGeometry.SimplicialObject.QCoh U ⥤
      SheafOfModules.{u} (AlgebraicGeometry.SimplicialObject.structureSheaf U))
