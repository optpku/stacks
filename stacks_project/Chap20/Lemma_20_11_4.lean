/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

variable (X : RingedSpace.{u}) (p : ℕ) (F : X.Modules) (U : Opens X)

/- Lemma 20.11.4 (1): the inclusion of module sheaves into module presheaves
on a ringed space is left exact. -/
@[stacks 01ER] #check
  (SheafOfModules.forget_preservesFiniteLimits X.ringCatSheaf :
    PreservesFiniteLimits (SheafOfModules.forget.{u} X.ringCatSheaf))

/- Lemma 20.11.4 (2): the degree-p right derived inclusion is the module-valued
cohomology presheaf; its underlying additive presheaf evaluates on U as H' p U. -/
@[stacks 01ER] #check
  (SheafOfModules.cohomologyPresheafFunctor_toPresheaf_isomorphic X.ringCatSheaf p :
    IsIsomorphic
      ((SheafOfModules.forget X.ringCatSheaf).rightDerived p ⋙
        PresheafOfModules.toPresheaf X.ringCatSheaf.obj)
      (SheafOfModules.toSheaf X.ringCatSheaf ⋙
        Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) p))

#check
  (SheafOfModules.cohomologyPresheafFunctor X.ringCatSheaf p :
    X.Modules ⥤ X.PresheafModules)

#check
  (SheafOfModules.cohomologyAtObject_isomorphic X.ringCatSheaf F p U :
    IsIsomorphic
      ((SheafOfModules.cohomologyAtObjectFunctor X.ringCatSheaf p U).obj F)
      (((SheafOfModules.toSheaf X.ringCatSheaf).obj F).H' p U))
