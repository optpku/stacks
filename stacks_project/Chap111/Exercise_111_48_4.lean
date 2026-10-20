/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ext.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Abelian
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Ext

/- Exercise 111.48.4 (1): a finite locally free tensor factor moves from the first argument
of sheaf Ext to its second argument as the structure-module-valued internal-Hom dual. -/
@[stacks 0DD4] #check (AlgebraicGeometry.RingedSpace.Ext.sheafExt_tensor :
  ∀ {X : RingedSpace.{u}} (E F G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
    IsIsomorphic (sheafExt (F ⊗ E) G i)
      (sheafExt F (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i))

/- Exercise 111.48.4 (2): tensoring the second argument of sheaf Ext by the dual of a finite
locally free module tensors the resulting sheaf Ext by the same dual. -/
@[stacks 0DD4] #check (AlgebraicGeometry.RingedSpace.Ext.sheafExt_tensorDual :
  ∀ {X : RingedSpace.{u}} (E F G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
    IsIsomorphic (sheafExt F (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i)
      (sheafExt F G i ⊗ ((ihom E).obj (SheafOfModules.unit X.ringCatSheaf))))

/- Exercise 111.48.4 (3): a finite locally free tensor factor moves across global Ext by
internal-Hom duality. -/
@[stacks 0DD4] #check (AlgebraicGeometry.RingedSpace.Ext.ext_tensor :
  ∀ {X : RingedSpace.{u}} (E F G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
    IsIsomorphic (AddCommGrpCat.of (Abelian.Ext (F ⊗ E) G i))
      (AddCommGrpCat.of
        (Abelian.Ext F (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i)))

/- Exercise 111.48.4 (4): global Ext from a finite locally free module is cohomology of its
internal-Hom dual tensored with the target module. -/
@[stacks 0DD4] #check (AlgebraicGeometry.RingedSpace.Ext.ext_eq_cohomology :
  ∀ {X : RingedSpace.{u}} (E G : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
    IsIsomorphic (AddCommGrpCat.of (Abelian.Ext E G i))
      (AlgebraicGeometry.RingedSpace.moduleCohomology
        (((ihom E).obj (SheafOfModules.unit X.ringCatSheaf)) ⊗ G) i))

end AlgebraicGeometry.RingedSpace.Ext
