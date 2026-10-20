/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.Lift.Computations
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.LiftTo.Computations
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.LiftFrom.Computations
public import ReasLib.CategoryTheory.Bicategory.FullSubbicategory.Pseudofunctor.StrongTrans.Modification.Computations

/-!
# Strong transformations for full-subbicategory pseudofunctor lifts

This aggregate exports the bilateral lift and the endpoint-preserving `liftTo` and `liftFrom`
variants, together with their component, naturality, and ambient readout API. It also exports the
canonical bilateral lift of modifications.
-/
