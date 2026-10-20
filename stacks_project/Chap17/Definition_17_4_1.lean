/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Generated
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 17.4.1 (01AM): global generation of a module sheaf is existence of a family of
global generating sections. -/
@[stacks 01AM]
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦
  (SheafOfModules.IsGloballyGenerated F : Prop)

/- The source presentation is the explicit epimorphism from the free sheaf associated to a family
of global sections. -/
#check fun {X : RingedSpace.{u}} (F : X.Modules) ↦
  (SheafOfModules.IsGloballyGenerated.iff_exists F :
    SheafOfModules.IsGloballyGenerated F ↔
      ∃ (I : Type u) (s : I → F.sections), Epi (F.freeHomEquiv.symm s))
