module

public import ReasLib.Algebra.Category.ModuleCat.Sequential
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Bottom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
import Mathlib.Tactic.CrossRefAttribute

/-!
# Grothendieck structure on sequential varying-ring modules

@stack 091D

The sheaf-of-modules construction gives the canonical Grothendieck-abelian structure on a
sequential varying-ring module category.  This leaf records the specialization explicitly so
downstream derived-limit declarations can rely on typeclass search without rebuilding a
chapter-local universe pin.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SequentialInverseSystem

/-- Stacks `091D`: a sequential varying-ring module category is abelian. -/
@[stacks 091D "abelian sequential varying-ring module category"]
noncomputable instance moduleSystemAbelian
    (F : SequentialInverseSystem CommRingCat.{u}) :
    Abelian (ModuleSystem.{u, v} F) :=
  SheafOfModules.Bottom.abelian (bottomRingSheaf F)

/-- Stacks `091D`: a sequential varying-ring module category is Grothendieck abelian. -/
@[stacks 091D "Grothendieck-abelian sequential varying-ring module category"]
noncomputable instance moduleSystemIsGrothendieckAbelian
    (F : SequentialInverseSystem CommRingCat.{u}) :
    IsGrothendieckAbelian (ModuleSystem.{u, v} F) := sorry

end CategoryTheory.SequentialInverseSystem

end
