/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# Standard derived categories of sheaves of modules
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe z u v w

namespace SheafOfModules

/-- The standard unbounded derived category of sheaves of modules over a ring sheaf. -/
abbrev Derived {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{w}) [abelian : Abelian (SheafOfModules.{z} O)] :=
  @DerivedCategory (SheafOfModules.{z} O) inferInstance inferInstance
    (HasDerivedCategory.standard (SheafOfModules.{z} O))

namespace Derived

/-- An abelian category of module sheaves carries its standard derived-category structure. -/
instance hasDerivedCategory {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    (O : Sheaf J RingCat.{w}) [abelian : Abelian (SheafOfModules.{z} O)] :
    HasDerivedCategory (SheafOfModules.{z} O) :=
  HasDerivedCategory.standard (SheafOfModules.{z} O)

end Derived
end SheafOfModules
