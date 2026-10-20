/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings

/-!
# Scalar restriction on universe-bounded sites
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules.ChangeOfRings

/-- Restriction of scalars between sheaves of modules on a site bounded by the
coefficient universe admits a left adjoint. -/
instance restrictScalars_isRightAdjoint_of_univLE
    {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [UnivLE.{max u v, w}] {R S : Sheaf J RingCat.{w}} (α : R ⟶ S) :
    (SheafOfModules.restrictScalars.{w} α).IsRightAdjoint := by
  sorry

end SheafOfModules.ChangeOfRings
