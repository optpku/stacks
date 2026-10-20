/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of rings for finitely generated modules

Extension of scalars restricts to finitely generated modules.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace FGModuleCat

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Extension of scalars sends a finitely generated module to a finitely
generated module. -/
@[stacks 05ET "finite modules under extension of scalars"]
theorem extendScalarsObj_finite (f : R →+* S) (M : FGModuleCat.{u} R) :
    let _ : Algebra R S := f.toAlgebra
    Module.Finite S
      ((((ModuleCat.isFG.{u} R).ι ⋙
        ModuleCat.extendScalars.{u, u, u} f).obj M) : Type u) := sorry

/-- Extension of scalars on finitely generated modules, obtained by
restricting the canonical `ModuleCat.extendScalars` functor. -/
@[stacks 05ET "extension of scalars on finite modules"]
noncomputable abbrev extendScalars (f : R →+* S) :
    FGModuleCat.{u} R ⥤ FGModuleCat.{u} S :=
  let _ : Algebra R S := f.toAlgebra
  (ModuleCat.isFG.{u} S).lift
    ((ModuleCat.isFG.{u} R).ι ⋙ ModuleCat.extendScalars.{u, u, u} f)
    (extendScalarsObj_finite f)

end FGModuleCat
