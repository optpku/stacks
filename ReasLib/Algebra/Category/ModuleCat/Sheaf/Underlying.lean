/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Tactic.CrossRefAttribute

/-!
# Underlying sheaves of types of sheaves of modules

This file names the composite forgetful functor from sheaves of modules to type-valued sheaves.
Keeping this composite as a single owner makes comparison and conservativity statements independent
of the intermediate additive-sheaf representation.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- The underlying type-valued sheaf of a sheaf of modules, used in the module-linear bridge for
Lemma 18.41.3 (0FN3). -/
@[stacks 0FN3 "underlying type-valued sheaf"]
noncomputable def toTypeSheaf (R : Sheaf J RingCat.{w}) :
    SheafOfModules.{z} R ⥤ Sheaf J (Type z) :=
  toSheaf R ⋙ sheafCompose J (CategoryTheory.forget AddCommGrpCat.{z})

/-- Forgetting a sheaf of modules to its underlying type-valued sheaf reflects isomorphisms.
Unlike the existing sheafification-leaf instance, this form does not impose a
`WEqualsLocallyBijective` assumption on the site. -/
instance toTypeSheaf_reflectsIsomorphisms (R : Sheaf J RingCat.{w}) :
    (toTypeSheaf.{u, v, w, z} R).ReflectsIsomorphisms := sorry

end SheafOfModules
