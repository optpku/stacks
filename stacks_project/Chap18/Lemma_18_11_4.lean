/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import StacksCheckRecall

/-!
# Lemma 18.11.4

The reusable change-of-rings construction is owned by
`ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R R' : Sheaf J RingCat.{w}}
variable (α : R ⟶ R') [Epi α]

/- Lemma 18.11.4 (0930): an epimorphism of sheaves of rings induces a fully faithful
restriction-of-scalars functor on sheaves of modules. -/
@[stacks 0930]
#check
  (restrictScalarsFullyFaithfulOfEpi (α := α) :
    (restrictScalars.{z} α).FullyFaithful)

end SheafOfModules
