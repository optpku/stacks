/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v u'

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [∀ X : C, HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
variable [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/- Lemma 17.9.8 (01BC): finite-type `R`-module sheaves admit a set containing exactly one
representative of every isomorphism class. -/
@[stacks 01BC]
#check
  (ObjectProperty.EssentiallySmall.exists_set_representatives
    (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules.{u} R)) :
    ∃ S : Set (SheafOfModules.{u} R),
      (∀ M ∈ S, M.IsFiniteType) ∧
      ∀ M : SheafOfModules.{u} R, M.IsFiniteType →
        ∃! N : SheafOfModules.{u} R, N ∈ S ∧ Nonempty (N ≅ M))

/- The reusable root owner is the essential smallness of the finite-type object property. -/
#synth ObjectProperty.EssentiallySmall
  (SheafOfModules.IsFiniteType : ObjectProperty (SheafOfModules.{u} R))

#check @SheafOfModules.IsFiniteType.essentiallySmall

/- The representative-set conclusion is available for every essentially small,
isomorphism-closed object property. -/
#check @ObjectProperty.EssentiallySmall.exists_set_representatives

end SheafOfModules
