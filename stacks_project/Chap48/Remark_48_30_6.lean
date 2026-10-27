/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.InverseSystem.Positive.Linear
import StacksCheckRecall

universe v u

open CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Remark 48.30.6: linear pro-morphisms between positive inverse systems are compatible families
indexed by positive affine reindexings. -/
@[stacks 0G4P] #check
  (CategoryTheory.PNatInverseSystem.LinearHom :
    CategoryTheory.PNatInverseSystem C → CategoryTheory.PNatInverseSystem C → Type v)

#check
  (CategoryTheory.PNatInverseSystem.LinearHom.Equivalent :
    ∀ {A B : CategoryTheory.PNatInverseSystem C},
      CategoryTheory.PNatInverseSystem.LinearHom A B →
        CategoryTheory.PNatInverseSystem.LinearHom A B → Prop)
