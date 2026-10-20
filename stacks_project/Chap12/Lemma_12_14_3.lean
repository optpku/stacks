/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Homology.Homotopy.ChainShift
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {A B : ChainComplex C ℤ} (a b : A ⟶ B)

/- Lemma 12.14.3: self-homotopies of a chain map `a : A ⟶ B` are canonically equivalent to
maps `A ⟶ B⟦1⟧`. -/
#check (ChainComplex.Homotopy.selfEquivShiftHom a :
  Homotopy a a ≃ (A ⟶ B⟦(1 : ℤ)⟧))

/- Lemma 12.14.3: homotopies between two chain maps are either empty or form a principal
homogeneous space under the additive group of maps into the shifted target. -/
@[stacks 011C]
#check (ChainComplex.Homotopy.isEmpty_or_nonempty_addTorsor a b :
  IsEmpty (Homotopy a b) ∨ Nonempty (AddTorsor (A ⟶ B⟦(1 : ℤ)⟧) (Homotopy a b)))
