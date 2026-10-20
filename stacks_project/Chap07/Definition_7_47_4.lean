/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Sieve
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C] {U V T : C}

/- Definition 7.47.4: for a category C, a morphism f : V ⟶ U, and a sieve S on U,
the pullback of S by f (also called the base change of S by f) is the sieve
Sieve.pullbackOrderHom f S on V whose arrows α : T ⟶ V satisfy
Sieve.pullbackOrderHom f S α ↔ S (α ≫ f). In source notation this is S ×_U V. The
return type Sieve V records that this is indeed a sieve. -/
@[stacks 00Z2] #check
  (CategoryTheory.Sieve.pullbackOrderHom : (V ⟶ U) → (Sieve U →o Sieve V))

#check (CategoryTheory.Sieve.pullbackOrderHom_apply :
  ∀ (morphism : V ⟶ U) (sieve : Sieve U) (arrow : T ⟶ V),
    CategoryTheory.Sieve.pullbackOrderHom morphism sieve arrow ↔ sieve (arrow ≫ morphism))
