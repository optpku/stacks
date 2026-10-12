/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import ReasLib.CategoryTheory.Limits.Colimit.Representable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite modules and filtered colimits

@stack 0G8N
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits Opposite

universe u v

namespace Module.Finite

variable {R : Type u} [Ring R]

/-- Lemma 10.11.1: a module is finite exactly when its representable Hom functor has injective
comparison maps for all filtered colimits. -/
@[stacks 0G8N "finite modules detect equality in filtered colimits"]
theorem iff_colimitPost_injective (N : ModuleCat.{v} R) :
    Module.Finite R N ↔
      ∀ ⦃J : Type v⦄ [SmallCategory J] [IsFiltered J] (F : J ⥤ ModuleCat R),
        Function.Injective (colimit.post F (coyoneda.obj (op N))) := sorry

end Module.Finite
