/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free
import StacksCheckRecall

/-!
# Definition 18.17.1

Compatibility facade for the reusable freeness, global-generation, and global-presentation
predicates owned by `ReasLib.Algebra.Category.ModuleCat.Sheaf.Free`.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {R : Sheaf J RingCat.{w}}
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable (ℱ : SheafOfModules.{w} R)

/- Definition 18.17.1 (1): freeness means being isomorphic to a free sheaf on some type. -/
@[stacks 03DE "(1)"]
#check (IsFree ℱ : Prop)

/- Definition 18.17.1 (2): finite freeness uses a finite indexing type. -/
@[stacks 03DE "(2)"]
#check (IsFiniteFree ℱ : Prop)

/- Definition 18.17.1 (3): global generation is the existence of a Mathlib family of global
generating sections. -/
@[stacks 03DE "(3)"]
#check (IsGloballyGenerated ℱ : Prop)

/- Definition 18.17.1 (4): generation by `r` global sections. -/
@[stacks 03DE "(4)"]
#check (IsGeneratedBy ℱ : ℕ → Prop)

/- Definition 18.17.1 (5): finite global generation. -/
@[stacks 03DE "(5)"]
#check (IsFiniteGloballyGenerated ℱ : Prop)

/- Definition 18.17.1 (6): existence of a Mathlib global presentation. -/
@[stacks 03DE "(6)"]
#check (HasGlobalPresentation ℱ : Prop)

/- Definition 18.17.1 (7): existence of a global presentation with finite generator and relation
families. -/
@[stacks 03DE "(7)"]
#check (HasFiniteGlobalPresentation ℱ : Prop)

end SheafOfModules
