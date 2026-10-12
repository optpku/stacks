/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

#check (CategoryTheory.Idempotents.Karoubi.instSymmetricCategory :
  SymmetricCategory (CategoryTheory.Idempotents.Karoubi C))
