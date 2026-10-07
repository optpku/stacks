module

public import ReasLib.CategoryTheory.Idempotents.Karoubi.Monoidal

@[expose] public section

open CategoryTheory
open scoped CategoryTheory.MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

#check (CategoryTheory.Idempotents.Karoubi.instSymmetricCategory :
  SymmetricCategory (CategoryTheory.Idempotents.Karoubi C))
