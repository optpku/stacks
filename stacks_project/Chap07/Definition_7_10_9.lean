/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (ℱ : Cᵒᵖ ⥤ Type w)

/- Definition 7.10.9: a presheaf of sets `ℱ` on a site `C` is separated if, for
every covering `{U_i ⟶ U}`, the map `ℱ(U) ⟶ ∏ ℱ(U_i)` is injective. -/
@[stacks 00WA] #check Presieve.IsSeparated J ℱ

#check @Presieve.IsSeparatedFor
#check @Presieve.IsSeparatedFor.ext
