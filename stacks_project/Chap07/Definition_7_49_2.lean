module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (ℱ : Cᵒᵖ ⥤ Type w)

/- Definition 7.49.2: Let `C` be a category. Let `J` be a topology on `C`. We say that a
presheaf of sets `ℱ` is separated if for every object `U` and every covering sieve `S` on `U`
the canonical map `ℱ(U) ⟶ Mor_PSh(C)(S, ℱ)` is injective. -/
@[stacks 00ZI] #check Presieve.IsSeparated J ℱ

#check @Presieve.IsSeparatedFor
#check @Presieve.IsSeparatedFor.ext
#check Sieve.functorInclusion
