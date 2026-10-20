module

public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.CategoryTheory.Sites.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w u₁ v₁ u₂ v₂

/- Definition 59.11.1: a presheaf is separated when restriction to every
   covering family is injective, and it is a sheaf when the two restrictions
   to every overlap form an equalizer; the same clauses apply to abelian
   presheaves through the corresponding concrete-category predicates. -/
@[stacks 03NK] #check (CategoryTheory.Presieve.isSeparated_iff_injective_restriction :
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type w),
    CategoryTheory.Presieve.IsSeparated J F ↔
      ∀ (U : C) (R : CategoryTheory.Presieve U),
        Sieve.generate R ∈ J U →
          Function.Injective
            (fun sectionValue : F.obj (Opposite.op U) =>
              fun (V : C) (arrow : V ⟶ U) (_ : R arrow) =>
                F.map arrow.op sectionValue))
#check CategoryTheory.Presieve.IsSeparated
#check CategoryTheory.Presieve.IsSheaf
#check CategoryTheory.Presheaf.IsSeparated
#check CategoryTheory.Presheaf.IsSheaf

end
