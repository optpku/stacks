module

public import ReasLib.CategoryTheory.Sites.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Definition 7.10.9: a presheaf of sets `ℱ` on a site `C` is separated if, for
every covering `{U_i ⟶ U}`, the map `ℱ(U) ⟶ ∏ ℱ(U_i)` is injective. -/
@[stacks 00WA] #check
  (CategoryTheory.Presieve.isSeparated_iff_injective_restriction :
    ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
      (F : Cᵒᵖ ⥤ Type w),
      CategoryTheory.Presieve.IsSeparated J F ↔
        ∀ (U : C) (R : CategoryTheory.Presieve U), Sieve.generate R ∈ J U →
          Function.Injective
            (fun sectionValue : F.obj (Opposite.op U) =>
              fun (V : C) (arrow : V ⟶ U) (_ : R arrow) =>
                F.map arrow.op sectionValue))
