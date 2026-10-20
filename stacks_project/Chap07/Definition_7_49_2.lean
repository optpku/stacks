module

public import ReasLib.CategoryTheory.Sites.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Definition 7.49.2: Let `C` be a category. Let `J` be a topology on `C`. We say that a
presheaf of sets `ℱ` is separated if for every object `U` and every covering sieve `S` on `U`
the canonical map `ℱ(U) ⟶ Mor_PSh(C)(S, ℱ)` is injective. Canonical sieve morphisms
are determined by their restrictions `ℱ.map f.op t`; these restriction families are
compatible. Passing to generated sieves gives the equivalent covering-presieve criterion. -/
@[stacks 00ZI] #check (CategoryTheory.Presieve.isSeparated_iff_injective_restriction :
  ∀ {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type w),
    CategoryTheory.Presieve.IsSeparated J F ↔
      ∀ (U : C) (R : Presieve U), Sieve.generate R ∈ J U →
        Function.Injective
          (fun sectionValue : F.obj (Opposite.op U) =>
            fun (V : C) (arrow : V ⟶ U) (_ : R arrow) =>
              F.map arrow.op sectionValue))

#check (CategoryTheory.Presieve.IsSeparated :
  ∀ {C : Type u} [Category.{v} C],
    GrothendieckTopology C → (Cᵒᵖ ⥤ Type w) → Prop)
