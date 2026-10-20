module

import ReasLib.CategoryTheory.Sites.Types.FullSubsite
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite

universe u

/- 7.15.3.1: if a full site of sets has a singleton e, then its sheaves are
   equivalent to sets, with i⁻¹ ℱ = ℱ(e) and i_* E = (U ↦ Mor_Sets(U, E)). -/
@[stacks 05UW] #check
  (CategoryTheory.TypesFullSubsite.sheaves_pt_sets_equivalence :
    ∀ (C : Type (u + 1)) [Category.{u, u + 1} C]
      (inclusion : C ⥤ Type u) [Functor.Full inclusion] [Functor.Faithful inclusion]
      (e : C) [Unique (inclusion.obj e)] [HasPullbacks C]
      (J : GrothendieckTopology C),
      (∀ (U : C) (R : Presieve U),
        Sieve.generate R ∈ J U ↔
          ∀ x : inclusion.obj U, ∃ (V : C) (f : V ⟶ U), R f ∧
            ∃ y : inclusion.obj V, inclusion.map f y = x) →
        ∃ i : Type u ≌ Sheaf J (Type u),
          i.inverse =
              sheafToPresheaf J (Type u) ⋙
                (evaluation Cᵒᵖ (Type u)).obj (Opposite.op e) ∧
            i.functor ⋙ sheafToPresheaf J (Type u) =
              yoneda ⋙
                (Functor.whiskeringLeft Cᵒᵖ (Type u)ᵒᵖ (Type u)).obj inclusion.op)
