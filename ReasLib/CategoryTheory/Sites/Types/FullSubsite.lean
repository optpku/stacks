/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Types

open CategoryTheory CategoryTheory.Limits Opposite

universe u

@[expose] public section

namespace CategoryTheory.TypesFullSubsite

/-- A full site of types with a singleton object has sheaves equivalent to sets,
with inverse evaluation at that object and direct image by restricted Yoneda. -/
theorem sheaves_pt_sets_equivalence
    (C : Type (u + 1)) [Category.{u, u + 1} C]
    (inclusion : C ⥤ Type u) [inclusion.Full] [inclusion.Faithful]
    (e : C) [Unique (inclusion.obj e)] [HasPullbacks C]
    (J : GrothendieckTopology C)
    (cover_iff_surjective : ∀ (U : C) (R : Presieve U),
      Sieve.generate R ∈ J U ↔
        ∀ x : inclusion.obj U, ∃ (V : C) (f : V ⟶ U), R f ∧
          ∃ y : inclusion.obj V, inclusion.map f y = x) :
    ∃ i : Type u ≌ Sheaf J (Type u),
      i.inverse = sheafToPresheaf J (Type u) ⋙ (evaluation Cᵒᵖ (Type u)).obj (op e) ∧
      i.functor ⋙ sheafToPresheaf J (Type u) =
        yoneda ⋙ (Functor.whiskeringLeft Cᵒᵖ (Type u)ᵒᵖ (Type u)).obj inclusion.op := sorry

end CategoryTheory.TypesFullSubsite
