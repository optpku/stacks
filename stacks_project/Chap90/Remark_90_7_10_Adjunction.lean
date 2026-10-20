/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Types.Basic
public import stacks_project.Chap90.Remark_90_7_7_Nilpotency
public import stacks_project.Chap90.Remark_90_7_10_Functors

public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Adjunction

/-!
# Restriction–completion adjunction

The canonical adjunction and counit isomorphism are available from the shared owner.
-/

@[expose] public section

open CategoryTheory

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.10: restriction is left adjoint to completion. -/
#check (CategoryTheory.Functor.typesCompletionAdjunction :
  (Functor.typesRestrictInclusion :
    (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤ (ArtinianLocalAlgCat Λ k ⥤ Type w)) ⊣
  (Functor.typesCompletionFunctor :
    (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤ (CompleteLocalAlgCat Λ k ⥤ Type w)))

#check (CategoryTheory.Functor.typesCompletionHomEquiv :
  ∀ (G : CompleteLocalAlgCat Λ k ⥤ Type w) (F : ArtinianLocalAlgCat Λ k ⥤ Type w),
    (Functor.typesRestrictInclusion.obj G ⟶ F) ≃
      (G ⟶ Functor.typesCompletionFunctor.obj F))

#check (CategoryTheory.Functor.typesCompletionCounitIso :
  Functor.typesCompletionFunctor ⋙ Functor.typesRestrictInclusion ≅
    𝟭 (ArtinianLocalAlgCat Λ k ⥤ Type w))
