/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupoidCompletion

/-!
# Completion of a groupoid in functors

The completed groupoid constructor and all seven structure-map formulas are
available through the shared mathematical owner.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CategoryTheory.GroupoidInFunctors.completion :
  CategoryTheory.GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k) →
    CategoryTheory.GroupoidInFunctors.{u + 1, u, w} (CompleteLocalAlgCat Λ k))

#check (CategoryTheory.GroupoidInFunctors.completion_U :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).U = Functor.typesCompletion G.U)

#check (CategoryTheory.GroupoidInFunctors.completion_R :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).R = Functor.typesCompletion G.R)

#check (CategoryTheory.GroupoidInFunctors.completion_s :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).s = Functor.typesCompletionMap G.s)

#check (CategoryTheory.GroupoidInFunctors.completion_t :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).t = Functor.typesCompletionMap G.t)

#check (CategoryTheory.GroupoidInFunctors.completion_c :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).c =
      (Functor.typesCompletionPullbackIso G.s G.t).inv ≫ Functor.typesCompletionMap G.c)

#check (CategoryTheory.GroupoidInFunctors.completion_e :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).e = Functor.typesCompletionMap G.e)

#check (CategoryTheory.GroupoidInFunctors.completion_i :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).i = Functor.typesCompletionMap G.i)

#check (CategoryTheory.GroupoidInFunctors.completion_spec :
  ∀ (G : GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k)),
    (CategoryTheory.GroupoidInFunctors.completion G).U = Functor.typesCompletion G.U ∧
      (CategoryTheory.GroupoidInFunctors.completion G).R = Functor.typesCompletion G.R ∧
      (CategoryTheory.GroupoidInFunctors.completion G).s = Functor.typesCompletionMap G.s ∧
      (CategoryTheory.GroupoidInFunctors.completion G).t = Functor.typesCompletionMap G.t ∧
      (CategoryTheory.GroupoidInFunctors.completion G).c =
        (Functor.typesCompletionPullbackIso G.s G.t).inv ≫
          Functor.typesCompletionMap G.c ∧
      (CategoryTheory.GroupoidInFunctors.completion G).e = Functor.typesCompletionMap G.e ∧
      (CategoryTheory.GroupoidInFunctors.completion G).i = Functor.typesCompletionMap G.i)
