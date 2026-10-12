/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion

/-!
# Compatibility checks for set-valued completion

This module keeps the source-facing compatibility surface used by existing
chapter consumers while the mathematical declarations live in `ReasLib`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- The set-valued completion is a functor on complete local algebras. -/
#check (CategoryTheory.Functor.typesCompletion :
  (ArtinianLocalAlgCat Λ k ⥤ Type w) → (CompleteLocalAlgCat Λ k ⥤ Type w))

/- Its object and map formulas are inverse-limit constructions. -/
#check (CategoryTheory.Functor.typesCompletion_obj :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k),
    (CategoryTheory.Functor.typesCompletion F).obj S =
      limit (S.truncationSystem ⋙ F))
#check (CategoryTheory.Functor.typesCompletion_map :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) {S T : CompleteLocalAlgCat Λ k}
    (f : S ⟶ T),
    (CategoryTheory.Functor.typesCompletion F).map f =
      limMap (Functor.whiskerRight (CompleteLocalAlgCat.truncationSystemMap f) F))

/- The truncation tower and its induced morphisms are available to consumers. -/
#check (CompleteLocalAlgCat.truncationSystem :
  ∀ (S : CompleteLocalAlgCat Λ k), SequentialInverseSystem (ArtinianLocalAlgCat Λ k))
#check (CompleteLocalAlgCat.truncationHom :
  ∀ {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T) (n : ℕ),
    S.truncation n ⟶ T.truncation n)
#check (CompleteLocalAlgCat.truncationSystemMap :
  ∀ {S T : CompleteLocalAlgCat Λ k} (f : S ⟶ T),
    S.truncationSystem ⟶ T.truncationSystem)

/- The compatible-element reconstruction API is retained under its canonical owner. -/
#check (CategoryTheory.Functor.typesCompletionStage :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (x : (CategoryTheory.Functor.typesCompletion F).obj S) (n : ℕ), F.Elements)
#check (CategoryTheory.Functor.typesCompletionSystem :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (x : (CategoryTheory.Functor.typesCompletion F).obj S),
    SequentialInverseSystem F.Elements)
#check (CategoryTheory.Functor.typesCompletionOfSystemStage :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n))
    (n : ℕ), F.obj (S.truncation n))
#check (CategoryTheory.Functor.typesCompletionOfSystem :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n)),
    (CategoryTheory.Functor.typesCompletion F).obj S)
#check (CategoryTheory.Functor.typesCompletionOfSystem_apply :
  ∀ (F : ArtinianLocalAlgCat Λ k ⥤ Type w) (S : CompleteLocalAlgCat Λ k)
    (ξ : SequentialInverseSystem F.Elements)
    (over_step : ∀ n, (CategoryOfElements.π F).IsHomLift (S.truncationMap n) (ξ.stepMap n))
    (j : ℕᵒᵖ),
    limit.π (S.truncationSystem ⋙ F) j
        (CategoryTheory.Functor.typesCompletionOfSystem F S ξ over_step) =
      CategoryTheory.Functor.typesCompletionOfSystemStage F S ξ over_step j.unop)
