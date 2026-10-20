module

public import Mathlib.CategoryTheory.Whiskering
public import stacks_project.Chap90.Definition_90_6_1_Prorepresentable
public import stacks_project.Chap90.Definition_90_22_2_TypesCompletion

public import ReasLib.AlgebraicGeometry.FormalDeformation.TypesCompletion.Adjunction

/-!
# Restriction and completion of set-valued functors

The quotient projections and functor operations are available from their shared owners.
-/

@[expose] public section

open CategoryTheory

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Remark 90.7.10: restriction and completion on set-valued functors. -/
#check (CategoryTheory.Functor.typesRestrictInclusion :
  (CompleteLocalAlgCat Λ k ⥤ Type w) ⥤ (ArtinianLocalAlgCat Λ k ⥤ Type w))

#check (CategoryTheory.Functor.typesCompletionFunctor :
  (ArtinianLocalAlgCat Λ k ⥤ Type w) ⥤ (CompleteLocalAlgCat Λ k ⥤ Type w))

#check (CompleteLocalAlgCat.truncationToInclusion :
  ∀ (R : CompleteLocalAlgCat Λ k) (n : ℕ),
    R ⟶ ArtinianLocalAlgCat.inclusion.obj (R.truncation n))
