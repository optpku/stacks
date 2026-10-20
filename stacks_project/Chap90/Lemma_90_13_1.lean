module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Schlessinger
import StacksCheckRecall

/-!
# Versal formal objects imply Schlessinger's (S1)

A predeformation category with a versal formal object satisfies Schlessinger's
condition (S1).
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type (u + 1)} [Category.{u + 1} F]

/- Lemma 90.13.1: a predeformation category with a versal formal object satisfies
Schlessinger's condition (S1). -/
@[stacks 06SY] #check (CategoryTheory.Functor.hasSchlessingerS1_of_isVersal :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [CategoryTheory.Functor.IsPredeformationCategory p] (ξ : FormalObject p)
    [FormalObject.IsVersal ξ], CategoryTheory.Functor.HasSchlessingerS1 p)
