module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.QuasiInitial
import StacksCheckRecall

/-!
# Quasi-initiality of versal formal objects

A versal formal object of a predeformation category is weakly initial in the
category of formal objects: every formal object admits a morphism from it.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable {F : Type (u + 1)} [Category.{u + 1} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/- Lemma 90.8.11: A versal formal object of a predeformation category admits a
morphism to every formal object. -/
@[stacks 06HT] #check (FormalObject.exists_hom_of_isVersal :
  ∀ [Functor.IsPredeformationCategory p] (ξ : FormalObject p)
    [FormalObject.IsVersal ξ] (η : FormalObject p), Nonempty (ξ ⟶ η))
