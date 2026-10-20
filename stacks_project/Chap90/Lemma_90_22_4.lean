module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.CompletionRepresentability
import StacksCheckRecall

/-!
# Prorepresentable groupoids in functors versus completion and object/arrow functors

A groupoid in functors on `ArtinianLocalAlgCat` is prorepresentable if and only if its
completion is representable as a groupoid in functors on `CompleteLocalAlgCat`, and if
and only if its object and arrow functors are prorepresentable.
-/

@[expose] public section

open CategoryTheory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 90.22.4 (1): a groupoid in functors on Artinian local algebras is
prorepresentable if and only if its completion is representable. -/
@[stacks 06KG] #check
  (CategoryTheory.GroupoidInFunctors.isProrepresentable_iff_isRepresentable_completion :
    ∀ (G : CategoryTheory.GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
      CategoryTheory.GroupoidInFunctors.IsProrepresentable G ↔
        CategoryTheory.GroupoidInFunctors.IsRepresentable
          (CategoryTheory.GroupoidInFunctors.completion G))

/- Lemma 90.22.4 (2): a groupoid in functors on Artinian local algebras is
prorepresentable if and only if its object and arrow functors are prorepresentable. -/
@[stacks 06KG] #check
  (CategoryTheory.GroupoidInFunctors.isProrepresentable_iff :
    ∀ (G : CategoryTheory.GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k)),
      CategoryTheory.GroupoidInFunctors.IsProrepresentable G ↔
        CategoryTheory.Functor.IsProrepresentable G.U ∧
          CategoryTheory.Functor.IsProrepresentable G.R)
