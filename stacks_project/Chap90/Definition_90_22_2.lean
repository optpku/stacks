module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GroupoidCompletion
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.22.2: Let `(U, R, s, t, c)` be a groupoid in functors on
`ArtinianLocalAlgCat Λ k`. The completion of `(U, R, s, t, c)` is the groupoid in
functors `GroupoidInFunctors.completion G` on `CompleteLocalAlgCat Λ k`, obtained by
completing the object and arrow functors and the source, target, identity, and inverse
maps, and transporting composition along `Functor.typesCompletionPullbackIso`. -/
@[stacks 06KE]
#check (CategoryTheory.GroupoidInFunctors.completion :
  CategoryTheory.GroupoidInFunctors.{u + 1, u, w} (ArtinianLocalAlgCat Λ k) →
    CategoryTheory.GroupoidInFunctors.{u + 1, u, w} (CompleteLocalAlgCat Λ k))
